-- | @futhark fmt@
module Futhark.CLI.Fmt (main) where

import Data.Bifunctor (second)
import Data.List qualified as L
import Data.Text qualified as T
import Data.Text.IO qualified as T
import Futhark.Util.Loc
import Futhark.Util.Options
import Language.Futhark
import Language.Futhark.Parser
  ( Comment (..),
    SyntaxError (..),
    parseFutharkWithComments,
  )
import System.Exit
import System.IO
import Text.Printf (printf)
import Control.Monad.State
import GHC.Base (undefined, Any)
import Prelude
import Language.Haskell.TH.PprLib (dcolon)
import Text.Regex.TDFA.Pattern (starTrans')
import Statistics.Sample (mean)
import Futhark.CodeGen.ImpGen (dPrim)
import Data.ByteString (intersperse)
import Data.Data (Constr)

-- The formatter implemented here is very crude and incomplete.  The
-- only syntactical construct it can currently handle is type
-- abbreviations without parameters, e.g:
--
--  type t = (bool, i32)
--
-- A *formatting function* is a function of type
--
--  [Comment] -> a -> ([Comment], Fmt)
--
-- where 'a' is some syntactical object, e.g. UncheckedTypeExp.  The
-- [Comment] list is a sorted list of "residual comments" that have
-- yet to be injected into the output.  A formatting function returns
-- a new list of comments (which may or may not be identical to the
-- input), as well as the formatted representation of 'a' as a 'Fmt'
-- value.
--
-- TODO: refactor this entire thing so that the maintenance of the
-- residual comments is encapsulated monadically.  Use a State monad
-- to keep the list.  This will make the code much cleaner.
--
-- TODO: ensure that doc comments (that start with "-- |" and are
-- connected to definitions) are always separated from other comments
-- with a single newline character.
--
-- TODO: prettyprint in a nicer way than one line per terminal.
--
-- TODO: support all syntactical constructs.

type FmtM = State [Comment]

-- | Invariant: Should not contain newline characters.
type Line = T.Text

-- | The result of formatting is a list of lines.  This is useful as
-- we might want to modify every line of a prettyprinted
-- sub-expression, to e.g. prepend indentation.
type Fmt = [Line]

comment :: Located a => a -> FmtM Fmt
comment a =
  do
    cs <- get
    case cs of
     c : cs'
      | locOf a > locOf c ->
        do
          put cs'
          pure [commentText c]
     _ -> pure []


-- | Documentation comments are always optional, so this takes a 'Maybe'.
fmtDocComment :: Maybe DocComment -> FmtM Fmt
fmtDocComment (Just (DocComment x loc)) =
  do 
    c <- comment loc
    pure (c <> prefix (T.lines x))
  where
    prefix [] = []
    prefix (l : ls) = ("-- | " <> l) : map ("-- " <>) ls
fmtDocComment Nothing = pure []

fmtMany :: (a -> FmtM Fmt) -> [a] -> FmtM Fmt
fmtMany f ds =
  concat <$> mapM f ds

fmtTupleTypeElems :: [UncheckedTypeExp] -> FmtM Fmt
fmtTupleTypeElems [] = pure []
fmtTupleTypeElems [t] = fmtTypeExp t
fmtTupleTypeElems (t : ts) =
  do 
     t' <- fmtTypeExp t
     ts' <- fmtTupleTypeElems ts
     pure (t' <> [","] <> ts')

fmtRecordColon :: (Name, TypeExp NoInfo Name) -> FmtM Fmt
fmtRecordColon (tf,ts) = 
  do
    pure([prettyText tf] <> [":"] <> [prettyText ts])

fmtRecordTypeElems :: [(Name, TypeExp NoInfo Name)] -> FmtM Fmt
fmtRecordTypeElems [] = pure []
fmtRecordTypeElems [t] = fmtRecordColon t
fmtRecordTypeElems (t : ts) =
  do 
     t' <- fmtRecordColon t
     ts' <- fmtRecordTypeElems ts
     pure (t' <> [","] <> ts')

fmtPrettyList :: [UncheckedTypeExp] -> FmtM Fmt
fmtPrettyList [] = pure []
fmtPrettyList [t] = pure [prettyText t]
fmtPrettyList (t : ts) =
  do
    ts' <- fmtPrettyList ts
    pure ([prettyText t] <> ts')

fmtSum :: [(Name, [TypeExp NoInfo Name])] -> FmtM Fmt
fmtSum [] = pure []
fmtSum [(tf,[ts])] = 
  do
    ts' <- fmtPrettyList [ts]
    pure (["|"] <> ["#"] <> [prettyText tf] <> ts')
fmtSum (t : ts) =
  do
    ts' <- fmtSum ts
    pure (["|"] <> ["#"] <> [prettyText t] <> ts')

fmtDimBrac :: [Name] -> FmtM Fmt
fmtDimBrac [] = pure []
fmtDimBrac [t] = pure (["["] <> [prettyText t] <> ["]"])
fmtDimBrac (l : ls) =
  do
    ls' <- fmtDimBrac ls
    pure(["["] <> [prettyText l] <> ["]"] <> ls')

fmtTypeExp :: UncheckedTypeExp -> FmtM Fmt
fmtTypeExp (TEVar v loc) =
  do 
    c <- comment loc
    pure (c <> [prettyText v])
fmtTypeExp (TETuple ts loc) =
  do 
    c <- comment loc
    ts' <- fmtTupleTypeElems ts
    pure (c <> ["("] <> ts' <> [")"])
fmtTypeExp (TEParens ps loc) =
  do
    c <- comment loc
    pure (c <> ["("] <> [prettyText ps] <> [")"])
fmtTypeExp (TERecord rs loc) = 
  do
    c <- comment loc
    rs' <- fmtRecordTypeElems rs
    pure (c <> ["{"] <> rs' <> ["}"])
fmtTypeExp (TEArray as bs loc) =
  do
    c <- comment loc
    pure (c <> [prettyText as] <> [prettyText bs])
fmtTypeExp (TEUnique us loc) =
  do
    c <- comment loc
    pure (c <> ["*"] <> [prettyText us])
fmtTypeExp (TEApply t arg loc) =
  do
    c <- comment loc
    pure (c <> [prettyText t] <> [prettyText arg])
fmtTypeExp (TEArrow (Just v) t1 t2 loc) =
  do
    c <- comment loc
    pure (c <> ["("] <> [prettyText v] <> [":"] <> [prettyText t1] <> [")"] <> [" -> "] <> [prettyText t2])
fmtTypeExp (TEArrow Nothing t1 t2 loc) =
  do
    c <- comment loc
    pure (c <> [prettyText t1] <> ["->"] <> [prettyText t2])
fmtTypeExp (TESum cs loc) =
  do
    c <- comment loc
    cs' <- fmtSum cs
    pure (c <> cs') 
fmtTypeExp (TEDim dims te loc) =
  do
    c <- comment loc
    dims' <- fmtDimBrac dims
    pure (c <> ["?"] <> ["["] <> dims' <> ["]"] <> ["."] <> [prettyText te])

fmtTypeParam :: UncheckedTypeParam -> FmtM Fmt
fmtTypeParam (TypeParamDim name loc) =
  do
    c <- comment loc
    pure (c <> [prettyText name])
fmtTypeParam (TypeParamType l name loc) =
  do
    c <- comment loc
    pure (c <> ["'" <> prettyText l] <> [prettyText name]) 

fmtTypeBind :: UncheckedTypeBind -> FmtM Fmt
fmtTypeBind (TypeBind name l ps e NoInfo dc _loc) =
  do
     dc' <- fmtDocComment dc
     ps' <- fmtMany fmtTypeParam ps
     e' <- fmtTypeExp e
     pure (dc' <> ["type" <> prettyText l] <> [prettyText name] <> ps' <> ["="] <> e')

fmtAttrs :: [AttrInfo Name] -> FmtM Fmt
fmtAttrs [] = pure []
fmtAttrs [t] = pure [prettyText t]
fmtAttrs (t : ts) =
  do
    ts' <- fmtAttrs ts
    pure (["#["] <> [prettyText t] <> ts' <> ["]"])

fmtTuplePat :: [UncheckedPat] -> FmtM Fmt
fmtTuplePat [] = pure []
fmtTuplePat [t] = fmtPatBase t
fmtTuplePat (t : ts) =
  do
    t' <- fmtPatBase t
    ts' <- fmtTuplePat ts
    pure(t' <> [","] <> ts')

fmtPatLit :: PatLit -> FmtM Fmt
fmtPatLit (PatLitInt x) = pure [prettyText x]
fmtPatLit (PatLitFloat f) = pure [prettyText f]
fmtPatLit (PatLitPrim v) = fmtLit v

fmtPatBase :: UncheckedPat -> FmtM Fmt
fmtPatBase (PatAscription p t loc) =
  do
    c <- comment loc
    p' <- fmtPatBase p
    t' <- fmtTypeExp t
    pure (c <> p' <> [":"] <> t')
fmtPatBase (PatParens p loc) =
  do
    c <- comment loc
    p' <- fmtPatBase p
    pure (c <> ["("] <> p' <> [")"])
fmtPatBase (Id v t loc) =
  do
    c <- comment loc
    t' <- fmtPatType t
    case unAnnot t of
      Just _h -> pure(c <> ["("] <> [prettyText v] <> [":"] <> t' <> [")"])
      Nothing -> pure (c <> [prettyText v])
fmtPatBase (TuplePat pats loc) =
  do
    c <- comment loc
    pats' <- fmtTuplePat pats
    pure(c <> pats')
fmtPatBase (RecordPat fs loc) =
  do
    --c <- comment loc
    --fs' <- fmtRecordPat fs
    --pure(c <> fs')
    undefined
fmtPatBase (Wildcard t loc) =
  do
    c <- comment loc
    t' <- fmtPatType t
    case unAnnot t of
      Just _h -> pure(c <> ["("] <> ["_"] <> [":"] <> t' <> [")"])
      Nothing -> pure (c <> ["_"])
fmtPatBase (PatLit e _f loc) =
  do
    c <- comment loc
    e' <- fmtPatLit e
    pure (c <> e')
fmtPatBase (PatConstr n _f ps loc) =
  do
    c <- comment loc
    ps' <- fmtMany fmtPatBase ps
    pure (c <> ["#"] <> [prettyText n] <> ps')
fmtPatBase (PatAttr attr p loc) =
  do
    c <- comment loc
    p' <- fmtPatBase p
    pure (c <> ["#["] <> [prettyText attr] <> ["]"] <> p')

fmtPatArr :: [UncheckedPat] -> FmtM Fmt
fmtPatArr [] = pure []
fmtPatArr [t] = fmtPatBase t
fmtPatArr (t : ts) =
  do
    ts' <- fmtPatArr ts
    t' <- fmtPatBase t
    pure (t' <> ts')

fmtPatType :: NoInfo PatType -> FmtM Fmt
fmtPatType t =
  do
    case unAnnot t of
      Just t' -> 
        pure ["@" <> "(" <> prettyText t' <> ")"] 
      _ -> pure []

operatorName :: Name -> Bool
operatorName = (`elem` opchars) . T.head . nameToText
  where
    opchars :: String
    opchars = "+-*/%=!><|&^."

fmtLit :: PrimValue -> FmtM Fmt
fmtLit (UnsignedValue (Int8Value v)) = pure ([prettyText v] <> ["u8"])
fmtLit (UnsignedValue (Int16Value v)) = pure ([prettyText v] <> ["u16"])
fmtLit (UnsignedValue (Int32Value v)) = pure ([prettyText v] <> ["u32"])
fmtLit (UnsignedValue (Int64Value v)) = pure ([prettyText v] <> ["u64"])
fmtLit (SignedValue v) = pure [prettyText v]
fmtLit (BoolValue True) = pure ["true"]
fmtLit (BoolValue False) = pure ["false"]
fmtLit (FloatValue v) = pure [prettyText v]

fmtFieldBase :: FieldBase NoInfo Name -> FmtM Fmt
fmtFieldBase (RecordFieldExplicit name e loc) =
  do
    c <- comment loc
    e' <- fmtValExp (-1) e
    pure (c <> [prettyText name] <> ["="] <> e')
fmtFieldBase (RecordFieldImplicit name _ loc) =
  do
    c <- comment loc
    pure (c <> [prettyText name])

fmtIntersperse :: [Name] -> FmtM Fmt
fmtIntersperse [] = pure []
fmtIntersperse [t] = pure [prettyText t]
fmtIntersperse (t : ts) =
  do
    ts' <- fmtIntersperse ts
    pure ([prettyText t] <> ["."] <> ts')

fmtValExp :: Int -> UncheckedExp -> FmtM Fmt
fmtValExp _ (Var name t loc) =
  do
    c <- comment loc
    t' <- fmtPatType t
    if operatorName(toName (qualLeaf name)) then
      pure(c <> ["("] <> [prettyText name] <> t' <> [")"])
    else
      pure (c <> [prettyText name] <> t')
fmtValExp _ (Hole t loc) =
  do
    c <- comment loc
    t' <- fmtPatType t
    pure (c <> ["???"] <> t')
fmtValExp _ (Parens e loc) =
  do
    c <- comment loc
    e' <- fmtValExp (-1) e
    pure (c <> ["("] <> e' <> [")"])
fmtValExp _ (QualParens (v, vloc) e loc) =
  do
    vc' <- comment vloc
    c' <- comment loc
    e' <- fmtValExp (-1) e
    pure(vc' <> c' <> [prettyText v] <> ["."] <> ["("] <> e' <> [")"])
fmtValExp p (Ascript e t loc) =
  do
    c <- comment loc
    e' <- fmtValExp 0 e
    t' <- fmtTypeExp t
    if p /= -1 then
      pure (c <> ["("] <> e' <> [":"] <> t' <> [")"])
    else
      pure (c <> e' <> [":"] <> t')
fmtValExp _ (Literal v loc) =
  do
    c <- comment loc
    v' <- fmtLit v
    pure (c <> v')
fmtValExp _ (IntLit v t loc) =
  do
    c <- comment loc
    t' <- fmtPatType t
    pure (c <> [prettyText v] <> t')
fmtValExp _ (FloatLit v t loc) =
  do
    c <- comment loc
    t' <- fmtPatType t
    pure (c <> [prettyText v] <> t')
fmtValExp _ (TupLit es loc) =
  do
    c <- comment loc
    --es' <- fmtMany fmtValExp (-1) es
    --pure (c <> es')
    undefined
fmtValExp _ (RecordLit fs loc) =
  do
    c <- comment loc
    fs' <- fmtMany fmtFieldBase fs
    pure(c <> fs')
fmtValExp _ (ArrayLit es t loc) =
  do
    c <- comment loc
    --es' <- fmtMany fmtValExp (-1) es
    t' <- fmtPatType t
    --pure (c <> ["["] <> es' <> t' <> ["]"])
    undefined
fmtValExp _ (StringLit s loc) =
  do
    c <- comment loc
    pure (c <> [prettyText s])
fmtValExp _ (Project k e _pt loc) =
  do
    c <- comment loc
    e' <- fmtValExp (-1) e
    pure (c <> [prettyText k] <> ["."] <> e')
fmtValExp _ (Negate e loc) =
  do
    c <- comment loc
    e' <- fmtValExp (-1) e
    pure (c <> ["-"] <> e')
fmtValExp _ (Not e loc) =
  do
    c <- comment loc
    e' <- fmtValExp (-1) e
    pure (c <> ["-"] <> e')
fmtValExp _ (Update src idxs ve loc) =
  do
    -- c <- comment loc
    -- src' <- fmtValExp (-1) src
    -- idxs' <- fmtSlice idxs
    -- ve' <- fmtValExp (-1) ve
    -- pure (c <> src' <> ["with"] <> ["["] <> idxs' <> ["]"] <> ["="] <> ve')
    undefined
fmtValExp _ (RecordUpdate src fs ve _f loc) =
  do
    c <- comment loc
    src' <- fmtValExp (-1) src
    fs' <- fmtIntersperse fs
    ve' <- fmtValExp (-1) ve
    pure (c <> src' <> ["with"] <> fs' <> ["="] <> ve')
fmtValExp _ (Assert e1 e2 _f loc) =
  do
    c <- comment loc
    e1' <- fmtValExp 10 e1
    e2' <- fmtValExp 10 e2
    pure (c <> ["assert"] <> e1' <> e2')
fmtValExp p (Lambda params body rettype _f loc) =
  do
    c <- comment loc
    params' <- fmtPatArr params
    rettype' <-
      case rettype of
        Just t ->
          do
            t' <- fmtTypeExp t
            pure ([":"] <> t')
        Nothing -> pure []
    body' <- fmtValExp (-1) body
    if p /= -1 then
      pure(c <> ["("] <> ["\\"] <> params' <> rettype' <> ["->"] <> body' <> [")"])
    else
      pure(c <> ["\\"] <> params' <> rettype' <> ["->"] <> body')
fmtValExp _ (OpSection binop _f loc) =
  do
    -- c <- comment loc
    -- binop' <- fmtBinOp binop
    -- pure(c <> ["("] <> binop' <> [")"])
    undefined
fmtValExp _ (OpSectionLeft binop _ x _ _ loc) = undefined
fmtValExp _ (OpSectionRight binop _ x _ _ loc) = undefined
fmtValExp _ (ProjectSection fields _ loc) = undefined
fmtValExp _ (IndexSection idxs _ loc) = undefined
fmtValExp p (Constr n cs t loc) = undefined
fmtValExp _ (Attr attr e loc) = undefined
fmtValExp i (AppExp e res) = undefined

fmtValBind :: UncheckedValBind -> FmtM Fmt
fmtValBind (ValBind entry name retdec1 rettype tparams args body dc attrs _loc) =
  do
    dc' <- fmtDocComment dc
    attrs' <- fmtAttrs attrs
    ps' <- fmtMany fmtTypeParam tparams
    args' <- fmtPatArr args
    body' <- fmtValExp (-1) body
    retdec1' <-
      case retdec1 of
        Just ret -> 
          do
            ret' <- fmtTypeExp ret
            pure ([":"] <> ret')
        Nothing -> pure []
    entry' <-
      case entry of
      Just _ -> pure ["entry"]
      Nothing -> pure []
    pure (dc' <> attrs' <> entry' <> [prettyText name] <> ps' <> args' <> retdec1' <> ["="] <> body')

fmtSpec :: [SpecBase NoInfo Name] -> FmtM Fmt
fmtSpec [] = pure []
fmtSpec [t] = pure [prettyText t]
fmtSpec (t : ts) =
  do
    ts' <- fmtSpec ts
    pure([prettyText t] <> ts')

fmtSigExp :: UncheckedSigExp -> FmtM Fmt
fmtSigExp (SigVar v _ loc) =
  do
    c <- comment loc
    pure (c <> [prettyText v])
fmtSigExp (SigParens e loc) =
  do
    c <- comment loc
    e' <- fmtSigExp e
    pure (c <> ["("] <> e' <> [")"])
fmtSigExp (SigSpecs ss loc) = 
  do
    c <- comment loc
    ss' <- fmtSpec ss
    pure (c <> ["{"] <> ss' <> ["}"])
fmtSigExp (SigWith s (TypeRef v ps td _loc1) loc) =
  do
    c <- comment loc
    ps' <- fmtMany fmtTypeParam ps
    td' <- fmtTypeExp td
    pure (c <> [prettyText s <> "with" <> prettyText v] <> ps' <> ["="] <> td')
fmtSigExp (SigArrow (Just v) e1 e2 loc) =
  do
    c <- comment loc
    pure (c <> ["(" <> prettyText v <> ":" <> prettyText e1 <> ")" <> "->" <> prettyText e2])
fmtSigExp (SigArrow Nothing e1 e2 loc) =
  do
    c <- comment loc
    pure (c <> [prettyText e1 <> "->" <> prettyText e2])

fmtSigBind :: UncheckedSigBind -> FmtM Fmt
fmtSigBind (SigBind name e dc _loc) =
  do
    dc' <- fmtDocComment dc
    e' <- fmtSigExp e
    pure (dc' <> ["module type " <> prettyText name <> "="] <> e')

fmtModExp :: UncheckedModExp -> FmtM Fmt
fmtModExp (ModVar v loc) =
  do
    c <- comment loc
    pure (c <> [prettyText v])
fmtModExp (ModParens e loc) =
  do
    c <- comment loc
    e' <- fmtModExp e
    pure (c <> ["("] <> e' <> [")"])
fmtModExp (ModImport v _iname loc) = 
  do
    c <- comment loc
    pure(c <> [prettyText (show v)])
fmtModExp (ModDecs ds loc) = 
  do
    c <- comment loc
    ds' <- fmtMany fmtDec ds
    pure (c <> ["{"] <> ds' <> ["}"])
fmtModExp (ModApply f a _uf _hf loc) =
  do
    c <- comment loc
    f' <- fmtModExp f
    a' <- fmtModExp a
    pure (c <> ["("] <> f' <> ["("] <> a'<> [")"] <> [")"])
fmtModExp (ModAscript me se _f loc) = 
  do
    c <- comment loc
    me' <- fmtModExp me
    se' <- fmtSigExp se
    pure (c <> me' <> [":"] <> se')
fmtModExp (ModLambda param maybe_sig body loc) =
  do
    c <- comment loc
    param' <- fmtModParam param
    maybe_sig' <-
      case maybe_sig of
        Just (sig, _) ->
          do
            sig' <- fmtSigExp sig
            pure ([":"] <> sig')
        Nothing -> pure []
    body' <- fmtModExp body
    pure (c <> ["\\"] <> param' <> maybe_sig' <> ["->"] <> body')

fmtModParam :: ModParamBase NoInfo Name -> FmtM Fmt
fmtModParam (ModParam pname psig _f loc) =
  do
    c <- comment loc
    psig' <- fmtSigExp psig
    pure (c <> [prettyText pname <> ":"] <> psig')

fmtModBind :: UncheckedModBind -> FmtM Fmt
fmtModBind (ModBind name ps sig e dc _loc) =
  do
    dc' <- fmtDocComment dc
    ps' <- fmtMany fmtModParam ps
    sig' <- 
      case sig of
        Just (s,_) -> 
          do
            s' <- fmtSigExp s
            pure ([":"] <> s')
        Nothing -> pure []
    e' <- fmtModExp e
    pure (dc' <> ["module" <> prettyText name] <> ps' <> sig' <> ["="] <> e')

fmtDec :: UncheckedDec -> FmtM Fmt
fmtDec (TypeDec tb) = fmtTypeBind tb
fmtDec (ValDec vb) = fmtValBind vb
fmtDec (SigDec sb) = fmtSigBind sb
fmtDec (ModDec mb) = fmtModBind mb
fmtDec (OpenDec ob loc) =
  do
    c <- comment loc
    ob' <- fmtModExp ob
    pure (c <> ["open"] <> ob')
fmtDec (LocalDec lb loc) =
  do
    c <- comment loc
    lb' <- fmtDec lb
    pure (c <> ["local"] <> lb')
fmtDec (ImportDec ib _a loc) = 
  do
    c <- comment loc
    pure(c <> ["import" <> prettyText ib])

-- | Does not return residual comments, because these are simply
-- inserted at the end.
fmtProg :: UncheckedProg -> FmtM Fmt
fmtProg (Prog dc decs) =
  do 
    dc' <- fmtDocComment dc
    decs' <- fmtMany fmtDec decs
    cs <- get
    pure (dc' <> decs' <> map commentText cs)

-- | Run @futhark fmt@.
main :: String -> [String] -> IO ()
main = mainWithOptions () [] "program" $ \args () ->
  case args of
    [file] -> Just $ do
      pres <- parseFutharkWithComments file <$> T.readFile file
      case pres of
        Left (SyntaxError loc err) -> do
          T.hPutStr stderr $ locText loc <> ":\n" <> prettyText err
          exitFailure
        Right (prog, cs) -> do
          let number i l = T.pack $ printf "%4d %s" (i :: Int) l
          T.hPutStr stdout $ T.unlines $ zipWith number [0 ..] $ evalState (fmtProg prog) cs
    _ -> Nothing
