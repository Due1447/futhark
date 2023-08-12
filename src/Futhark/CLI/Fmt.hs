-- | @futhark fmt@
module Futhark.CLI.Fmt (main) where

--import Data.Bifunctor (second)
--import Data.List qualified as L
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
--import Text.Printf (printf)
import Control.Monad.State
--import GHC.Base (undefined, Any, Levity (Unlifted))
import Prelude
--import Language.Haskell.TH.PprLib (dcolon)
--import Text.Regex.TDFA.Pattern (starTrans')
--import Statistics.Sample (mean)
import Futhark.CodeGen.ImpGen (dPrim)
--import Data.ByteString (intersperse)
import Data.List.NonEmpty qualified as NE
import Data.Maybe
--import Data.Map.Strict qualified as MS
--import Data.Data (Constr)
--import GHC.GHCi (NoIO)
--import Language.C (TypeSpec)
--import Data.Text.Prettyprint.Doc (Pretty(pretty))
--import Futhark.CodeGen.ImpCode (DimSize, BinOp)
--import Language.Futhark.Parser.Monad (binOp)
--import Futhark.Analysis.HORep.MapNest (params)
--import Language.Futhark.TypeChecker.Monad (unappliedFunctor)
--import Language.Futhark.TypeChecker.Terms.DoLoop (UncheckedLoop)
--import Futhark.IR (RepTypes(RetType), Shape, Diet (Observe), TypeBase, Ident (identName))
--import Data.Aeson (Array)
--import Control.Arrow (Arrow (second))
--import qualified Data.Aeson.KeyMap as M


-- The formatter implemented here is unfinished
-- currently there are a some of the stntax tree that it can't handle
-- it also just prints one line per terminal
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
          c' <- comment a
          pure ([commentText c] <> ["\n"] <> c')
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
     pure (t' <> [", "] <> ts')

fmtRecordColon :: (Name, UncheckedTypeExp) -> FmtM Fmt
fmtRecordColon (tf,ts) = 
  do
    ts' <- fmtTypeExp ts
    pure([prettyText tf <> ": "] <> ts')

fmtRecordTypeElems :: [(Name, UncheckedTypeExp)] -> FmtM Fmt
fmtRecordTypeElems [] = pure []
fmtRecordTypeElems [t] = fmtRecordColon t
fmtRecordTypeElems (t : ts) =
  do 
     t' <- fmtRecordColon t
     ts' <- fmtRecordTypeElems ts
     pure (t' <> [", "] <> ts')

fmtPrettyList :: [UncheckedTypeExp] -> FmtM Fmt
fmtPrettyList [] = pure []
fmtPrettyList [t] = fmtTypeExp t
fmtPrettyList (t : ts) =
  do
    t' <- fmtTypeExp t
    ts' <- fmtPrettyList ts
    pure (t' <> [" "] <> ts')

fmtSum :: [(Name, [UncheckedTypeExp])] -> FmtM Fmt
fmtSum [] = pure []
fmtSum [(tf,ts)] = 
  do
    ts' <- fmtPrettyList ts
    pure (["#" <> prettyText tf <> " "] <> ts')
fmtSum (t : ts) =
  do
    t' <- fmtSum [t]
    ts' <- fmtSum2 ts
    pure (t' <> [" "] <> ts')

-- is here so I can make sure that the first sum doesn't have a |
fmtSum2 :: [(Name, [UncheckedTypeExp])] -> FmtM Fmt
fmtSum2 [] = pure []
fmtSum2 [(tf,ts)] = 
  do
    ts' <- fmtPrettyList ts
    pure (["| #" <> prettyText tf <> " "] <> ts')
fmtSum2 (t : ts) =
  do
    t' <- fmtSum2 [t]
    ts' <- fmtSum2 ts
    pure (t' <> [" "] <> ts')

fmtDimBrac :: [Name] -> FmtM Fmt
fmtDimBrac [] = pure []
fmtDimBrac [t] = pure ["[" <> prettyText t <> "] "]
fmtDimBrac (l : ls) =
  do
    ls' <- fmtDimBrac ls
    pure(["[" <> prettyText l <> "] "] <> ls')

fmtSizeExp :: SizeExp NoInfo Name -> FmtM Fmt
fmtSizeExp SizeExpAny {} = pure ["[] "]
fmtSizeExp (SizeExp e loc) =
  do
    c <- comment loc
    e' <- fmtValExp e
    pure(c <> ["["] <> e' <> ["] "])

fmtTypeArgExp :: TypeArgExp NoInfo Name -> FmtM Fmt
fmtTypeArgExp (TypeArgExpSize d) = fmtSizeExp d
fmtTypeArgExp (TypeArgExpType t) = fmtTypeExp t

fmtTypeExp :: UncheckedTypeExp -> FmtM Fmt
fmtTypeExp (TEVar v loc) =
  do 
    c <- comment loc
    pure (c <> [prettyText v <> " "])
fmtTypeExp (TETuple ts loc) =
  do 
    c <- comment loc
    ts' <- fmtTupleTypeElems ts
    pure (c <> ["("] <> ts' <> [") "])
fmtTypeExp (TEParens te loc) =
  do
    c <- comment loc
    te' <- fmtTypeExp te
    pure (c <> ["("] <> te' <> [") "])
fmtTypeExp (TERecord rs loc) = 
  do
    c <- comment loc
    rs' <- fmtRecordTypeElems rs
    pure (c <> ["{"] <> rs' <> ["} "])
fmtTypeExp (TEArray d at loc) =
  do
    c <- comment loc
    d' <- fmtSizeExp d
    at' <- fmtTypeExp at
    pure (c <> d' <> [" "] <> at')
fmtTypeExp (TEUnique us loc) =
  do
    c <- comment loc
    us' <- fmtTypeExp us
    pure (c <> ["*"] <> us')
fmtTypeExp (TEApply t arg loc) =
  do
    c <- comment loc
    t' <- fmtTypeExp t
    arg' <- fmtTypeArgExp arg
    pure (c <> t' <> [" "] <> arg')
fmtTypeExp (TEArrow (Just v) t1 t2 loc) =
  do
    c <- comment loc
    t1' <- fmtTypeExp t1
    t2' <- fmtTypeExp t2
    pure (c <> ["(" <> prettyText v <> ":"] <> t1' <> [") " <> " -> "] <> t2')
fmtTypeExp (TEArrow Nothing t1 t2 loc) =
  do
    c <- comment loc
    t1' <- fmtTypeExp t1
    t2' <- fmtTypeExp t2
    pure (c <> t1' <> [" -> "] <> t2')
fmtTypeExp (TESum cs loc) =
  do
    c <- comment loc
    cs' <- fmtSum cs
    pure (c <> cs') 
fmtTypeExp (TEDim dims te loc) =
  do
    c <- comment loc
    dims' <- fmtDimBrac dims
    te' <- fmtTypeExp te
    pure (c <> ["?"] <> dims' <> ["."] <> te')

fmtTypeParam :: UncheckedTypeParam -> FmtM Fmt
fmtTypeParam (TypeParamDim name loc) =
  do
    c <- comment loc
    pure (c <> ["[" <> prettyText name <> "] "])
fmtTypeParam (TypeParamType l name loc) =
  do
    c <- comment loc
    pure (c <> ["'" <> prettyText l <> prettyText name <> " "]) 

fmtTypeBind :: UncheckedTypeBind -> FmtM Fmt
fmtTypeBind (TypeBind name l ps e NoInfo dc loc) =
  do
     c <- comment loc 
     dc' <- fmtDocComment dc
     ps' <- fmtMany fmtTypeParam ps
     e' <- fmtTypeExp e 
     pure (c <> dc' <> ["\ntype" <> prettyText l <> " " <> prettyText name <> " "] <> ps' <> ["="] <> ["\n"] <> ["  "] <> e' <> ["\n"])

fmtAttrAtom :: AttrAtom Name -> FmtM Fmt
fmtAttrAtom (AtomName v) = pure [prettyText v]
fmtAttrAtom (AtomInt x) = pure [prettyText x]

fmtAttrInfo :: AttrInfo Name -> FmtM Fmt
fmtAttrInfo (AttrAtom attr loc) =
  do
    c <- comment loc
    attr' <- fmtAttrAtom attr
    pure(c <> attr')
fmtAttrInfo (AttrComp f attrs loc) =
  do
    c <- comment loc
    attrs' <- fmtAttrs attrs
    pure (c <> [prettyText f <> "("] <> attrs' <> [") "])

fmtAttrs :: [AttrInfo Name] -> FmtM Fmt
fmtAttrs [] = pure []
fmtAttrs [t] = fmtAttrInfo t
fmtAttrs (t : ts) =
  do
    t' <- fmtAttrInfo t
    ts' <- fmtAttrs ts
    pure (["#["] <> t' <> [" "] <> ts' <> ["] "])

fmtTuplePat :: [UncheckedPat] -> FmtM Fmt
fmtTuplePat [] = pure []
fmtTuplePat [t] = fmtPatBase t
fmtTuplePat (t : ts) =
  do
    t' <- fmtPatBase t
    ts' <- fmtTuplePat ts
    pure(t' <> [", "] <> ts')

fmtPatLit :: PatLit -> FmtM Fmt
fmtPatLit (PatLitInt x) = pure [prettyText x]
fmtPatLit (PatLitFloat f) = pure [prettyText f]
fmtPatLit (PatLitPrim v) = fmtLit v

fmtPatRecord :: [(Name, UncheckedPat)] -> FmtM Fmt
fmtPatRecord [] = pure []
fmtPatRecord [t] = fmtPatRec t
fmtPatRecord (l : ls) =
  do
    l' <- fmtPatRec l
    ls' <- fmtPatRecord ls
    pure (l' <> [", "] <> ls')

fmtPatRec :: (Name, UncheckedPat) -> FmtM Fmt
fmtPatRec (name, t) =
  do
    t' <- fmtPatBase t
    pure ([prettyText name <> " = "] <> t')

fmtPatBase :: UncheckedPat -> FmtM Fmt
fmtPatBase (PatAscription p t loc) =
  do
    c <- comment loc
    p' <- fmtPatBase p
    t' <- fmtTypeExp t
    pure (c <> p' <> [": "] <> t')
fmtPatBase (PatParens p loc) =
  do
    c <- comment loc
    p' <- fmtPatBase p
    pure (c <> ["("] <> p' <> [") "])
fmtPatBase (Id v t loc) =
  do
    c <- comment loc
    t' <- fmtPatType t
    case unAnnot t of
      Just _h -> pure(c <> ["(" <> prettyText v <> ":"] <> t' <> [") "])
      Nothing -> pure (c <> [prettyText v <> " "])
fmtPatBase (TuplePat pats loc) =
  do
    c <- comment loc
    pats' <- fmtTuplePat pats
    pure(c <> ["("] <> pats' <> [") "])
fmtPatBase (RecordPat fs loc) =
  do
    c <- comment loc
    fs' <- fmtPatRecord fs
    pure(c <> ["{"] <> fs' <> ["} "])
fmtPatBase (Wildcard t loc) =
  do
    c <- comment loc
    t' <- fmtPatType t
    case unAnnot t of
      Just _h -> pure(c <> ["(" <> "_" <> ":"] <> t' <> [") "])
      Nothing -> pure (c <> ["_ "])
fmtPatBase (PatLit e _f loc) =
  do
    c <- comment loc
    e' <- fmtPatLit e
    pure (c <> e')
fmtPatBase (PatConstr n _f ps loc) =
  do
    c <- comment loc
    ps' <- fmtMany fmtPatBase ps
    pure (c <> ["#" <> prettyText n <> " "] <> ps')
fmtPatBase (PatAttr attr p loc) =
  do
    c <- comment loc
    p' <- fmtPatBase p
    attr' <- fmtAttrs [attr] 
    pure (c <> attr' <> p')

fmtPatArr :: [UncheckedPat] -> FmtM Fmt
fmtPatArr [] = pure []
fmtPatArr [t] = fmtPatBase t
fmtPatArr (t : ts) =
  do
    ts' <- fmtPatArr ts
    t' <- fmtPatBase t
    pure(t' <> ts')

fmtPatType :: NoInfo PatType -> FmtM Fmt
fmtPatType t =
  do
    case unAnnot t of
      Just t' -> 
        pure [" @" <> "(" <> prettyText t' <> ") "] 
      _ -> pure []

operatorName :: Name -> Bool
operatorName = (`elem` opchars) . T.head . nameToText
  where
    opchars :: String
    opchars = "+-*/%=!><|&^."

fmtLit :: PrimValue -> FmtM Fmt
fmtLit (UnsignedValue (Int8Value v)) = pure [prettyText v <> "u8 "]
fmtLit (UnsignedValue (Int16Value v)) = pure [prettyText v <> "u16 "]
fmtLit (UnsignedValue (Int32Value v)) = pure [prettyText v <> "u32 "]
fmtLit (UnsignedValue (Int64Value v)) = pure [prettyText v <> "u64 "]
fmtLit (SignedValue v) = pure [prettyText v]
fmtLit (BoolValue True) = pure [" true "]
fmtLit (BoolValue False) = pure [" false "]
fmtLit (FloatValue v) = pure [prettyText v <> " "]

fmtRecLit :: [FieldBase NoInfo Name] -> FmtM Fmt
fmtRecLit [] = pure []
fmtRecLit [t] = fmtFieldBase t
fmtRecLit (t : ts) =
  do
    t' <- fmtFieldBase t
    ts' <- fmtRecLit ts
    pure(t' <> [", "] <> ts')

fmtFieldBase :: FieldBase NoInfo Name -> FmtM Fmt
fmtFieldBase (RecordFieldExplicit name e loc) =
  do
    c <- comment loc
    e' <- fmtValExp e
    pure (c <> [prettyText name <> " = "] <> e')
fmtFieldBase (RecordFieldImplicit name _ loc) =
  do
    c <- comment loc
    pure (c <> [prettyText name])

fmtIntersperse :: [Name] -> FmtM Fmt
fmtIntersperse [] = pure []
fmtIntersperse [t] = pure [prettyText t <> " "]
fmtIntersperse (t : ts) =
  do
    ts' <- fmtIntersperse ts
    pure ([prettyText t <> "."] <> ts')

fmtNameComma :: [VName] -> FmtM Fmt
fmtNameComma [] = pure []
fmtNameComma [t] = pure [prettyText t <> " "]
fmtNameComma (t : ts) =
  do
    ts' <- fmtNameComma ts
    pure ([prettyText t <> ", "] <> ts')

fmtMaybeExp :: Maybe UncheckedExp -> FmtM Fmt
fmtMaybeExp (Just e) = 
  do
    e' <- fmtValExp e
    pure (e' <> [": "])
fmtMaybeExp Nothing = pure []

-- fmtMaybeExpDue :: Maybe UncheckedExp -> FmtM Fmt
-- fmtMaybeExpDue (Just e) = 
--   do
--     e' <- fmtValExp e
--     pure ([" :"] <> e')
-- fmtMaybeExpDue Nothing = pure []

fmtDimIndex :: UncheckedDimIndex -> FmtM Fmt
fmtDimIndex (DimFix e) = fmtValExp e
fmtDimIndex (DimSlice i j (Just s)) =
  do
    i' <- fmtMaybeExp i
    j' <- fmtMaybeExp j
    s' <- fmtValExp s
    pure (i' <> j' <> s')
fmtDimIndex (DimSlice i (Just j) s) =
  do
    i' <- fmtMaybeExp i
    s' <- fmtMaybeExp s
    j' <- fmtValExp j
    pure (i' <>  j' <> s')
fmtDimIndex (DimSlice i Nothing Nothing) =
  do
    fmtMaybeExp i

fmtSliceBase :: UncheckedSlice -> FmtM Fmt
fmtSliceBase [] = pure []
fmtSliceBase [t] = fmtDimIndex t
fmtSliceBase (t : ts) =
  do
    t' <- fmtDimIndex t
    ts' <- fmtSliceBase ts
    pure (t' <> [", "] <> ts')

fmtValMany :: [UncheckedExp] -> FmtM Fmt
fmtValMany [] = pure []
fmtValMany [t]= fmtValExp t
fmtValMany (l : ls) =
  do
    l' <- fmtValExp l
    ls' <- fmtValMany ls
    pure(l' <> [", "] <> ls')

fmtBinOp :: QualName Name -> FmtM Fmt
fmtBinOp bop =
  case leading of
    Backtick ->
      do
        pure["`" <> prettyText bop <> "`"]
    _ -> pure [prettyText bop]
    where
      leading = leadingOperator $ toName $ qualLeaf bop

fmtFormatBinOp :: QualName Name -> UncheckedExp -> UncheckedExp -> FmtM Fmt
fmtFormatBinOp bop x y =
  do
    x' <- fmtValExp x
    y' <- fmtValExp y
    bop' <- fmtBinOp bop
    pure (x' <> bop' <> [" "] <> y') -- add space between x and bop if you remove space after all val

fmtFields :: [Name] -> FmtM Fmt
fmtFields [] = pure []
fmtFields [t] = pure ["." <> prettyText t]
fmtFields (l : ls) =
  do
    ls' <- fmtFields ls
    pure(["." <> prettyText l <> " "] <> ls')

fmtCaseBase :: UncheckedCase -> FmtM Fmt
fmtCaseBase (CasePat p e loc) =
  do
    c <- comment loc
    p' <- fmtPatBase p
    e' <- fmtValExp e
    pure (c <> ["\ncase "] <> p' <> ["-> "] <> e')

fmtNameBracket :: [VName] -> FmtM Fmt
fmtNameBracket [] = pure []
fmtNameBracket [t] = pure ["[" <> prettyText t <> "] "]
fmtNameBracket (l : ls) =
  do
    ls' <- fmtNameBracket ls
    pure (["[" <> prettyText l <> "] "] <> ls' )

fmtLoopForm :: LoopFormBase NoInfo Name -> FmtM Fmt
fmtLoopForm (For i ubound) =
  do
    ubound' <- fmtValExp ubound
    pure ([" for " <> prettyText i <> " < "] <> ubound')
fmtLoopForm (ForIn x e) =
  do
    x' <- fmtPatBase x
    e' <- fmtValExp e
    pure ([" for "] <> x' <> ["in "] <> e')
fmtLoopForm (While cond) =
  do
    cond' <- fmtValExp cond
    pure ([" while "] <> cond')

fmtSizeBinder :: SizeBinder Name -> FmtM Fmt
fmtSizeBinder (SizeBinder v loc) =
  do
    c <- comment loc
    pure (c <> ["[" <> prettyText v <> "] "]) 

fmtLetBody :: UncheckedExp -> FmtM Fmt
fmtLetBody body@(AppExp LetPat {} _) = fmtValExp body
fmtLetBody body@(AppExp LetFun {} _) = fmtValExp body
fmtLetBody body =
  do
    body' <- fmtValExp body
    pure (["in "] <> body')

fmtAppExp :: AppExpBase NoInfo Name -> FmtM Fmt
fmtAppExp (Coerce e t loc) =
  do
    c <- comment loc
    e' <- fmtValExp e
    t' <- fmtTypeExp t
    pure (c <> e' <> [" :> "] <> t')
fmtAppExp (BinOp (bop, _loc) _pt (x, _s) (y, _f) loc) =
  do
    c <- comment loc
    binop <- fmtFormatBinOp bop x y
    pure (c <> binop <> [" "])
fmtAppExp (Match e cs loc) =
  do
    c <- comment loc
    e' <- fmtValExp e
    cs' <- fmtMany fmtCaseBase (NE.toList cs)
    pure (c <> ["\nmatch "] <> e' <> [" "] <> cs')
fmtAppExp (DoLoop sizeparams pat initexp form loopbody loc) =
  do
    c <- comment loc
    sizeparams' <- fmtNameBracket sizeparams
    pat' <- fmtPatBase pat
    initexp' <- fmtValExp initexp
    form' <- fmtLoopForm form
    loopbody' <- fmtValExp loopbody
    pure (c <> [" loop "] <> sizeparams' <> [" "] <> pat' <> ["="] <> ["\n"] <> ["  "] <> initexp' <> [" "] <> form' <> [" do"] <> ["\n"] <> ["  "] <> loopbody')
fmtAppExp (Index e idxs loc) =
  do
    c <- comment loc
    e' <- fmtValExp e
    idxs' <- fmtSliceBase idxs
    pure (c <> [fst (head (maybeToList (T.unsnoc (mconcat e'))))] <> ["["] <> idxs' <> ["] "])
fmtAppExp (LetPat sizes pat e body loc) =
  do
    c <- comment loc
    sizes' <- fmtMany fmtSizeBinder sizes
    pat' <- fmtPatBase pat
    e' <- fmtValExp e
    body' <- fmtLetBody body
    pure (c <> ["let "] <> sizes' <> [" "] <> pat' <> [" ="] <> ["\n"] <> ["  "] <> e' <> ["\n"] <> ["  "] <> body')
fmtAppExp (LetFun fname (tparams, paramss, retdecl, rettype, e) body loc) =
  do
    c <- comment loc
    tparams' <- fmtMany fmtTypeParam tparams
    params' <- fmtMany fmtPatBase paramss
    e' <- fmtValExp e
    retdecl' <- 
      case retdecl of
        Just v -> 
          do
            v' <- fmtTypeExp v
            pure ([": "] <> v')
        Nothing -> pure []
    body' <- fmtLetBody body
    pure (c <> ["let " <> prettyText fname <> " "] <> tparams' <> [" "] <> params' <> [" "] <> retdecl' <> ["="] <> ["\n"] <> ["  "] <> e' <> ["\n"] <> ["  "] <> body')
fmtAppExp (LetWith dest src idxs ve body loc) =
  do
    c <- comment loc
    idxs' <- fmtSliceBase idxs
    ve' <- fmtValExp ve
    body' <- fmtLetBody body
    if dest == src then
      pure (c <> ["let " <> prettyText dest <> "["] <> idxs' <> ["] " <> "="] <> ["\n"] <> ["  "] <> ve' <> ["\n"] <> ["  "] <> body')
    else
      pure (c <> ["let " <> prettyText dest <> " = " <> prettyText src <> " with" <> "["] <> idxs' <> ["] " <> "="] <> ["\n"] <> ["  "] <> ve' <> ["\n"] <> ["  "] <> body')
fmtAppExp (Range start maybe_step end loc) =
  do
    c <- comment loc
    start' <- fmtValExp start
    maybe_step' <-
      case maybe_step of
        Just v ->
          do
            v' <- fmtValExp v
            pure ([" .. "] <> v')
        Nothing -> pure []
    end' <-
      case end of
        DownToExclusive end' ->
          do
            end'' <- fmtValExp end'
            pure ([" ..> "] <> end'')
        ToInclusive end' ->
          do
            end'' <- fmtValExp end'
            pure ([" ... "] <> end'')
        UpToExclusive end' ->
          do
            end'' <- fmtValExp end'
            pure ([" ..< "] <> end'')
    pure (c <> start' <> maybe_step' <> end')
fmtAppExp (If c t f loc) =
  do
    co <- comment loc
    c' <- fmtValExp c
    t' <- fmtValExp t
    f' <- fmtValExp f
    pure(co <> ["if "] <> c' <> ["\n  then "] <> t' <> ["\n  else "] <> f')
fmtAppExp (Apply f args loc) =
  do
    c <- comment loc
    f' <- fmtValExp f
    args' <- fmtMany fmtValExp (map snd (NE.toList args))
    pure (c <> f' <> [" "] <> args')

fmtValExp :: UncheckedExp -> FmtM Fmt
fmtValExp (Var name t loc) =
  do
    c <- comment loc
    t' <- fmtPatType t
    if operatorName(toName (qualLeaf name)) then
      pure(c <> ["(" <> prettyText name] <> t' <> [") "])
    else
      pure (c <> [prettyText name <> " "] <> t')
fmtValExp (Hole t loc) =
  do
    c <- comment loc
    t' <- fmtPatType t
    pure (c <> ["???"] <> t')
fmtValExp (Parens e loc) =
  do
    c <- comment loc
    e' <- fmtValExp e
    pure (c <> ["("] <> e' <> [") "])
fmtValExp (QualParens (v, vloc) e loc) =
  do
    vc' <- comment vloc
    c' <- comment loc
    e' <- fmtValExp e
    pure(vc' <> c' <> [prettyText v <> "." <> "("] <> e' <> [") "])
fmtValExp (Ascript e t loc) =
  do
    c <- comment loc
    e' <- fmtValExp e
    t' <- fmtTypeExp t
    pure (c <> e' <> [": "] <> t')
fmtValExp (Literal v loc) =
  do
    c <- comment loc
    v' <- fmtLit v
    pure (c <> v')
fmtValExp (IntLit v t loc) =
  do
    c <- comment loc
    t' <- fmtPatType t
    pure (c <> [prettyText v <> " "] <> t')
fmtValExp (FloatLit v t loc) =
  do
    c <- comment loc
    t' <- fmtPatType t
    pure (c <> [prettyText v <> " "] <> t')
fmtValExp (TupLit es loc) =
  do
    c <- comment loc
    es' <- fmtValMany es
    pure (c <> ["("] <> es' <> [") "])
fmtValExp (RecordLit fs loc) =
  do
    c <- comment loc
    fs' <- fmtRecLit fs
    pure(c <> ["{"] <> fs' <> ["} "])
fmtValExp (ArrayLit es t loc) =
  do
    c <- comment loc
    es' <- fmtValMany es
    t' <- fmtPatType t
    pure (c <> ["["] <> es' <> [" "] <> t' <> ["] "])
fmtValExp (StringLit s loc) =
  do
    c <- comment loc
    pure (c <> [prettyText s <> " "])
fmtValExp (Project k e _pt loc) =
  do
    c <- comment loc
    e' <- fmtValExp e
    pure (c <> e' <> ["." <> prettyText k <> " "])
fmtValExp (Negate e loc) =
  do
    c <- comment loc
    e' <- fmtValExp e
    pure (c <> ["-"] <> e')
fmtValExp (Not e loc) =
  do
    c <- comment loc
    e' <- fmtValExp e
    pure (c <> ["!"] <> e')
fmtValExp (Update src idxs ve loc) =
  do
    c <- comment loc
    src' <- fmtValExp src
    idxs' <- fmtSliceBase idxs
    ve' <- fmtValExp ve
    pure (c <> src' <> [" with" <> "["] <> idxs' <> ["]" <> "="] <> ["\n"] <> ["  "] <> ve')
fmtValExp (RecordUpdate src fs ve _f loc) =
  do
    c <- comment loc
    src' <- fmtValExp src
    fs' <- fmtIntersperse fs
    ve' <- fmtValExp ve
    pure (c <> src' <> [" with "] <> fs' <> ["="] <> ["\n"] <> ["  "] <> ve')
fmtValExp (Assert e1 e2 _f loc) =
  do
    c <- comment loc
    e1' <- fmtValExp e1
    e2' <- fmtValExp e2
    pure (c <> [" assert "] <> e1' <> [" "] <> e2')
fmtValExp (Lambda pparams body rettype _f loc) =
  do
    c <- comment loc
    params' <- fmtPatArr pparams
    rettype' <-
      case rettype of
        Just t ->
          do
            t' <- fmtTypeExp t
            pure ([": "] <> t')
        Nothing -> pure []
    body' <- fmtValExp body
    pure(c <> ["\\"] <> params' <> [" "] <> rettype' <> [" -> "] <> body')
fmtValExp (OpSection binop _f loc) =
  do
    c <- comment loc
    pure(c <> ["(" <> prettyText binop <> ") "])
fmtValExp (OpSectionLeft binop _ x _ _ loc) = --go check here
  do
    c <- comment loc
    x' <- fmtValExp x
    binop' <- fmtBinOp binop
    pure (c <> ["("] <> x' <> [" "] <> binop' <> [") "])
fmtValExp (OpSectionRight binop _ x _ _ loc) = 
  do
    c <- comment loc
    x' <- fmtValExp x
    binop' <- fmtBinOp binop
    pure (c <> ["("] <> binop' <> [" "] <> x' <> [") "])
fmtValExp (ProjectSection fields _ loc) = 
  do
    c <- comment loc
    fields' <- fmtFields fields
    pure (c <> ["("] <> fields' <> [") "])
fmtValExp (IndexSection idxs _ loc) =
  do
    c <- comment loc
    idxs' <- fmtSliceBase idxs
    pure (c <> ["(" <> "." <> "["] <> idxs' <> ["]" <> ") "])
fmtValExp (Constr n cs t loc) =
  do
    c <- comment loc
    cs' <- fmtValMany cs
    t' <- fmtPatType t
    pure (c <> ["#" <> prettyText n <> " "] <> cs' <> [" "] <> t')
fmtValExp (Attr attr e loc) =
  do
    c <- comment loc
    attr' <- fmtAttrs [attr]
    e' <- fmtValExp e
    pure (c <> ["#["] <> attr' <> ["] "] <> e')
fmtValExp (AppExp e res) =
  do
    case unAnnot res of
      Just (AppRes t ext) ->
        if not $ null ext then
          do
            app <- fmtAppExp e
            ext' <- fmtNameComma ext
            pure (["("] <> app <> ["@" <> "(" <> prettyText t <> "," <> "["] <> ext' <> ["]" <> ")" <> ") "])
        else
          fmtAppExp e
      _ -> fmtAppExp e

--missing a check with rettype
fmtValBind :: UncheckedValBind -> FmtM Fmt
fmtValBind (ValBind entry name retdecl rettype tparams args body dc attrs loc) =
  do
    c <- comment loc
    dc' <- fmtDocComment dc
    attrs' <- fmtAttrs attrs
    ps' <- fmtMany fmtTypeParam tparams
    args' <- fmtPatArr args
    body' <- fmtValExp body
    retdec1' <-
      case retdecl of
        Just ret -> 
          do
            ret' <- fmtTypeExp ret
            pure ([": "] <> ret')
        Nothing -> pure []
    entry' <-
      case entry of
      Just _ -> pure ["\nentry "] 
      Nothing -> pure ["\ndef "]
    pure (c <> dc' <> attrs' <> entry' <> [prettyText name <> " "] <> ps' <> [" "] <> args' <> [" "] <> retdec1' <> [" ="] <> ["\n"] <> ["  "] <> body' <> ["\n"])

fmtSpecBase :: UncheckedSpec -> FmtM Fmt
fmtSpecBase (TypeAbbrSpec tpsig) = fmtTypeBind tpsig
fmtSpecBase (TypeSpec l name ps dc loc) =
  do
    dc' <- fmtDocComment dc
    c <- comment loc
    ps' <- fmtMany fmtTypeParam ps
    pure(c <> dc' <> ["\ntype" <> prettyText l <> " " <> prettyText name <> " "] <> ps')
fmtSpecBase (ValSpec name tparams vtype _ dc loc) =
  do
    dc' <- fmtDocComment dc
    c <- comment loc
    tparams' <- fmtMany fmtTypeParam tparams
    vtype' <- fmtTypeExp vtype
    pure(c <> dc' <> ["\nval " <> prettyText name <> " "] <> tparams' <> [":"] <> vtype')
fmtSpecBase (ModSpec name sig dc loc) =
  do
    dc' <- fmtDocComment dc
    c <- comment loc
    sig' <- fmtSigExp sig
    pure(c <> dc' <> ["module " <> prettyText name <> ":"] <> sig')
fmtSpecBase (IncludeSpec e loc) =
  do
    c <- comment loc
    e' <- fmtSigExp e
    pure(c <> ["include "] <> e')

fmtSpec :: [UncheckedSpec] -> FmtM Fmt
fmtSpec [] = pure []
fmtSpec [t] = fmtSpecBase t
fmtSpec (t : ts) =
  do
    t' <- fmtSpecBase t
    ts' <- fmtSpec ts
    pure(t' <> [" "] <> ts')

fmtSigExp :: UncheckedSigExp -> FmtM Fmt
fmtSigExp (SigVar v _ loc) =
  do
    c <- comment loc
    pure (c <> [prettyText v <> " "])
fmtSigExp (SigParens e loc) =
  do
    c <- comment loc
    e' <- fmtSigExp e
    pure (c <> ["("] <> e' <> [") "])
fmtSigExp (SigSpecs ss loc) = 
  do
    c <- comment loc
    ss' <- fmtSpec ss
    pure (c <> ["{"] <> ss' <> ["} "])
fmtSigExp (SigWith s (TypeRef v ps td _loc1) loc) =
  do
    c <- comment loc
    s' <- fmtSigExp s
    ps' <- fmtMany fmtTypeParam ps
    td' <- fmtTypeExp td
    pure (c <> s' <> [" with " <> prettyText v <> " "] <> ps' <> [" ="] <> ["\n"] <> ["  "] <> td')
fmtSigExp (SigArrow (Just v) e1 e2 loc) =
  do
    c <- comment loc
    e1' <- fmtSigExp e1
    e2' <- fmtSigExp e2
    pure (c <> ["(" <> prettyText v <> ":"] <> e1' <> [") " <> "-> "] <> e2')
fmtSigExp (SigArrow Nothing e1 e2 loc) =
  do
    c <- comment loc
    e1' <- fmtSigExp e1
    e2' <- fmtSigExp e2
    pure (c <> e1' <> [" ->" ] <> e2')

fmtSigBind :: UncheckedSigBind -> FmtM Fmt
fmtSigBind (SigBind name e dc loc) =
  do
    c <- comment loc
    dc' <- fmtDocComment dc
    e' <- fmtSigExp e
    pure (c <> dc' <> ["module type " <> prettyText name <> " ="] <> ["\n"] <> ["  "] <> e' <> ["\n"])

fmtModExp :: UncheckedModExp -> FmtM Fmt
fmtModExp (ModVar v loc) =
  do
    c <- comment loc
    pure (c <> [prettyText v])
fmtModExp (ModParens e loc) =
  do
    c <- comment loc
    e' <- fmtModExp e
    pure (c <> ["("] <> e' <> [") "])
fmtModExp (ModImport v _iname loc) = 
  do
    c <- comment loc
    pure(c <> ["import " <> prettyText (show v) <> " "])
fmtModExp (ModDecs ds loc) = 
  do
    c <- comment loc
    ds' <- fmtMany fmtDec ds
    pure (c <> ["{"] <> ds' <> ["} "])
fmtModExp (ModApply f a _uf _hf loc) =
  do
    c <- comment loc
    f' <- fmtModExp f
    a' <- fmtModExp a
    pure (c <> ["("] <> f' <> ["("] <> a'<> [")" <> ") "])
fmtModExp (ModAscript me se _f loc) = 
  do
    c <- comment loc
    me' <- fmtModExp me
    se' <- fmtSigExp se
    pure (c <> me' <> [": "] <> se')
fmtModExp (ModLambda param maybe_sig body loc) =
  do
    c <- comment loc
    param' <- fmtModParam param
    maybe_sig' <-
      case maybe_sig of
        Just (sig, _) ->
          do
            sig' <- fmtSigExp sig
            pure ([": "] <> sig')
        Nothing -> pure []
    body' <- fmtModExp body
    pure (c <> ["\\"] <> param' <> maybe_sig' <> [" -> "] <> body')

fmtModParam :: ModParamBase NoInfo Name -> FmtM Fmt
fmtModParam (ModParam pname psig _f loc) =
  do
    c <- comment loc
    psig' <- fmtSigExp psig
    pure (c <> [prettyText pname <> ": "] <> psig')

fmtModBind :: UncheckedModBind -> FmtM Fmt
fmtModBind (ModBind name ps sig e dc loc) =
  do
    c <- comment loc
    dc' <- fmtDocComment dc
    ps' <- fmtMany fmtModParam ps
    sig' <- 
      case sig of
        Just (s,_) -> 
          do
            s' <- fmtSigExp s
            pure ([": "] <> s')
        Nothing -> pure []
    e' <- fmtModExp e
    pure (c <> dc' <> ["module " <> prettyText name <> " "] <> ps' <> sig' <> [" ="] <> ["\n"] <> ["  "] <> e' <> ["\n"])

fmtDec :: UncheckedDec -> FmtM Fmt
fmtDec (TypeDec tb) = fmtTypeBind tb
fmtDec (ValDec vb) = fmtValBind vb
fmtDec (SigDec sb) = fmtSigBind sb
fmtDec (ModDec mb) = fmtModBind mb
fmtDec (OpenDec ob loc) =
  do
    c <- comment loc
    ob' <- fmtModExp ob
    pure (c <> ["\nopen "] <> ob' <> ["\n"])
fmtDec (LocalDec lb loc) =
  do
    c <- comment loc
    lb' <- fmtDec lb
    pure (c <> ["\nlocal "] <> lb' <> ["\n"])
fmtDec (ImportDec ib _a loc) = 
  do
    c <- comment loc
    pure(c <> ["\nimport " <> prettyText (show ib)] <> ["\n"])

cum :: [Comment] -> FmtM Fmt
cum [] = pure []
cum [t] = pure ["\n" <> commentText t]
cum (l : ls) =
  do
    l' <- cum [l]
    ls' <- cum ls
    pure(l' <> ls')

-- | Does not return residual comments, because these are simply
-- inserted at the end.
fmtProg :: UncheckedProg -> FmtM Fmt
fmtProg (Prog dc decs) =
  do 
    dc' <- fmtDocComment dc
    decs' <- fmtMany fmtDec decs
    cs <- get
    cs' <- cum cs
    pure (dc' <> decs' <> cs')

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
          --This was printing the number of the line to be able to check if something was wrong
          --let number i l = T.pack $ printf "%4d %s" (i :: Int) l
          --T.hPutStr stdout $ T.unlines $ zipWith number [0 ..] $ evalState (fmtProg prog) cs
          T.hPutStr stdout $ T.concat $ evalState (fmtProg prog) cs
    _ -> Nothing
