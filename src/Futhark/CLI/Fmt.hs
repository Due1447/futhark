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
import GHC.Base (undefined, Any, Levity (Unlifted))
import Prelude
import Language.Haskell.TH.PprLib (dcolon)
import Text.Regex.TDFA.Pattern (starTrans')
import Statistics.Sample (mean)
import Futhark.CodeGen.ImpGen (dPrim)
import Data.ByteString (intersperse)
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict qualified as MS
import Data.Data (Constr)
import GHC.GHCi (NoIO)
import Language.C (TypeSpec)
import Data.Text.Prettyprint.Doc (Pretty(pretty))
import Futhark.CodeGen.ImpCode (DimSize, BinOp)
import Language.Futhark.Parser.Monad (binOp)
import Futhark.Analysis.HORep.MapNest (params)
import Language.Futhark.TypeChecker.Monad (unappliedFunctor)
import Language.Futhark.TypeChecker.Terms.DoLoop (UncheckedLoop)
import Futhark.IR (RepTypes(RetType), Shape, Diet (Observe), TypeBase, Ident (identName))
import Data.Aeson (Array)
import Control.Arrow (Arrow (second))
import qualified Data.Aeson.KeyMap as M
import qualified Data.Map.Strict as MS

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

fmtRecordColon :: (Name, UncheckedTypeExp) -> FmtM Fmt
fmtRecordColon (tf,ts) = 
  do
    ts' <- fmtTypeExp ts
    pure([prettyText tf] <> [":"] <> ts')

fmtRecordTypeElems :: [(Name, UncheckedTypeExp)] -> FmtM Fmt
fmtRecordTypeElems [] = pure []
fmtRecordTypeElems [t] = fmtRecordColon t
fmtRecordTypeElems (t : ts) =
  do 
     t' <- fmtRecordColon t
     ts' <- fmtRecordTypeElems ts
     pure (t' <> [","] <> ts')

fmtPrettyList :: [UncheckedTypeExp] -> FmtM Fmt
fmtPrettyList [] = pure []
fmtPrettyList [t] = fmtTypeExp t
fmtPrettyList (t : ts) =
  do
    t' <- fmtTypeExp t
    ts' <- fmtPrettyList ts
    pure (t' <> ts')

fmtSum :: [(Name, [UncheckedTypeExp])] -> FmtM Fmt
fmtSum [] = pure []
fmtSum [(tf,ts)] = 
  do
    ts' <- fmtPrettyList ts
    pure (["#" <> prettyText tf] <> ts')
fmtSum (t : ts) =
  do
    t' <- fmtSum [t]
    ts' <- fmtSum2 ts
    pure (t' <> ts')

-- is here so I can make sure that the first sum doesn't have a |
fmtSum2 :: [(Name, [UncheckedTypeExp])] -> FmtM Fmt
fmtSum2 [] = pure []
fmtSum2 [(tf,ts)] = 
  do
    ts' <- fmtPrettyList ts
    pure (["|"] <> ["#" <> prettyText tf] <> ts')
fmtSum2 (t : ts) =
  do
    t' <- fmtSum2 [t]
    ts' <- fmtSum2 ts
    pure (t' <> ts')

fmtDimBrac :: [Name] -> FmtM Fmt
fmtDimBrac [] = pure []
fmtDimBrac [t] = pure (["["] <> [prettyText t] <> ["]"])
fmtDimBrac (l : ls) =
  do
    ls' <- fmtDimBrac ls
    pure(["["] <> [prettyText l] <> ["]"] <> ls')

fmtSizeExp :: SizeExp NoInfo Name -> FmtM Fmt
fmtSizeExp SizeExpAny {} = pure ["[]"]
fmtSizeExp (SizeExp e loc) =
  do
    c <- comment loc
    e' <- fmtValExp (-1) e
    pure(c <> ["["] <> e' <> ["]"])

fmtTypeArgExp :: TypeArgExp NoInfo Name -> FmtM Fmt
fmtTypeArgExp (TypeArgExpSize d) = fmtSizeExp d
fmtTypeArgExp (TypeArgExpType t) = fmtTypeExp t

-- I'm unsure if [prettyText l] is enough to evaluate the liftedness
-- If not then this function exists
--fmtLifted :: Liftedness -> FmtM Fmt
--fmtLifted Language.Futhark.Unlifted = pure [""]
--fmtLifted Language.Futhark.SizeLifted = pure ["~"]
--fmtLifted Language.Futhark.Lifted = pure ["^"]

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
fmtTypeExp (TEParens te loc) =
  do
    c <- comment loc
    te' <- fmtTypeExp te
    pure (c <> ["("] <> te' <> [")"])
fmtTypeExp (TERecord rs loc) = 
  do
    c <- comment loc
    rs' <- fmtRecordTypeElems rs
    pure (c <> ["["] <> rs' <> ["]"])
fmtTypeExp (TEArray d at loc) =
  do
    c <- comment loc
    d' <- fmtSizeExp d
    at' <- fmtTypeExp at
    pure (c <> d' <> at')
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
    pure (c <> t' <> arg')
fmtTypeExp (TEArrow (Just v) t1 t2 loc) =
  do
    c <- comment loc
    t1' <- fmtTypeExp t1
    t2' <- fmtTypeExp t2
    pure (c <> ["("] <> [prettyText v] <> [":"] <> t1' <> [")"] <> [" -> "] <> t2')
fmtTypeExp (TEArrow Nothing t1 t2 loc) =
  do
    c <- comment loc
    t1' <- fmtTypeExp t1
    t2' <- fmtTypeExp t2
    pure (c <> t1' <> ["->"] <> t2')
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
    pure (c <> ["?"] <> ["["] <> dims' <> ["]"] <> ["."] <> te')

fmtTypeParam :: UncheckedTypeParam -> FmtM Fmt
fmtTypeParam (TypeParamDim name loc) =
  do
    c <- comment loc
    pure (c <> ["["] <> [prettyText name] <> ["]"])
fmtTypeParam (TypeParamType l name loc) =
  do
    c <- comment loc
    --l' <- fmtLifted l
    pure (c <> ["'"] <> [prettyText l] <> [prettyText name]) 

fmtTypeBind :: UncheckedTypeBind -> FmtM Fmt
fmtTypeBind (TypeBind name l ps e NoInfo dc loc) =
  do
     c <- comment loc 
     dc' <- fmtDocComment dc
     --l' <- fmtLifted l
     ps' <- fmtMany fmtTypeParam ps
     e' <- fmtTypeExp e
     pure (c <> dc' <> ["type"] <> [prettyText l] <> [prettyText name] <> ps' <> ["="] <> e')

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
    attrs' <- fmtMany fmtAttrInfo attrs
    pure (c <> [prettyText f] <> ["("] <> attrs' <> [")"])

fmtAttrs :: [AttrInfo Name] -> FmtM Fmt
fmtAttrs [] = pure []
fmtAttrs [t] = fmtAttrInfo t
fmtAttrs (t : ts) =
  do
    t' <- fmtAttrInfo t
    ts' <- fmtAttrs ts
    pure (["#" <> "["] <> t' <> ts' <> ["]"])

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

fmtPatRecord :: [(Name, UncheckedPat)] -> FmtM Fmt
fmtPatRecord [] = pure []
fmtPatRecord [t] = fmtPatRec t
fmtPatRecord (l : ls) =
  do
    l' <- fmtPatRec l
    ls' <- fmtPatRecord ls
    pure (l' <> [","] <> ls')

fmtPatRec :: (Name, UncheckedPat) -> FmtM Fmt
fmtPatRec (name, t) =
  do
    t' <- fmtPatBase t
    pure ([prettyText name] <> ["="] <> t')

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
    c <- comment loc
    fs' <- fmtPatRecord fs
    pure(c <> fs')
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
    pure (c <> ["#" <> prettyText n] <> ps')
fmtPatBase (PatAttr attr p loc) =
  do
    c <- comment loc
    p' <- fmtPatBase p
    attr' <- fmtAttrInfo attr 
    pure (c <> ["#" <> "["] <> attr' <> ["]"] <> p')

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

fmtNameComma :: [VName] -> FmtM Fmt
fmtNameComma [] = pure []
fmtNameComma [t] = pure [prettyText t]
fmtNameComma (t : ts) =
  do
    ts' <- fmtNameComma ts
    pure ([prettyText t] <> [","] <> ts')

fmtMaybeExp :: Maybe UncheckedExp -> FmtM Fmt
fmtMaybeExp (Just e) = fmtValExp (-1) e
fmtMaybeExp Nothing = pure []

fmtDimIndex :: UncheckedDimIndex -> FmtM Fmt
fmtDimIndex (DimFix e) = fmtValExp (-1) e
fmtDimIndex (DimSlice i j (Just s)) =
  do
    i' <- fmtMaybeExp i
    j' <- fmtMaybeExp j
    s' <- fmtValExp (-1) s
    pure (i' <> [":"] <> j' <> [":"] <> s')
fmtDimIndex (DimSlice i (Just j) s) =
  do
    i' <- fmtMaybeExp i
    s' <- fmtMaybeExp s
    j' <- fmtValExp (-1) j
    pure (i' <> [":"] <> j' <> [":"] <> s')
fmtDimIndex (DimSlice i Nothing Nothing) =
  do
    i' <- fmtMaybeExp i
    pure (i' <> [":"])

fmtSliceBase :: UncheckedSlice -> FmtM Fmt
fmtSliceBase [] = pure []
fmtSliceBase [t] = fmtDimIndex t
fmtSliceBase (t : ts) =
  do
    t' <- fmtDimIndex t
    ts' <- fmtSliceBase ts
    pure (t' <> [","] <> ts')

fmtValMany ::Int -> [UncheckedExp] -> FmtM Fmt
fmtValMany _ [] = pure []
fmtValMany p [t]= fmtValExp p t
fmtValMany p (l : ls) =
  do
    l' <- fmtValExp p l
    ls' <- fmtValMany p ls
    pure(l' <> [","] <> ls')

fmtBinOp :: QualName Name -> FmtM Fmt
fmtBinOp bop =
  case leading of
    Backtick ->
      do
        pure(["`"] <> [prettyText bop] <> ["`"])
    _ -> pure [prettyText bop]
    where
      leading = leadingOperator $ toName $ qualLeaf bop

fmtFormatBinOp :: Int -> QualName Name -> UncheckedExp -> UncheckedExp -> FmtM Fmt
fmtFormatBinOp p bop x y =
  do
    x' <- fmtValExp symPrecedence x
    y' <- fmtValExp symRPrecedence y
    bop' <- fmtBinOp bop
    if p > symPrecedence then
      pure (["("] <> x' <> bop' <> y' <> [")"])
    else
      pure (x' <> bop' <> y')
    where
      leading = leadingOperator $ toName $ qualLeaf bop
      symPrecedence = precedence leading
      symRPrecedence = rprecedence leading
      precedence PipeRight = -1
      precedence PipeLeft = -1
      precedence LogAnd = 0
      precedence LogOr = 0
      precedence Band = 1
      precedence Bor = 1
      precedence Xor = 1
      precedence Equal = 2
      precedence NotEqual = 2
      precedence Bang = 2
      precedence Equ = 2
      precedence Less = 2
      precedence Leq = 2
      precedence Greater = 2
      precedence Geq = 2
      precedence ShiftL = 3
      precedence ShiftR = 3
      precedence Plus = 4
      precedence Minus = 4
      precedence Times = 5
      precedence Divide = 5
      precedence Mod = 5
      precedence Quot = 5
      precedence Rem = 5
      precedence Pow = 6
      precedence Backtick = 9
      rprecedence Minus = 10
      rprecedence Divide = 10
      rprecedence op = precedence op

fmtFields :: [Name] -> FmtM Fmt
fmtFields [] = pure []
fmtFields [t] = pure (["."] <> [prettyText t])
fmtFields (l : ls) =
  do
    ls' <- fmtFields ls
    pure(["."] <> [prettyText l] <> ls')

fmtCaseBase :: UncheckedCase -> FmtM Fmt
fmtCaseBase (CasePat p e loc) =
  do
    c <- comment loc
    p' <- fmtPatBase p
    e' <- fmtValExp (-1) e
    pure (c <> ["case"] <> p' <> ["->"] <> e')

fmtNameBracket :: [VName] -> FmtM Fmt
fmtNameBracket [] = pure []
fmtNameBracket [t] = pure (["["] <> [prettyText t] <> ["]"])
fmtNameBracket (l : ls) =
  do
    ls' <- fmtNameBracket ls
    pure (["["] <> [prettyText l] <> ["]"] <> ls')

fmtLoopForm :: LoopFormBase NoInfo Name -> FmtM Fmt
fmtLoopForm (For i ubound) =
  do
    ubound' <- fmtValExp (-1) ubound
    pure (["for"] <> [prettyText i] <> ["<"] <> ubound')
fmtLoopForm (ForIn x e) =
  do
    x' <- fmtPatBase x
    e' <- fmtValExp (-1) e
    pure (["for"] <> x' <> ["in"] <> e')
fmtLoopForm (While cond) =
  do
    cond' <- fmtValExp (-1) cond
    pure (["while"] <> cond')

fmtSizeBinder :: SizeBinder Name -> FmtM Fmt
fmtSizeBinder (SizeBinder v loc) =
  do
    c <- comment loc
    pure (c <> ["["] <> [prettyText v] <> ["]"]) 

fmtLetBody :: UncheckedExp -> FmtM Fmt
fmtLetBody body@(AppExp LetPat {} _) = fmtValExp (-1) body
fmtLetBody body@(AppExp LetFun {} _) = fmtValExp (-1) body
fmtLetBody body =
  do
    body' <- fmtValExp (-1) body
    pure (["in"] <> body')

fmtShapeSize :: Language.Futhark.Shape Size -> FmtM Fmt
fmtShapeSize (Shape ds) = pure ["MISSING_FmtShapeSize"]

fmtTypeArg :: Int -> TypeArg Size -> FmtM Fmt
fmtTypeArg _ (TypeArgDim d) = fmtSize d
fmtTypeArg p (TypeArgType t) = fmtType p t

fmtTypeArgs :: Int -> [TypeArg Size] -> FmtM Fmt
fmtTypeArgs _ [] = pure []
fmtTypeArgs p [t] = fmtTypeArg p t
fmtTypeArgs p (l : ls) =
  do
    l' <- fmtTypeArg p l
    ls' <- fmtTypeArgs p ls
    pure (l' <> ls')

fmtDiet :: Language.Futhark.Diet -> FmtM Fmt
fmtDiet Consume = pure ["*"]
fmtDiet Language.Futhark.Observe = pure [""]

fmtScalarRec :: [Language.Futhark.TypeBase Size ()] -> FmtM Fmt
fmtScalarRec [] = pure []
fmtScalarRec [t] = fmtType 0 t
fmtScalarRec (l : ls) =
  do
    l' <- fmtType 0 l
    ls' <- fmtScalarRec ls
    pure (l' <> [","] <> ls')

fmtScalarRecord :: (Name, Language.Futhark.TypeBase Size ()) -> FmtM Fmt
fmtScalarRecord (n, fs) = 
  do
    fs' <- fmtType 0 fs
    pure ([prettyText n] <> [":"] <> fs')

fmtScalarSum :: [(Name, [Language.Futhark.TypeBase Size ()])] -> FmtM Fmt
fmtScalarSum [] = pure []
fmtScalarSum [(tf,ts)] = 
  do
    ts' <- fmtTypes 2 ts
    pure (["|"] <> ["#" <> prettyText tf] <> ts')
fmtScalarSum (t : ts) =
  do
    t' <- fmtScalarSum [t]
    ts' <- fmtScalarSum ts
    pure (t' <> ts')

fmtScalarType :: Int -> ScalarTypeBase Size () -> FmtM Fmt
fmtScalarType _ (Prim et) = pure [prettyText et]
fmtScalarType p (TypeVar _ u v targs) =
  do
    targs' <- fmtTypeArgs 3 targs
    if not (null targs) && p > 3 then
      pure (["("] <> [prettyText u] <> [prettyText v] <> targs' <> [")"])
    else
      pure ([prettyText u] <> [prettyText v] <> targs')
fmtScalarType _ (Record fs) =
  do
    case areTupleFields fs of
      Just ts ->
        do
          ts' <- fmtScalarRec ts
          pure (["("] <> ts' <> [")"])
      _ -> pure ["MISSING_ScalarType_Record"]
        -- do
        --   f <- MS.toList fs
        --   fs' <- fmtScalarRecord f
        --   pure (["{"] <> fs' <> ["}"])
        -- MS.toList doesnt work because fmtScalarType takes ScalarTypeBase Size (),
        -- the () prevents it from working I think.
fmtScalarType p (Arrow _ (Named v) d t1 t2) =
  do
    d' <- fmtDiet d
    t1' <- fmtType 0 t1
    t2' <- fmtRetType 1 t2
    if p > 1 then
      pure (["("] <> ["("] <> [prettyText v] <> [":"] <> d' <> t1' <> [")"] <> ["->"] <> t2' <> [")"])
    else
      pure (["("] <> [prettyText v] <> [":"] <> d' <> t1' <> [")"] <> ["->"] <> t2')
fmtScalarType p (Arrow _ Unnamed d t1 t2) =
  do
    d' <- fmtDiet d
    t1' <- fmtType 2 t1
    t2' <- fmtRetType 1 t2
    if p > 1 then
      pure (["("] <> d' <> t1' <> ["->"] <> t2' <> [")"])
    else
      pure (d' <> t1' <> ["->"] <> t2')
fmtScalarType p (Sum cs) = pure ["MISSING_ScalarType_SUM"]
  -- do
  --   c <- MS.toList cs
  --   cs' <- fmtScalarSum [c]
  --   if p > 0 then
  --     pure (["("] <> cs' <> [")"])
  --   else
  --     cs'
  -- MS.toList doesnt work because fmtScalarType takes ScalarTypeBase Size (),
  -- the () prevents it from working I think.

fmtSize :: Size -> FmtM Fmt
fmtSize (AnySize Nothing) = pure []
fmtSize (AnySize (Just v)) = pure (["?"] <> [prettyText v])
fmtSize (SizeExpr e) = pure ["MISSING_FmtSize_SizeExpr"] 
--fmtValExp (-1) e
--fmtValExp takes Expbase NoInfo Name, here e is Expbase Info VName

fmtTypes :: Int -> [Language.Futhark.TypeBase Size ()] -> FmtM Fmt
fmtTypes _ [] = pure []
fmtTypes p [t] = fmtType p t
fmtTypes p (l : ls) =
  do
    l' <- fmtType p l
    ls' <- fmtTypes p ls
    pure (l' <> ls')

fmtType :: Int -> Language.Futhark.TypeBase Size () -> FmtM Fmt
fmtType _ (Array _ u shape at) =
  do
    shape' <- fmtShapeSize shape
    at' <- fmtScalarType 1 at
    pure ([prettyText u] <> shape' <> at')
fmtType p (Scalar t) = fmtScalarType p t

fmtRetType :: Int -> RetTypeBase Size () -> FmtM Fmt
fmtRetType p (RetType [] t) =
  fmtType p t
fmtRetType _ (RetType dims t) =
  do
    dims' <- fmtNameBracket dims
    t' <- fmtType 0 t
    pure(["?"] <> dims' <> ["."] <> t')

fmtStructRet :: StructRetType -> FmtM Fmt
fmtStructRet = fmtRetType 0

fmtAppExp :: Int -> AppExpBase NoInfo Name -> FmtM Fmt
fmtAppExp p (Coerce e t loc) =
  do
    c <- comment loc
    e' <- fmtValExp 0 e
    t' <- fmtTypeExp t
    if p /= -1 then
      pure (c <> ["("] <> e' <> [":>"] <> t' <> [")"])
    else
      pure (c <> e' <> [":>"] <> t')
fmtAppExp p (BinOp (bop, _loc) _pt (x, _s) (y, _f) loc) =
  do
    c <- comment loc
    binop <- fmtFormatBinOp p bop x y
    pure (c <> binop)
fmtAppExp _ (Match e cs loc) =
  do
    c <- comment loc
    e' <- fmtValExp (-1) e
    cs' <- fmtMany fmtCaseBase (NE.toList cs)
    pure (c <> ["match"] <> e' <> cs')
fmtAppExp _ (DoLoop sizeparams pat initexp form loopbody loc) =
  do
    c <- comment loc
    sizeparams' <- fmtNameBracket sizeparams
    pat' <- fmtPatBase pat
    initexp' <- fmtValExp (-1) initexp
    form' <- fmtLoopForm form
    loopbody' <- fmtValExp (-1) loopbody
    pure (c <> ["loop"] <> sizeparams' <> pat' <> ["="] <> initexp' <> form' <> ["do"] <> loopbody')
fmtAppExp _ (Index e idxs loc) =
  do
    c <- comment loc
    e' <- fmtValExp 9 e
    idxs' <- fmtSliceBase idxs
    pure (c <> e' <> ["["] <> idxs' <> ["]"])
fmtAppExp p (LetPat sizes pat e body loc) =
  do
    c <- comment loc
    sizes' <- fmtMany fmtSizeBinder sizes
    pat' <- fmtPatBase pat
    e' <- fmtValExp (-1) e
    body' <- fmtLetBody body
    if p /= -1 then
      pure (c <> ["("] <> ["let"] <> sizes' <> pat' <> ["="] <> e' <> body' <> [")"])
    else
      pure (c <> ["let"] <> sizes' <> pat' <> ["="] <> e' <> body')
fmtAppExp _ (LetFun fname (tparams, paramss, retdecl, rettype, e) body loc) =
  do
    c <- comment loc
    tparams' <- fmtMany fmtTypeParam tparams
    params' <- fmtMany fmtPatBase paramss
    e' <- fmtValExp (-1) e
    retdecl' <- 
      case retdecl of
        Just v -> 
          do
            v' <- fmtTypeExp v
            pure ([":"] <> v')
        Nothing -> pure []
    body' <- fmtLetBody body
    pure (c <> ["let"] <> [prettyText fname] <> tparams' <> params' <> retdecl' <> ["="] <> e' <> body')
fmtAppExp _ (LetWith dest src idxs ve body loc) =
  do
    c <- comment loc
    idxs' <- fmtSliceBase idxs
    ve' <- fmtValExp (-1) ve
    body' <- fmtLetBody body
    if dest == src then
      pure (c <> ["let"] <> [prettyText dest] <> ["["] <> idxs' <> ["]"] <> ["="] <> ve' <> body')
    else
      pure (c <> ["let"] <> [prettyText dest] <> ["="] <> [prettyText src] <> ["with"] <> ["["] <> idxs' <> ["]"] <> ["="] <> ve' <> body')
fmtAppExp p (Range start maybe_step end loc) =
  do
    c <- comment loc
    start' <- fmtValExp (-1) start
    maybe_step' <-
      case maybe_step of
        Just v ->
          do
            v' <- fmtValExp (-1) v
            pure ([".."] <> v')
        Nothing -> pure []
    end' <-
      case end of
        DownToExclusive end' ->
          do
            end'' <- fmtValExp (-1) end'
            pure (["..>"] <> end'')
        ToInclusive end' ->
          do
            end'' <- fmtValExp (-1) end'
            pure (["..."] <> end'')
        UpToExclusive end' ->
          do
            end'' <- fmtValExp (-1) end'
            pure (["..<"] <> end'')
    if p /= 1 then
      pure (c <> ["("] <> start' <> maybe_step' <> end' <> [")"])
    else
      pure (c <> start' <> maybe_step' <> end')
fmtAppExp _ (If c t f loc) =
  do
    co <- comment loc
    c' <- fmtValExp (-1) c
    t' <- fmtValExp (-1) t
    f' <- fmtValExp (-1) f
    pure(co <> ["if"] <> c' <> ["then"] <> t' <> ["else"] <> f')
fmtAppExp p (Apply f args loc) = pure ["MISSING_FmtAppExp_Apply"]
  --do
    -- c <- comment loc
    -- f' <- fmtValExp (-1) f
    -- argsl <- snd (NE.toList args)
    -- args' <- fmtValExp (-1) argsl
    -- if p >= 10 then
    --   pure (c <> ["("] <> f' <> args' <> [")"])
    -- else
    --   pure (c <> f' <> args')
    -- NE.toList didn't work here and I am unsure as to why

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
    es' <- fmtValMany (-1) es
    pure (c <> ["("] <> es' <> [")"])
fmtValExp _ (RecordLit fs loc) =
  do
    c <- comment loc
    fs' <- fmtMany fmtFieldBase fs
    pure(c <> fs')
fmtValExp _ (ArrayLit es t loc) =
  do
    c <- comment loc
    es' <- fmtValMany (-1) es
    t' <- fmtPatType t
    pure (c <> ["["] <> es' <> t' <> ["]"])
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
    c <- comment loc
    src' <- fmtValExp (-1) src
    idxs' <- fmtSliceBase idxs
    ve' <- fmtValExp (-1) ve
    pure (c <> src' <> ["with"] <> ["["] <> idxs' <> ["]"] <> ["="] <> ve')
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
fmtValExp p (Lambda pparams body rettype _f loc) =
  do
    c <- comment loc
    params' <- fmtPatArr pparams
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
    c <- comment loc
    pure(c <> ["("] <> [prettyText binop] <> [")"])
fmtValExp _ (OpSectionLeft binop _ x _ _ loc) =
  do
    c <- comment loc
    x' <- fmtValExp (-1) x
    binop' <- fmtBinOp binop
    pure (c <> ["("] <> x' <> binop' <> [")"])
fmtValExp _ (OpSectionRight binop _ x _ _ loc) = 
  do
    c <- comment loc
    x' <- fmtValExp (-1) x
    binop' <- fmtBinOp binop
    pure (c <> ["("] <> binop' <> x' <> [")"])
fmtValExp _ (ProjectSection fields _ loc) = 
  do
    c <- comment loc
    fields' <- fmtFields fields
    pure (c <> ["("] <> fields' <> [")"])
fmtValExp _ (IndexSection idxs _ loc) =
  do
    c <- comment loc
    idxs' <- fmtSliceBase idxs
    pure (c <> ["("] <> ["."] <> ["["] <> idxs' <> ["]"] <> [")"])
fmtValExp p (Constr n cs t loc) =
  do
    c <- comment loc
    cs' <- fmtValMany 10 cs
    t' <- fmtPatType t
    if p >= 10 then
      pure (c <> ["("] <> ["#" <> prettyText n] <> cs' <> t' <> [")"])
    else
      pure (c <> ["#" <> prettyText n] <> cs' <> t')
fmtValExp _ (Attr attr e loc) =
  do
    c <- comment loc
    attr' <- fmtAttrs [attr]
    e' <- fmtValExp (-1) e
    pure (c <> attr' <> e')
fmtValExp i (AppExp e res) =
  do
    case unAnnot res of
      Just (AppRes t ext) ->
        if not $ null ext then
          do
            app <- fmtAppExp i e
            ext' <- fmtNameComma ext
            pure (["("] <> app <> ["@"] <> ["("] <> [prettyText t] <> [","] <> ["["] <> ext' <> ["]"] <> [")"] <> [")"])
        else
          fmtAppExp i e
      _ -> fmtAppExp i e

--missing a check with rettype
fmtValBind :: UncheckedValBind -> FmtM Fmt
fmtValBind (ValBind entry name retdecl rettype tparams args body dc attrs loc) =
  do
    c <- comment loc
    dc' <- fmtDocComment dc
    attrs' <- fmtAttrs attrs
    ps' <- fmtMany fmtTypeParam tparams
    args' <- fmtPatArr args
    body' <- fmtValExp (-1) body
    retdec1' <-
      case retdecl of
        Just ret -> 
          do
            ret' <- fmtTypeExp ret
            pure ([":"] <> ret')
        Nothing -> pure []
    entry' <-
      case entry of
      Just _ -> pure ["entry"]
      Nothing -> pure ["def"]
    pure (c <> dc' <> attrs' <> entry' <> [prettyText name] <> ps' <> args' <> retdec1' <> ["="] <> body')

fmtSpecBase :: UncheckedSpec -> FmtM Fmt
fmtSpecBase (TypeAbbrSpec tpsig) = fmtTypeBind tpsig
fmtSpecBase (TypeSpec l name ps dc loc) =
  do
    dc' <- fmtDocComment dc
    --l' <- fmtLifted l
    c <- comment loc
    ps' <- fmtMany fmtTypeParam ps
    pure(c <> dc' <> ["type"] <> [prettyText l] <> [prettyText name] <> ps')
fmtSpecBase (ValSpec name tparams vtype _ dc loc) =
  do
    dc' <- fmtDocComment dc
    c <- comment loc
    tparams' <- fmtMany fmtTypeParam tparams
    vtype' <- fmtTypeExp vtype
    pure(c <> dc' <> ["type"] <> [prettyText name] <> tparams' <> [":"] <> vtype')
fmtSpecBase (ModSpec name sig dc loc) =
  do
    dc' <- fmtDocComment dc
    c <- comment loc
    sig' <- fmtSigExp sig
    pure(c <> dc' <> ["module"] <> [prettyText name] <> [":"] <> sig')
fmtSpecBase (IncludeSpec e loc) =
  do
    c <- comment loc
    e' <- fmtSigExp e
    pure(c <> ["include"] <> e')

fmtSpec :: [UncheckedSpec] -> FmtM Fmt
fmtSpec [] = pure []
fmtSpec [t] = fmtSpecBase t
fmtSpec (t : ts) =
  do
    t' <- fmtSpecBase t
    ts' <- fmtSpec ts
    pure(t' <> ts')

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
    s' <- fmtSigExp s
    ps' <- fmtMany fmtTypeParam ps
    td' <- fmtTypeExp td
    pure (c <> s' <> ["with"] <> [prettyText v] <> ps' <> ["="] <> td')
fmtSigExp (SigArrow (Just v) e1 e2 loc) =
  do
    c <- comment loc
    e1' <- fmtSigExp e1
    e2' <- fmtSigExp e2
    pure (c <> ["("] <> [prettyText v] <> [":"] <> e1' <> [")"] <> ["->"] <> e2')
fmtSigExp (SigArrow Nothing e1 e2 loc) =
  do
    c <- comment loc
    e1' <- fmtSigExp e1
    e2' <- fmtSigExp e2
    pure (c <> e1' <> ["->"] <> e2')

fmtSigBind :: UncheckedSigBind -> FmtM Fmt
fmtSigBind (SigBind name e dc loc) =
  do
    c <- comment loc
    dc' <- fmtDocComment dc
    e' <- fmtSigExp e
    pure (c <> dc' <> ["module type"] <> [prettyText name] <> ["="] <> e')

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
    pure (c <> [prettyText pname] <> [":"] <> psig')

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
            pure ([":"] <> s')
        Nothing -> pure []
    e' <- fmtModExp e
    pure (c <> dc' <> ["module"] <> [prettyText name] <> ps' <> sig' <> ["="] <> e')

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
    pure(c <> ["import"] <> [prettyText (show ib)])

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
          --This was printing the number of the line to be able to check if something was wrong
          --let number i l = T.pack $ printf "%4d %s" (i :: Int) l
          --T.hPutStr stdout $ T.unlines $ zipWith number [0 ..] $ evalState (fmtProg prog) cs
          T.hPutStr stdout $ T.unlines $ evalState (fmtProg prog) cs
    _ -> Nothing
