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
  do t' <- fmtTypeExp t
     ts' <- fmtTupleTypeElems ts
     pure (t' <> [","] <> ts')

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

fmtTypeParam :: UncheckedTypeParam -> FmtM Fmt
fmtTypeParam = undefined

fmtTypeBind :: UncheckedTypeBind -> FmtM Fmt
fmtTypeBind (TypeBind name l ps e NoInfo dc _loc) =
  do
     dc' <- fmtDocComment dc
     ps' <- fmtMany fmtTypeParam ps
     e' <- fmtTypeExp e
     pure (dc' <> ["type" <> prettyText l] <> [prettyText name] <> ps' <> e')

fmtDec :: UncheckedDec -> FmtM Fmt
fmtDec (TypeDec tb) = fmtTypeBind tb

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
