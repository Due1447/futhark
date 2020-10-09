-- | @futhark check@
module Futhark.CLI.Check (main) where

import Control.Monad
import Control.Monad.IO.Class
import Futhark.Compiler
import Futhark.Util.Options
import Futhark.Util.Pretty (pretty)
import System.Console.GetOpt
import System.IO

newtype CheckConfig = CheckConfig {checkWarn :: Bool}

newCheckConfig :: CheckConfig
newCheckConfig = CheckConfig True

options :: [FunOptDescr CheckConfig]
options =
  [ Option
      "w"
      []
      (NoArg $ Right $ \cfg -> cfg {checkWarn = False})
      "Disable all warnings."
  ]

-- | Run @futhark check@.
main :: String -> [String] -> IO ()
main = mainWithOptions newCheckConfig options "program" $ \args cfg ->
  case args of
    [file] -> Just $ do
      (warnings, _, _) <- readProgramOrDie file
      when (checkWarn cfg) $
        liftIO $ hPutStr stderr $ pretty warnings
    _ -> Nothing
