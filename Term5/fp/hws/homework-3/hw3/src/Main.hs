{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import Control.Exception (catch)
import Control.Monad.Cont (liftIO)
import qualified Data.Set as Set
import HW3.Action (HIO (..), HiPermission (..), PermissionException)
import HW3.Base (HiValue (HiValueNull))
import HW3.Evaluator (eval)
import HW3.Parser (parse)
import HW3.Pretty (prettyValue)
import Prettyprinter
import Prettyprinter.Render.String (renderString)
import System.Console.Haskeline
import Text.Megaparsec (errorBundlePretty)

main :: IO ()
main = runInputT defaultSettings loop
  where
    loop :: InputT IO ()
    loop = do
      minput <- getInputLine  "hi> "
      case minput of
        Nothing -> return ()
        Just input -> do
          case parse input of
            Left err -> outputStr $ errorBundlePretty err
            Right expr -> do
              res <- liftIO $ catch (runHIO (eval expr) $ Set.fromList [AllowTime, AllowRead, AllowWrite]) $
                \(e :: PermissionException) -> Right HiValueNull <$ print e
              case res of
                Left err -> outputStrLn $ show err
                Right val -> outputStrLn $ renderString $
                  layoutPretty defaultLayoutOptions { layoutPageWidth = Unbounded } $ prettyValue val
          loop

