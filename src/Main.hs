module Main where

import qualified Data.Text.IO as TIO
import Text.Megaparsec
import QntSyn.Parse

main :: IO ()
main = do
  src <- TIO.getContents
  case parse expr "<stdin expr>" src of
    Left err -> putStrLn $ errorBundlePretty err
    Right _  -> putStrLn "Parsed!"
