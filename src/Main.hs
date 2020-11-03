module Main where

import qualified Data.Text.IO as TIO
import Text.Megaparsec
import QntSyn
import QntSyn.Parse
import QntSyn.Infer

main :: IO ()
main = do
  t <- TIO.getContents
  case parse expr "<stdin expr>" t of
    Left err -> putStrLn $ errorBundlePretty err
    Right e  -> case doInfer e of
      Left err -> print err
      Right t  -> TIO.putStrLn $ pPrintTypeScheme t
