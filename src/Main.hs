{-# LANGUAGE DataKinds, OverloadedStrings, LambdaCase #-}

module Main where

import QntSyn
import Common
import Data.Proxy
import Data.Text (Text)
import qualified Data.Text.IO as TIO
import Text.Megaparsec
import QntSyn.Parse
import QntSyn.Pretty
import Tqc
import Rename
import Tc
import qualified Data.Map as M

tNat :: Type Qual
tNat = TName $ Qual (Module ["Data", "Nat"]) "Nat"

initTe :: TypeEnv
initTe = M.fromList
  [ (QualName $ Qual (Module ["Data", "Nat"]) "-", Scheme mempty $ tNat `tArrow` tNat `tArrow` tNat)
  ]

initKe :: KindEnv
initKe = M.fromList
  [ (Qual (Module ["Data", "Nat"]) "Nat", KStar)
  , (Qual (Module []) "->", KArrow KStar $ KArrow KStar KStar)
  ]

initCe :: ConstrEnv
initCe = mempty

showTypeErr :: Text -> TypeError -> Text
showTypeErr src = \case
  TeInExpr (L l e) te -> showTypeErr src te <> "\nin expression: " <> printSrc src l
  TeInScheme (L l s) te -> showTypeErr src te <> "\nin scheme: " <> printSrc src l
  TeSchemeMismatch s0 s1 -> "couldn't match scheme " <> pPrintScheme pr s0 <> " with " <> pPrintScheme pr s1
  TeTypeMismatch t0 t1 -> "couldn't match type " <> pPrintType pr t0 <> " with " <> pPrintType pr t1
  TeInfiniteType t0 t1 -> "cannot construct the infinite type " <> pPrintType pr t0 <> " ~ " <> pPrintType pr t1
  TeKindNotStar -> "type is not fully-applied"
  where pr :: Proxy 'Renamed
        pr = Proxy

printSrc :: Text -> SrcSpan -> Text
printSrc src (SrcSpan (SourcePos f l0 c0) (SourcePos _ l1 c1)) = "(TODO source)"

showErr :: Text -> CompileError -> Text
showErr src = \case
  NumRangeErr -> "Numeric literal out of range!"
  TypeErr te  -> showTypeErr src te

main :: IO ()
main = do
  src <- TIO.getContents
  case parse expr "<stdin expr>" src of
    Left err -> do
      putStrLn "Parse error!"
      putStr $ errorBundlePretty err
    Right (L _ eP) -> do
      putStrLn "Parsed!"
      TIO.putStrLn $ pPrintExpr eP
      case runTqc (runRename (renameExpr eP) mempty) TqcConfig of
        Left err -> do
          putStrLn "Error in renaming expr!"
          TIO.putStrLn $ showErr src err
        Right (eR, _) -> do
          putStrLn "Renamed!"
          TIO.putStrLn $ pPrintExpr eR
          case runTqc (runInfer (infer eR) initTe initKe initCe mempty 0) TqcConfig of
            Left err -> do
              putStrLn "Error in typechecking!"
              TIO.putStrLn $ showErr src err
            Right (((ty, eT), sub, _), _) -> do
              putStrLn "Typechecked!"

              TIO.putStrLn $ pPrintExpr eT

              let ty' = applySub sub ty
                  s = generalize mempty ty'

              putStrLn "Inferred scheme:"
              TIO.putStrLn $ pPrintScheme (Proxy :: Proxy 'Typechecked) s
