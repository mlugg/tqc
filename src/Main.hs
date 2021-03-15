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

{-
qualNat :: Text -> Qual
qualNat = Qual (Module ["Data", "Nat"])

tNat :: Type Qual
tNat = TName $ qualNat "Nat"

preludeTe :: TypeEnv
preludeTe = M.fromList
  [ ( QualName $ qualNat "+", Scheme mempety $ tNat `tArrow` tNat `tArrow` tNat)
  , ( QualName $ qualNat "-", Scheme mempety $ tNat `tArrow` tNat `tArrow` tNat)
  , ( QualName $ qualNat "*", Scheme mempety $ tNat `tArrow` tNat `tArrow` tNat)
  , ( QualName $ qualNat "/", Scheme mempety $ tNat `tArrow` tNat `tArrow` tNat)
  ]

preludeKe :: KindEnv
preludeKe = M.fromList
  [ (qualNat "Nat", KStar)
  , (Qual (Module []) "->", KStar `KArrow` KStar `KArrow` KStar)
  ]

preludeCe :: ConstrEnv
preludeCe = M.fromList []

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

  let thisModule = Module ["Main"]

  case parse file "<stdin>" src of
    Left err -> do
      putStrLn "Parse error!"
      putStr $ errorBundlePretty err
    Right (QntProg dataDecls bindings) -> do
      putStrLn "Parsed!"
      TIO.putStrLn $ pPrintExpr eP

      -- Initial kind environment
      let dataDeclKinds = dataDecls <&> \ (DataDecl name args _) ->
            (Qual thisModule name, foldr KArrow KStar (paramKind <$> args))
            where paramKind (TyParam _ k) = k
          initKe = preludeKe <> M.fromList dataDeclKinds

      -- Initial constructor environment
      let dataDeclConstrs = concat $ dataDecls <&> \ (DataDecl dataName tyArgs constrs) ->
            let params = S.fromList $ args <&> \ (TyParam n _) -> n
            in constrs <&> \ (DataConstr constrName constrArgs) ->
              (Qual thisModule constrName, (params, foldl TApp (Qual thisModule dataName) (TVar . TvName <$> params), constrArgs))
            (Qual thisModule name, (S.fromList $ paramName <$> args, t, )
          initCe = preludeCe <> M.fromList dataDeclConstrs

      -- Initial type environment
      let constrTypeEnv = dataDeclConstrs <&> \ (constrName, (tyVars, resultType, argTypes)) ->
            foldr TArrow resultType argTypes
          initTe = preludeTe <$> constrTypeEnv


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
              -}

main :: IO ()
main = pure ()
