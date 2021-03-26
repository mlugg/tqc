{-# LANGUAGE DataKinds, OverloadedStrings, LambdaCase #-}

module Main where

import Cli
import Tqc
import qualified Data.Text.IO as TIO
import qualified QntSyn.Parse
import Text.Megaparsec (parse)
import qualified Data.Map as M
import QntSyn
import Tc
import Common
import qualified Data.Text as T
import qualified Data.Set as S
import Data.Functor
import Data.Traversable
import Data.Foldable
import Control.Monad.IO.Class
import Rename
import qualified QntToNcl
import qualified NclToPhtn
import qualified CodeGen.Gen as CodeGen
import qualified CodeGen.AsmText as AsmText

data ModuleInfo p = ModuleInfo Module [DataDecl p] [QntBind p]

builtinKindEnv :: KindEnv
builtinKindEnv = M.fromList
  [ (Qual (Module []) "->", KStar `KArrow` KStar `KArrow` KStar)
  , (Qual (Module ["Data", "Nat"]) "Nat", KStar)
  ]

builtinTypeEnv :: TypeEnv
builtinTypeEnv = M.fromList
  [ (QualName $ Qual (Module []) "error", Scheme (S.singleton "a") (TName $ Qual (Module []) "a"))
  ]

builtinConstrEnv :: ConstrEnv
builtinConstrEnv = M.fromList
  [
  ]

builtinVars :: [Qual]
builtinVars = M.keys builtinTypeEnv >>= \ case
  QualName q -> [q]
  _          -> []

builtinTypes :: [Qual]
builtinTypes = M.keys builtinKindEnv

compilerMain :: Tqc ()
compilerMain = do
  cfg <- askConf

  infosParsed <- for (tqcFiles cfg) $ \ file -> do
    src <- liftIO $ TIO.readFile (qntSrcName file)
    case parse QntSyn.Parse.file (qntSrcName file) src of
      Left err -> throwErr $ ParseErr err
      Right (QntProg datas binds) -> do
        let modu = Module $ T.split (`elem` ['/', '\\']) $ T.pack $ qntSrcName file
        pure $ ModuleInfo modu datas binds

  let allVars = do
        ModuleInfo modu datas binds <- infosParsed

        let constrVars = do
              DataDecl _ _ constrs <- datas
              DataConstr name _ <- constrs
              pure $ Qual modu name

        let bindVars = do
              b <- binds
              pure $ Qual modu (bindName b)

        constrVars <> bindVars

      allVars' = builtinVars <> allVars

      allTypes = do
        ModuleInfo modu datas _ <- infosParsed
        DataDecl name _ _ <- datas
        pure $ Qual modu name

      allTypes' = builtinTypes <> allTypes

  infosRenamed <- for infosParsed $ \ (ModuleInfo modu datas binds) ->
    runRename' allVars' allTypes' $ do
      datas' <- traverse renameData datas
      binds' <- traverse renameBind binds
      pure $ ModuleInfo modu datas' binds'


  let typeEnv = fold $ do
        ModuleInfo modu datas binds <- infosRenamed

        let constrsEnv = do
              DataDecl typeName params constrs <- datas
              let paramNames = params <&> \ (TyParam n _) -> n
              let typeOut = foldr TApp (TName $ Qual modu typeName) (TName . Qual (Module []) <$> paramNames)
              DataConstr name args <- constrs
              let constrType = foldr tArrow typeOut args
              pure $ M.singleton (QualName $ Qual modu name) (Scheme (S.fromList paramNames) constrType)

        let bindsEnv = do
              b <- binds
              case b of
                QntImpl _ _ -> []
                QntExpl name _ (L _ s) -> pure $ M.singleton (QualName $ Qual modu name) s

        constrsEnv <> bindsEnv

      typeEnv' = builtinTypeEnv <> typeEnv

      kindEnv = fold $ do
        ModuleInfo modu datas _ <- infosRenamed
        DataDecl name params _ <- datas
        let dataKind = foldr (\ (TyParam _ paramKind) k -> paramKind `KArrow` k) KStar params
        pure $ M.singleton (Qual modu name) dataKind

      kindEnv' = builtinKindEnv <> kindEnv

      constrEnv = fold $ do
        ModuleInfo modu datas _ <- infosRenamed
        DataDecl typeName params constrs <- datas
        let paramNames = params <&> \ (TyParam n _) -> n
        let typeOut = foldr TApp (TName $ Qual modu typeName) (TName . Qual (Module []) <$> paramNames)
        DataConstr name args <- constrs
        pure $ M.singleton (Qual modu name) (S.fromList paramNames, typeOut, args)

      constrEnv' = builtinConstrEnv <> constrEnv

  infosTypechecked <- for infosRenamed $ \ (ModuleInfo modu datas binds) -> do
    (info, _) <- runInfer' typeEnv' kindEnv' constrEnv' $ do
      datas' <- traverse (checkDataConstrs modu) datas
      (_, binds') <- inferTopLevelBinds modu binds
      pure $ ModuleInfo modu datas' binds'
    pure info

  for_ (zip infosTypechecked (tqcFiles cfg)) $ \ (ModuleInfo modu datas binds, QuantaFile _ asmOut objOut) -> do
    -- Note that the free variables of these binds are meaningless, as
    -- they are top-level
    nclBinds <- QntToNcl.runConvert' $ traverse QntToNcl.convertBind binds
    (phtnBinds, phtnFuncs) <- NclToPhtn.runCompile' mempty {-TODO-} $ traverse NclToPhtn.compileTopLevelBind nclBinds
    asmFuncs <- CodeGen.runGen' $ traverse CodeGen.genFunc phtnFuncs
    let moduleStr = case modu of Module ms -> T.intercalate "." ms
        funcsSrc = T.intercalate "\n\n" $ AsmText.asmFuncText <$> asmFuncs
        objsSrc = fold $ phtnBinds <&> \ (name, funcName) ->
          let objname = "obj_" <> moduleStr <> "." <> name
          in T.unlines
            [ "global " <> objname
            , objname <> ":"
            , "\tdw FLAG_STATIC"
            , "\tdw OBJ_TYPE_THUNK_0"
            , "\tdd 1"
            , "\tdq " <> funcName
            , ""
            ]

    liftIO $ TIO.putStrLn $ "section .data\n\n" <> objsSrc <> "\nsection .text\n\n" <> funcsSrc <> "\n"

main :: IO ()
main = parseArgs >>= \ case
  Nothing -> pure ()
  Just cfg -> runTqc compilerMain cfg >>= \ case
    Left err -> print err
    Right () -> putStrLn "Compilation successful!"
