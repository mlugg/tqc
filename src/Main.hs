{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}

module Main where

import Cli
import Tqc
import PhtnSyn
import Rename
import QntSyn
import Tc
import Common
import qualified QntToNcl
import qualified NclToPhtn
import qualified CodeGen.Gen as CodeGen
import qualified CodeGen.AsmText as AsmText
import qualified QntSyn.Parse
import QntSyn.Pretty

import qualified Data.Text.IO as TIO
import Text.Megaparsec (parse, errorBundlePretty, sourcePosPretty)
import qualified Data.Map as M
import qualified Data.Text as T
import qualified Data.Set as S
import Data.Functor
import Data.Traversable
import Data.Foldable
import Control.Monad.IO.Class
import System.Process
import System.Exit
import Data.Maybe
import Data.Text (Text)
import Data.Proxy

data ModuleInfo p = ModuleInfo FilePath Module [DataDecl p] [QntBind p]

tNat :: Type Qual
tNat = TName $ Qual (Module ["Data", "Nat"]) "Nat"

builtinKindEnv :: KindEnv
builtinKindEnv = M.fromList
  [ (Qual (Module []) "->", KStar `KArrow` KStar `KArrow` KStar)
  , (Qual (Module ["Data", "Nat"]) "Nat", KStar)
  ]

builtinTypeEnv :: TypeEnv
builtinTypeEnv = M.fromList
  [ (QualName $ Qual (Module []) "error", Scheme (S.singleton "a") (TName $ Qual (Module []) "a"))
  , (QualName $ Qual (Module ["Data", "Nat"]) "+", Scheme mempty (tNat `tArrow` tNat `tArrow` tNat))
  , (QualName $ Qual (Module ["Data", "Nat"]) "-", Scheme mempty (tNat `tArrow` tNat `tArrow` tNat))
  , (QualName $ Qual (Module ["Data", "Nat"]) "*", Scheme mempty (tNat `tArrow` tNat `tArrow` tNat))
  , (QualName $ Qual (Module ["Data", "Nat"]) "/", Scheme mempty (tNat `tArrow` tNat `tArrow` tNat))
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

wrapErrorFile :: FilePath -> Tqc a -> Tqc a
wrapErrorFile f m = tqcCatchErr m $ throwErr . InFile f

compilerMain :: Tqc ()
compilerMain = do
  cfg <- askConf

  infosParsed <- for (tqcFiles cfg) $ \ file -> do
    src <- liftIO $ TIO.readFile (qntSrcName file)
    case parse QntSyn.Parse.file (qntSrcName file) src of
      Left err -> throwErr $ ParseErr err
      Right (QntProg datas binds) -> do
        let modu = Module $ T.split (`elem` ['/', '\\']) $ T.pack $ qntSrcName file
        pure $ ModuleInfo (qntSrcName file) modu datas binds

  let allVars = do
        ModuleInfo _ modu datas binds <- infosParsed

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
        ModuleInfo _ modu datas _ <- infosParsed
        DataDecl name _ _ <- datas
        pure $ Qual modu name

      allTypes' = builtinTypes <> allTypes

  infosRenamed <- for infosParsed $ \ (ModuleInfo filePath modu datas binds) ->
    wrapErrorFile filePath $
      runRename' allVars' allTypes' $ do
        datas' <- traverse renameData datas
        binds' <- traverse renameBind binds
        pure $ ModuleInfo filePath modu datas' binds'


  let typeEnv = fold $ do
        ModuleInfo _ modu datas binds <- infosRenamed

        let constrsEnv = do
              DataDecl typeName params constrs <- datas
              let paramNames = params <&> \ (TyParam n _) -> n
              let typeOut = foldl TApp (TName $ Qual modu typeName) (TName . Qual (Module []) <$> paramNames)
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
        ModuleInfo _ modu datas _ <- infosRenamed
        DataDecl name params _ <- datas
        let dataKind = foldr (\ (TyParam _ paramKind) k -> paramKind `KArrow` k) KStar params
        pure $ M.singleton (Qual modu name) dataKind

      kindEnv' = builtinKindEnv <> kindEnv

      constrEnv = fold $ do
        ModuleInfo _ modu datas _ <- infosRenamed
        DataDecl typeName params constrs <- datas
        let paramNames = params <&> \ (TyParam n _) -> n
        let typeOut = foldr TApp (TName $ Qual modu typeName) (TName . Qual (Module []) <$> paramNames)
        DataConstr name args <- constrs
        pure $ M.singleton (Qual modu name) (S.fromList paramNames, typeOut, args)

      constrEnv' = builtinConstrEnv <> constrEnv

      constrIds = fold $ do
        ModuleInfo _ modu datas _ <- infosRenamed
        DataDecl _ _ constrs <- datas
        let f (DataConstr name _) x = (Qual modu name, x)
        pure $ M.fromList $ zipWith f constrs [0..]

  infosTypechecked <- for infosRenamed $ \ (ModuleInfo filePath modu datas binds) ->
    wrapErrorFile filePath $ do
      (info, _) <- runInfer' typeEnv' kindEnv' constrEnv' $ do
        datas' <- traverse checkDataConstrs datas
        (_, binds') <- inferTopLevelBinds modu binds
        pure $ ModuleInfo filePath modu datas' binds'
      pure info

  for_ (zip infosTypechecked (tqcFiles cfg)) $ \ (ModuleInfo filePath modu datas binds, QuantaFile _ asmOutFile objOutFile) ->
    wrapErrorFile filePath $ do
      -- Note that the free variables of these binds are meaningless, as
      -- they are top-level
      nclBinds <- QntToNcl.runConvert' $ traverse QntToNcl.convertBind binds

      (phtnBinds, phtnFuncs) <- NclToPhtn.runCompile' constrIds $ do
        normalBinds <- traverse NclToPhtn.compileTopLevelBind nclBinds
        constrBinds <- fmap fold $
          for datas $ \ (DataDecl _ _ constrs) ->
            for constrs $ \ (DataConstr name as) ->
              NclToPhtn.compileConstrFunction (Qual modu name) (length as)
        pure $ normalBinds <> constrBinds

      asmFuncs <- CodeGen.runGen' $ traverse CodeGen.genFunc phtnFuncs

      let localNames = phtnBinds <&> \ (name, _) -> qualToAsmName (Qual modu name)
          externNames = foldMap getPhtnGlobalRefs phtnFuncs S.\\ S.fromList localNames

          externsSrc = foldMap (\ n -> "extern " <> n <> "\n") externNames

          funcsSrc = T.intercalate "\n\n" $ AsmText.asmFuncText <$> asmFuncs

          objsSrc = fold $ phtnBinds <&> \ (name, funcName) ->
            let objname = qualToAsmName (Qual modu name)
                extra = if name /= "main" then "" else "global obj_main\nobj_main:\n"
            in T.unlines
              [ "global " <> objname
              , extra <> objname <> ":"
              , "\tdw FLAG_STATIC"
              , "\tdw OBJ_TYPE_THUNK_0"
              , "\tdd 1"
              , "\tdq " <> funcName
              , ""
              ]

          fullSrc = T.unlines
            [ "%include \"asm/runtime.inc\""
            , ""
            , externsSrc
            , "section .data"
            , ""
            , objsSrc
            , "section .text"
            , ""
            , funcsSrc
            ]

      liftIO $ TIO.writeFile asmOutFile fullSrc
      liftIO $ putStrLn $ "Wrote " <> asmOutFile

      case objOutFile of
        Nothing -> pure ()
        Just objOutFile' -> do
          liftIO (rawSystem "nasm" ["-f", "elf64", asmOutFile, "-o", objOutFile']) >>= \ case
            ExitFailure _ -> throwErr $ NasmErr objOutFile'
            ExitSuccess -> liftIO $ putStrLn $ "Wrote " <> objOutFile'

  case tqcBinaryFile cfg of
    Nothing -> pure ()
    Just binOutFile -> do
      let objFiles = catMaybes $ (\ (QuantaFile _ _ objOutFile) -> objOutFile) <$> tqcFiles cfg
          runtimeLink = if tqcShared cfg then ["-L.", "-ltqc"] else ["libtqc.a"]
      liftIO (rawSystem "ld" (objFiles <> runtimeLink <> ["-o", binOutFile])) >>= \ case
        ExitFailure _ -> throwErr $ LinkErr binOutFile
        ExitSuccess -> liftIO $ putStrLn $ "Wrote " <> binOutFile

printError :: CompileError -> Text
printError = \ case
  NumRangeErr -> "numeric literal out of range (0 to 2^64 - 1)"
  TypeErr err -> printTypeError err
  UnknownVarErr x -> "unknown identifier '" <> x <> "'"
  UnknownTypeErr x -> "unknown type name '" <> x <> "'"
  AmbiguousNameErr x ys -> "name '" <> x <> "' is ambiguous; it may refer to any of " <> T.intercalate "," (psPrintId p . QualName <$> ys)
  ParseErr err -> T.pack $ errorBundlePretty err
  NasmErr path -> "nasm error while assembling " <> T.pack path
  LinkErr path -> "linker error while linking " <> T.pack path
  InFile path err -> "in file " <> T.pack path <> ":\n" <> printError err
  where p :: Proxy 'Renamed
        p = Proxy

printTypeError :: TypeError -> Text
printTypeError = \ case
  TeInExpr (L ss e) te -> "in " <> printExprType e <> " (" <> printSpan ss <> ")\n" <> printTypeError te
  TeInScheme (L ss s) te -> "in the type scheme '" <> pPrintScheme p s <> "' (" <> printSpan ss <> ")\n" <> printTypeError te
  TeSchemeMismatch s1 s2 -> "type schemes '" <> pPrintScheme p s1 <> "' and '" <> pPrintScheme p s2 <> "' do not match"
  TeTypeMismatch t0 t1 -> "cannot match type '" <> pPrintType p t0 <> "' with '" <> pPrintType p t1 <> "'"
  TeInfiniteType t0 t1 -> "cannot construct the infinite type '" <> pPrintType p t0 <> " ~ " <> pPrintType p t1 <> "'"
  TeKindNotStar -> "expected a type but got an unapplied type constructor"
  TeBadTypeApp t0 k0 t1 k1 -> "kind mismatch in type application: cannot apply type '" <> pPrintType p t1 <> " :: " <> pPrintKind k1 <> "' to '" <> pPrintType p t0 <> " :: " <> pPrintKind k0 <> "'"
  TeUnknownVar n -> "unknown identifier '" <> psPrintId p n <> "'"
  TeUnknownType n -> "unknown type name '" <> psPrintTyId p n <> "'"
  TeBadPatternArgs q n m -> "bad pattern match for constructor '" <> psPrintId p (QualName q) <> "': expected " <> T.pack (show n) <> " args but got " <> T.pack (show m)
  where p :: Proxy 'Renamed
        p = Proxy

printExprType :: QntExpr 'Renamed -> Text
printExprType = \ case
  QntVar _ -> "identifer"
  QntNatLit _ -> "numeric literal"
  QntApp _ _ -> "function application"
  QntLam _ _ -> "lambda abstraction"
  QntLet _ _ -> "let expression"
  QntCase _ _ -> "case statement"

printSpan :: SrcSpan -> Text
printSpan (SrcSpan start end) = T.pack (sourcePosPretty start) <> " - " <> T.pack (sourcePosPretty end)

main :: IO ()
main = parseArgs >>= \ case
  Nothing -> pure ()
  Just cfg -> runTqc compilerMain cfg >>= \ case
    Left err -> TIO.putStrLn $ printError err
    Right () -> putStrLn "Compilation successful!"
