{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}

module Cli (parseArgs) where

import Data.Functor
import Data.Unique
import Data.Maybe
import Data.Traversable
import System.Environment
import System.Console.GetOpt
import Text.Read
import Tqc
import Data.Foldable

data Option
  = OptAsmOut
  | OptObjOut
  | OptStatic
  | OptShared
  | OptOptimisation (Maybe Int)
  | OptOutfile String
  deriving (Eq)

getIncompatibleOptionErrs :: [Option] -> [String]
getIncompatibleOptionErrs opts = mconcat
  [ if OptAsmOut `elem` opts && OptObjOut `elem` opts then ["-S and -c cannot be used together"] else []
  , if OptStatic `elem` opts && OptShared `elem` opts then ["--static and --shared cannot be used together"] else []
  ]

optDescrs :: [OptDescr Option]
optDescrs =
  [ Option ['S'] [] (NoArg OptAsmOut) "Compile, but do not assemble."
  , Option ['c'] [] (NoArg OptObjOut) "Compile and assemble, but do not link."
  , Option [] ["static"] (NoArg OptStatic) "Use static linkage for the resulting binary."
  , Option [] ["shared"] (NoArg OptShared) "Use shared linkage for the resulting binary."
  , Option ['O'] [] (ReqArg (OptOptimisation . readMaybe) "0-9") "Set the optimisation level for compilation."
  , Option ['o'] [] (ReqArg OptOutfile "filename") "Set the output filename."
  ]

parseArgs :: IO (Maybe TqcConfig)
parseArgs = do
  as <- getArgs
  let (opts, inFiles, errs) = getOpt Permute optDescrs as

  let errs' = errs <> getIncompatibleOptionErrs opts

  if not $ null errs'
  then do
    traverse_ putStrLn errs'
    putStrLn $ usageInfo "Usage:" optDescrs
    pure Nothing
  else do
    let optlevel = foldr (\ case { OptOptimisation (Just x) -> const $ Just x; _ -> id }) Nothing opts
        shared = any (== OptShared) opts
        doObj = all (/= OptAsmOut) opts
        doBin = all (`notElem` [OptAsmOut, OptObjOut]) opts
        outfile = foldr (\ case { OptOutfile x -> const $ Just x; _ -> id }) Nothing opts

        mkState = TqcConfig shared (fromMaybe 3 optlevel)

    if
      | doBin -> do -- Outputting a binary
          files <- for inFiles $ \ src -> do
            asm <- createTmpFilepath "asm"
            obj <- createTmpFilepath "o"
            pure $ QuantaFile src asm (Just obj)
          let outfile' = fromMaybe archDefaultBinaryFile outfile
          pure $ Just $ mkState files (Just outfile')

      | [src] <- inFiles, doObj -> do -- One input file, outputting object files
          asm <- createTmpFilepath "asm"
          let outfile' = fromMaybe "out.o" outfile
          pure $ Just $ mkState [QuantaFile src asm (Just outfile')] Nothing

      | [src] <- inFiles -> do -- One input file, outputting asm files
          let outfile' = fromMaybe "out.asm" outfile
          pure $ Just $ mkState [QuantaFile src outfile' Nothing] Nothing

      | doObj -> do -- Multiple input files, outputting object files
          files <- for inFiles $ \ src -> do
            asm <- createTmpFilepath "asm"
            let obj = src <> "." <> fromMaybe "o" outfile
            pure $ QuantaFile src asm (Just obj)
          pure $ Just $ mkState files Nothing

      | otherwise -> do -- Multiple input files, outputting asm files
          let files = inFiles <&> \ src ->
                let asm = src <> "." <> fromMaybe "asm" outfile
                in QuantaFile src asm Nothing

          pure $ Just $ mkState files Nothing
          
createTmpFilepath :: String -> IO FilePath
createTmpFilepath ext = do
  unique <- newUnique <&> hashUnique <&> show
  pure $ archTempDirectory <> "/tqc_tmp_" <> unique <> "." <> ext

archDefaultBinaryFile, archTempDirectory :: String
archDefaultBinaryFile = "a.out"
archTempDirectory = "/tmp"
