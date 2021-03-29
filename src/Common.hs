{-# LANGUAGE OverloadedStrings #-}

module Common where

import Data.Text (Text)
import qualified Data.Text as T
import Data.Char
import Numeric

data TqcPass
  = Parsed
  | Renamed
  | Typechecked
  deriving (Show, Eq)

newtype Module = Module [Text]
  deriving (Show, Ord, Eq)

data Qual = Qual Module Text
  deriving (Ord, Eq, Show)

data RName
  = QualName Qual
  | LoclName LName
  deriving (Ord, Eq, Show)

data LName
  = SrcName Text
  | GenName Text
  deriving (Ord, Eq, Show)

qualToAsmName :: Qual -> Text
qualToAsmName (Qual (Module ms) x)
  | null ms = "obj_" <> x'
  | otherwise = "obj_" <> T.intercalate "." ms <> "." <> x'
  where x' = foldMap goChar $ T.unpack x
        goChar c
          | c >= 'A' && c <= 'Z' = T.singleton c
          | c >= 'a' && c <= 'z' = T.singleton c
          | c >= '0' && c <= '9' = T.singleton c
          | otherwise = T.cons '#' $ T.justifyRight 6 '0' $ T.pack $ showHex (ord c) ""
