module Common where

import Data.Text (Text)

data TqcPass
  = Parsed
  | Renamed
  | Typechecked
  deriving (Show, Eq)

newtype Module = Module [Text]
  deriving (Show, Ord, Eq)

data Qual = Qual Module Text
  deriving (Ord, Eq)

data RName
  = QualName Qual
  | LoclName LName
  deriving (Ord, Eq)

data LName
  = SrcName Text
  | GenName Text
  deriving (Ord, Eq)
