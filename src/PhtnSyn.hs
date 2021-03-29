{-# LANGUAGE LambdaCase #-}

module PhtnSyn where

import Data.Word
import Data.Text (Text)
import Data.Sequence
import Data.Set (Set)
import qualified Data.Set as S

type PhtnSrc = Seq PhtnInsn

data PhtnInsn
  = PPushArg
  | PPushClos Word64 -- PPushBody offset
  | PPushStack StackPos
  | PPushGlobl Text
  | PAllocate AllocInfo -- PAllocate bodyLen type
  | PObjSetPtr StackPos Word64 StackPos -- PObjSetPtr obj field val
  | PObjSetLit StackPos Word64 Word64 -- PObjSetLit obj field val
  | PObjGetPtr StackPos Word64 -- PObjGetPtr obj field
  | PObjSwitchLit Word64 [SwitchAlt] PhtnSrc -- PObjSwitchLit obj field alts def
  | PEval -- evals tos, pushing new ptr
  | PPop Word64
  | PReplaceStack StackPos StackPos -- PReplaceStack dst src
  deriving (Show)

data PhtnFunc = PhtnFunc Text PhtnSrc
  deriving (Show)

data SwitchAlt = SwitchAlt Word64 PhtnSrc
  deriving (Show)

data AllocInfo
  = AllocFun Word64 Text -- closure len, entry code
  | AllocData Word64 -- closure len
  | AllocThunk0 Word64 Text -- closure len, entry code
  | AllocThunk1
  deriving (Show)

data StackPos
  = TopOff Word64
  | BottomOff Word64
  deriving (Show)

getPhtnGlobalRefs :: PhtnFunc -> Set Text
getPhtnGlobalRefs (PhtnFunc _ is) = foldMap go is where
  go = \ case
    PPushGlobl x -> S.singleton x
    PObjSwitchLit _ alts def -> foldMap go def <> foldMap goAlt alts
    _            -> mempty
  goAlt (SwitchAlt _ is') = foldMap go is'
