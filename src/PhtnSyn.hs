module PhtnSyn where

import Data.Word
import Data.Text (Text)
import Data.Sequence

type PhtnSrc = Seq PhtnInsn

data PhtnInsn
  = PPushArg
  | PPushClos Word64 -- PPushBody offset
  | PPushStack StackPos
  | PAllocate  AllocInfo -- PAllocate bodyLen type
  | PObjSetPtr StackPos Word64 StackPos -- PObjSetPtr obj field val
  | PObjSetLit StackPos Word64 Word64 -- PObjSetLit obj field val
  | PObjGetPtr StackPos Word64 -- PObjGetPtr obj field
  | PObjSwitchLit StackPos Word64 [SwitchAlt] PhtnSrc -- PObjSwitchLit obj field alts def
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
  | AllocThunk
  | AllocInd
  deriving (Show)

data StackPos
  = TopOff Word64
  | BottomOff Word64
  deriving (Show)
