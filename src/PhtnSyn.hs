module PhtnSyn where

import Data.Word
import Data.Text (Text)

data PhtnInsn
  = FPushArg
  | FPushBody  Word64 -- FPushBody offset
  | FPushStack Word64 -- FPushStack offset
  | FAllocate  AllocInfo -- FAllocate bodyLen type
  | FObjSetPtr StackPos Word64 StackPos -- FObjSetPtr obj field val
  | FObjSetLit StackPos Word64 Word64 -- FObjSetLit obj field val
  | FPop Word64
  | FReplaceStack StackPos StackPos -- FReplaceStack dst src
  deriving (Show)

data PhtnFunc = PhtnFunc Text [PhtnInsn]
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

