module CodeGen.Asm where

import Data.Text (Text)
import Data.Word
import Data.Int
import Data.Sequence

data Reg = SP | BP | AX | BX | CX | DX | SI | DI | R8 | R9 | R10 | R11 | R12 | R13 | R14 | R15
  deriving (Show)

data ObjOff
  = OType
  | OSize
  | OBody Word64
  deriving (Show)

data Loc
  = R Reg
  | I Word64
  | L Text
  | HdrSizePlus Word64
  | Index Reg Int64
  | IndexObj Reg ObjOff
  deriving (Show)

data Instruction
  = Push Loc
  | Pop Loc
  | Mov8 Loc Loc
  | Mov4 Loc Loc
  | Cmp Loc Loc
  | Add Reg Word64
  | Call Loc
  | Je Loc
  | Jmp Loc
  | Label Text
  | Ret
  -- Macros
  | MacEval
  deriving (Show)

data AsmFunc = AsmFunc Text (Seq Instruction)
  deriving (Show)
