{-# LANGUAGE LambdaCase, OverloadedStrings #-}

module CodeGen.AsmText where

import Data.Text (Text)
import Data.Foldable
import qualified Data.Text as T
import CodeGen.Asm

regText32 :: Reg -> Text
regText32 = \case
  SP -> "esp"
  BP -> "ebp"
  AX -> "eax"
  BX -> "ebx"
  CX -> "ecx"
  DX -> "edx"
  SI -> "esi"
  DI -> "edi"
  R8 -> "r8d"
  R9 -> "r9d"
  R10 -> "r10d"
  R11 -> "r11d"
  R12 -> "r12d"
  R13 -> "r13d"
  R14 -> "r14d"
  R15 -> "r15d"

regText64 :: Reg -> Text
regText64 = \case
  SP -> "rsp"
  BP -> "rbp"
  AX -> "rax"
  BX -> "rbx"
  CX -> "rcx"
  DX -> "rdx"
  SI -> "rsi"
  DI -> "rdi"
  R8 -> "r8"
  R9 -> "r9"
  R10 -> "r10"
  R11 -> "r11"
  R12 -> "r12"
  R13 -> "r13"
  R14 -> "r14"
  R15 -> "r15"

data Size = Dword | Qword

asmLocText :: Size -> Loc -> Text
asmLocText s l = case (s, l) of
  (Dword, R r) -> regText32 r
  (Qword, R r) -> regText64 r
  (_, I x) -> T.pack (show x)
  (_, L x) -> x
  (_, HdrSizePlus x) -> "obj.hdr_size + " <> T.pack (show x)
  (_, Index r off) -> szAnn <> " [" <> regText64 r <> " + " <> T.pack (show off) <> "]"
  (_, IndexObj r off) ->
    let off' = case off of
          OType -> "obj.type"
          OSize -> "obj.size"
          OBody x -> "obj.body + " <> T.pack (show x)
    in szAnn <> " [" <> regText64 r <> " + " <> off' <> "]"
  where szAnn = case s of
          Dword -> "dword"
          Qword -> "qword"

asmInsnText :: Instruction -> Text
asmInsnText = \case
  Push l -> "push " <> asmLocText Qword l
  Pop l -> "pop " <> asmLocText Qword l
  Mov8 dst src -> "mov " <> asmLocText Qword dst <> ", " <> asmLocText Qword src
  Mov4 dst src -> "mov " <> asmLocText Dword dst <> ", " <> asmLocText Dword src
  Cmp x y -> "cmp " <> asmLocText Qword x <> ", " <> asmLocText Qword y
  Add r n -> "add " <> asmLocText Qword (R r) <> ", " <> T.pack (show n)
  Call l -> "call " <> asmLocText Qword l
  Je l -> "je " <> asmLocText Qword l
  Jmp l -> "jmp " <> asmLocText Qword l
  Label lbl -> lbl <> ":"
  Ret -> "ret"
  MacEval -> "eval"

asmFuncText :: AsmFunc -> Text
asmFuncText (AsmFunc name is) =
  name <> ":\n\t" <> T.intercalate "\n\t" (toList $ asmInsnText <$> is)
