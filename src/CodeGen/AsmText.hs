{-# LANGUAGE LambdaCase, OverloadedStrings #-}

module CodeGen.AsmText where

import Data.Text (Text)
import Data.Foldable
import qualified Data.Text as T
import CodeGen.Asm

asmRegText :: Reg -> Text
asmRegText = \case
  SP -> "sp"
  BP -> "bp"
  AX -> "ax"
  BX -> "bx"
  CX -> "cx"
  DX -> "dx"

data Size = Dword | Qword

asmLocText :: Size -> Loc -> Text
asmLocText s l = case (s, l) of
  (Dword, R r) -> "e" <> asmRegText r
  (Qword, R r) -> "r" <> asmRegText r
  (_, I x) -> T.pack (show x)
  (_, L x) -> x
  (_, HdrSizePlus x) -> "obj.hdr_size + " <> T.pack (show x)
  (_, Index r off) -> szAnn <> " [r" <> asmRegText r <> " + " <> T.pack (show off) <> "]"
  (_, IndexObj r off) ->
    let off' = case off of
          OType -> "obj.type"
          OSize -> "obj.size"
          OEval -> "obj.eval"
          OBody x -> "obj.body + " <> T.pack (show x)
    in szAnn <> " [r" <> asmRegText r <> " + " <> off' <> "]"
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

asmFuncText :: AsmFunc -> Text
asmFuncText (AsmFunc name is) =
  name <> ":\n  " <> T.intercalate "\n  " (toList $ asmInsnText <$> is)
