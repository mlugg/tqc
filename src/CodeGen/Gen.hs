{-# LANGUAGE LambdaCase, OverloadedStrings #-}

module CodeGen.Gen where

import Data.Int
import Data.Word
import PhtnSyn
import CodeGen.Asm
import Data.Foldable

-- rbp: base ptr
-- rsp: stack ptr
-- rax: ptr to argument or return val
-- rbx: ptr to function object
-- rcx, rdx: intermediate registers

-- alloc takes input (allocation size in 8-byte words) in rcx and
-- returns in rcx

intWord :: Word64 -> Int64
intWord = fromIntegral

stackLoc :: StackPos -> Loc
stackLoc = \case
  TopOff off -> Index SP (8 * intWord off)
  BottomOff off -> Index BP (8 * (- intWord off - 1))

genSingle :: PhtnInsn -> [Instruction]
genSingle = \case
  PPushArg ->
    [ Push $ R AX ]

  PPushClos n ->
    [ Push $ IndexObj BX (OBody $ 8 * n + 8) ]

  PPushStack loc ->
    [ Push $ stackLoc loc ]

  PAllocate info ->
    let (objType, bodyLen, eval) = case info of
          AllocFun closLen _ -> (L "OBJ_TYPE_FUN", closLen + 1, "eval_fun") -- one extra for entry code
          AllocData closLen -> (L "OBJ_TYPE_DATA", closLen + 1, "eval_data") -- one extra for constructor id
          AllocThunk -> (L "OBJ_TYPE_THUNK", 2, "eval_thunk")
          AllocInd -> (L "OBJ_TYPE_IND", 1, "eval_ind")

        extra = case info of
          AllocFun _ entry -> [ Mov8 (IndexObj CX (OBody 0)) (L entry) ]
          _ -> []
    in
      [ Mov8 (R CX) (HdrSizePlus $ 8 * bodyLen)
      , Push (R AX)
      , Call (L "alloc")
      , Pop (R AX)
      , Push (R CX)
      , Mov4 (IndexObj CX OType) objType
      , Mov4 (IndexObj CX OSize) (I bodyLen)
      , Mov8 (IndexObj CX OEval) (L eval)
      ] <> extra

  PObjSetPtr obj n val ->
    [ Mov8 (R CX) (stackLoc obj)
    , Mov8 (R DX) (stackLoc val)
    , Mov8 (IndexObj CX (OBody $ 8 * n)) (R DX)
    ]

  PObjSetLit obj n val ->
    [ Mov8 (R CX) (stackLoc obj)
    , Mov8 (IndexObj CX (OBody $ 8 * n)) (I val)
    ]

  PObjGetPtr obj n ->
    [ Mov8 (R CX) (stackLoc obj)
    , Push (IndexObj CX (OBody $ 8 * n))
    ]

  PObjSwitchLit obj n alts def -> _

  PPop n ->
    [ Add SP (n*8) ]

  PReplaceStack dst src ->
    [ Mov8 (R CX) (stackLoc src)
    , Mov8 (stackLoc dst) (R CX)
    ]

genFunc :: PhtnFunc -> AsmFunc
genFunc (PhtnFunc name is) = AsmFunc name $ mconcat [hdr, toList is >>= genSingle, ftr]
  where hdr =
          [ Push (R BP)
          , Mov8 (R BP) (R SP)
          ]
        ftr =
          [ Mov8 (R CX) (Index SP 0)
          , Call (IndexObj CX OEval)
          , Pop (R AX)
          , Pop (R BP)
          , Ret
          ]
