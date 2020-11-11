{-# LANGUAGE LambdaCase, OverloadedStrings, DeriveFunctor, TupleSections #-}

module CodeGen.Gen where

import Data.Int
import Data.Word
import PhtnSyn
import CodeGen.Asm
import Data.Foldable
import Data.Sequence
import qualified Data.Sequence as Seq (fromList)
import Tqc
import Numeric.Natural
import Control.Monad

-- Monad definition and operations {{{

newtype Gen a = Gen { runGen :: Natural -> Tqc (a, Natural) }
  deriving (Functor)

instance Applicative Gen where
  pure x = Gen $ \n -> pure (x, n)
  (<*>) = ap

instance Monad Gen where
  m >>= f = Gen $ \n0 -> do
    (x, n1) <- runGen m n0
    runGen (f x) n1

instance TqcMonad Gen where
  lift m = Gen $ \n -> (, n) <$> m

freshId :: Gen Natural
freshId = Gen $ \n -> pure (n, n+1)

-- }}}

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

genSingle :: PhtnInsn -> Gen (Seq Instruction)
genSingle = \case
  PPushArg -> pure $ Seq.fromList $
    [ Push (R AX) ]

  PPushClos n -> pure $ Seq.fromList $
    [ Push (IndexObj BX (OBody $ 8 * n + 8)) ]

  PPushStack loc -> pure $ Seq.fromList $
    [ Push (stackLoc loc) ]

  PAllocate info ->
    let (objType, bodyLen, eval) = case info of
          AllocFun closLen _ -> (L "OBJ_TYPE_FUN", closLen + 1, "eval_fun") -- one extra for entry code
          AllocData closLen -> (L "OBJ_TYPE_DATA", closLen + 1, "eval_data") -- one extra for constructor id
          AllocThunk -> (L "OBJ_TYPE_THUNK", 2, "eval_thunk")
          AllocInd -> (L "OBJ_TYPE_IND", 1, "eval_ind")

        extra = case info of
          AllocFun _ entry -> [ Mov8 (IndexObj CX (OBody 0)) (L entry) ]
          _ -> []
    in pure $ Seq.fromList $
        [ Mov8 (R CX) (HdrSizePlus $ 8 * bodyLen)
        , Push (R AX)
        , Call (L "alloc")
        , Pop (R AX)
        , Push (R CX)
        , Mov4 (IndexObj CX OType) objType
        , Mov4 (IndexObj CX OSize) (I bodyLen)
        , Mov8 (IndexObj CX OEval) (L eval)
        ] <> extra

  PObjSetPtr obj n val -> pure $ Seq.fromList $
    [ Mov8 (R CX) (stackLoc obj)
    , Mov8 (R DX) (stackLoc val)
    , Mov8 (IndexObj CX (OBody $ 8 * n)) (R DX)
    ]

  PObjSetLit obj n val -> pure $ Seq.fromList $
    [ Mov8 (R CX) (stackLoc obj)
    , Mov8 (IndexObj CX (OBody $ 8 * n)) (I val)
    ]

  PObjGetPtr obj n -> pure $ Seq.fromList $
    [ Mov8 (R CX) (stackLoc obj)
    , Push (IndexObj CX (OBody $ 8 * n))
    ]

  PObjSwitchLit obj n alts def -> _

  PPop n -> pure $ Seq.fromList $
    [ Add SP (n*8) ]

  PReplaceStack dst src -> pure $ Seq.fromList $
    [ Mov8 (R CX) (stackLoc src)
    , Mov8 (stackLoc dst) (R CX)
    ]

genFunc :: PhtnFunc -> Gen AsmFunc
genFunc (PhtnFunc name is) = do
  code <- fold <$> traverse genSingle is
  pure $ AsmFunc name (hdr <> code <> ftr)
  where hdr = Seq.fromList
          [ Push (R BP)
          , Mov8 (R BP) (R SP)
          ]
        ftr = Seq.fromList
          [ Mov8 (R CX) (Index SP 0)
          , Call (IndexObj CX OEval)
          , Pop (R AX)
          , Pop (R BP)
          , Ret
          ]
