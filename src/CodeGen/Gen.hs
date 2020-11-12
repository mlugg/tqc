{-# LANGUAGE LambdaCase, OverloadedStrings, DeriveFunctor, TupleSections #-}

module CodeGen.Gen where

import Data.Int
import Data.Word
import PhtnSyn
import CodeGen.Asm
import Data.Foldable
import Data.Traversable
import Data.Sequence hiding (zip)
import qualified Data.Sequence as Seq (fromList)
import Tqc
import Numeric.Natural
import Control.Monad
import qualified Data.Text as T

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
-- rax: ptr to argument
-- rbx: ptr to function object
-- rcx: return val
-- rax-rdx are scratch registers

-- alloc takes input (size in bytes) in rcx and returns in rdx

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
          AllocFun _ entry -> [ Mov8 (IndexObj DX (OBody 0)) (L entry) ]
          _ -> []
    in pure $ Seq.fromList $
        [ Mov8 (R CX) (HdrSizePlus $ 8 * bodyLen)
        , Call (L "alloc")
        , Push (R DX)
        , Mov4 (IndexObj DX OType) objType
        , Mov4 (IndexObj DX OSize) (I bodyLen)
        , Mov8 (IndexObj DX OEval) (L eval)
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

  PObjSwitchLit field alts def -> do
    swId <- freshId
    let swId' = T.pack $ show swId
    let numberedAlts :: [(Natural, SwitchAlt)]
        numberedAlts = zip [0..] alts
        src0 = Seq.fromList
          [ Pop (R CX)
          , Mov8 (R DX) (IndexObj CX (OBody $ 8 * field))
          ]

    src1 <- fmap mconcat $ for numberedAlts $ \(n, SwitchAlt x _) -> do
      let lblName = ".sw" <> swId' <> "c" <> T.pack (show n)
      pure $ Seq.fromList $
        [ Cmp (R DX) (I x)
        , Je (L lblName)
        ]

    let src2 = Seq.fromList
          [ Jmp (L $ ".sw" <> swId' <> "d") ]

    src3 <- fmap mconcat $ for numberedAlts $ \(n, SwitchAlt _ src) -> do
      s <- genSrc src
      pure $ Label (".sw" <> swId' <> "c" <> T.pack (show n))
          <| (s |> Jmp (L $ ".sw" <> swId' <> "end"))

    let src4 = pure $
          Label $ ".sw" <> swId' <> "d"

    src5 <- genSrc def

    let src6 = pure $
          Label $ ".sw" <> swId' <> "end"

    pure $ mconcat
      [ src0, src1, src2, src3, src4, src5, src6 ]

  PEval -> pure $ Seq.fromList $
    [ Pop (R CX)
    , Push (R AX)
    , Push (R BX)
    , Mov8 (R AX) (R CX)
    , Call (IndexObj AX OEval)
    , Pop (R BX)
    , Pop (R AX)
    , Push (R CX)
    ]

  PPop n -> pure $ Seq.fromList $
    [ Add SP (n*8) ]

  PReplaceStack dst src -> pure $ Seq.fromList $
    [ Mov8 (R CX) (stackLoc src)
    , Mov8 (stackLoc dst) (R CX)
    ]

genSrc :: PhtnSrc -> Gen (Seq Instruction)
genSrc = fmap fold . traverse genSingle

genFunc :: PhtnFunc -> Gen AsmFunc
genFunc (PhtnFunc name src) = do
  code <- genSrc src
  pure $ AsmFunc name (hdr <> code <> ftr)
  where hdr = Seq.fromList
          [ Push (R BP)
          , Mov8 (R BP) (R SP)
          ]
        ftr = Seq.fromList
          [ Pop (R CX)
          , Pop (R BP)
          , Ret
          ]
