{-|
Copyright  :  (C) 2021-2022, QBayLogic B.V.,
                  2022     , Google Inc.,
License    :  BSD2 (see the file LICENSE)
Maintainer :  QBayLogic B.V. <devops@qbaylogic.com>
-}

module Floating where

import Clash.Prelude
import qualified Clash.Explicit.Prelude as CEP
import Clash.Explicit.Testbench

import qualified Prelude as P
import Numeric (showHex)

import qualified Clash.Cores.Xilinx.Floating as F

import Floating.Annotations
import Floating.TH

newtype FloatVerifier = FloatVerifier Float

instance Eq FloatVerifier where
  (FloatVerifier x) == (FloatVerifier y) = pack x == pack y

instance ShowX FloatVerifier where
  showsPrecX = showsPrecXWith showsPrec

instance Show FloatVerifier where
  showsPrec = floatVerifierShowsPrec

floatVerifierShowsPrec
  :: Int
  -> FloatVerifier
  -> ShowS
floatVerifierShowsPrec _ (FloatVerifier x)
  | isNaN x = nanSign . nanString . showHex payload . (')':)
  | otherwise = shows x
 where
  nanSign | msb (pack x) == 0 = ('+':)
          | otherwise         = ('-':)
  nanString
    | testBit (pack x) 22 = ("qNaN(0x" P.++)
    | otherwise           = ("sNaN(0x" P.++)
  payload = truncateB $ pack x :: BitVector 22

playSampleRom
  :: forall n a dom
   . ( KnownDomain dom
     , KnownNat n
     , BitPack a
     , 1 <= n
     )
  => Clock dom
  -> Reset dom
  -> MemBlob n (BitSize a)
  -> (Signal dom Bool, Signal dom a)
playSampleRom clk rst content = (done, out)
 where
  out = unpack . asyncRomBlob content <$> cnt
  done = CEP.register clk rst enableGen False $ (== maxBound) <$> cnt
  cnt :: Signal dom (Index n)
  cnt = CEP.register clk rst enableGen 0 $ satSucc SatBound <$> cnt

basicBinaryTB
  :: forall n d
   . ( KnownNat n
     , KnownNat d
     , 1 <= n
     )
  => (   Clock XilinxSystem
      -> DSignal XilinxSystem 0 Float
      -> DSignal XilinxSystem 0 Float
      -> DSignal XilinxSystem d Float
     )
  -> Vec n (Float, Float, Float)
  -> Signal XilinxSystem Bool
basicBinaryTB comp samples = done
 where
  (inputX, inputY, expectedOutput) = unzip3 samples
  testInputX = fromSignal $ stimuliGenerator clk rst inputX
  testInputY = fromSignal $ stimuliGenerator clk rst inputY
  expectOutput = outputVerifier' clk rst (repeat @d 0 ++ expectedOutput)
  done =
      expectOutput . ignoreFor clk rst en (SNat @d) 0
    . toSignal $ comp clk testInputX testInputY
  clk = tbClockGen (not <$> done)
  rst = resetGen
  en = enableGen
{-# INLINE basicBinaryTB #-}

basicRomTB
  :: forall d n
   . ( KnownNat n
     , KnownNat d
     , 1 <= n
     )
  => (   Clock XilinxSystem
      -> DSignal XilinxSystem 0 Float
      -> DSignal XilinxSystem 0 Float
      -> DSignal XilinxSystem d Float
     )
  -> MemBlob n (BitSize (Float, Float, Float))
  -> Signal XilinxSystem Bool
basicRomTB comp sampleBlob = done
 where
  (done0, samples) = playSampleRom clk rst sampleBlob
  (inputX, inputY, expectedOutput) = unbundle samples
  -- Only assert while not finished
  done = mux done0 done0
    $ assert clk rst "basicRomTB" out (fmap FloatVerifier expectedOutput)
             done0
  out =
      fmap FloatVerifier . ignoreFor clk rst en (SNat @d) 0
    . toSignal $ comp clk (fromSignal inputX) (fromSignal inputY)
  clk = tbClockGen (not <$> done)
  rst = resetGen
  en = enableGen
{-# INLINE basicRomTB #-}

addBasic
  :: Clock XilinxSystem
  -> DSignal XilinxSystem 0 Float
  -> DSignal XilinxSystem 0 Float
  -> DSignal XilinxSystem F.AddDefDelay Float
addBasic clk x y = withClock clk $ withEnable enableGen $ F.add x y
{-# NOINLINE addBasic #-}
{-# ANN addBasic (binaryTopAnn "addBasic") #-}

addBasicTB :: Signal XilinxSystem Bool
addBasicTB = basicRomTB addBasic $(memBlobTH Nothing addBasicSamples)
{-# ANN addBasicTB (TestBench 'addBasic) #-}

addEnable
  :: Clock XilinxSystem
  -> Enable XilinxSystem
  -> DSignal XilinxSystem 0 Float
  -> DSignal XilinxSystem 0 Float
  -> DSignal XilinxSystem 11 Float
addEnable clk en x y = withClock clk $ withEnable en $ F.add x y
{-# NOINLINE addEnable #-}
{-# ANN addEnable (binaryEnTopAnn "addEnable") #-}

addEnableTB :: Signal XilinxSystem Bool
addEnableTB = done
 where
  testInput =
    fromSignal $ stimuliGenerator clk rst $(listToVecTH [1 :: Float .. 25])
  en =
    toEnable $ stimuliGenerator clk rst
        (   (replicate d11 True ++ replicate d4 True ++ replicate d4 False)
         :< True)
  expectedOutput =
       replicate d11 0
    ++ $(listToVecTH . P.map (\i -> i + i) $
                [1 :: Float .. 4]
           -- Stall for four cycles
           P.++ P.replicate 4 5
           -- Still in the pipeline (11 deep) from before the stall.
           P.++ P.take 11 [5 .. 25]
           -- We "lose" four samples of what remains due to not being enabled
           -- for those inputs.
           P.++ P.drop 4 (P.drop 11 [5 .. 25])
        )
  expectOutput =
    outputVerifier' clk rst expectedOutput
  done =
      expectOutput . ignoreFor clk rst enableGen d11 0
    . toSignal $ addEnable clk en testInput testInput
  clk = tbClockGen (not <$> done)
  rst = resetGen
{-# ANN addEnableTB (TestBench 'addEnable) #-}

addShortPL
  :: Clock XilinxSystem
  -> DSignal XilinxSystem 0 Float
  -> DSignal XilinxSystem 0 Float
  -> DSignal XilinxSystem 6 Float
addShortPL clk x y =
  withClock clk $ withEnable enableGen $ F.addWith F.defConfig x y
{-# NOINLINE addShortPL #-}
{-# ANN addShortPL (binaryTopAnn "addShortPL") #-}

addShortPLTB :: Signal XilinxSystem Bool
addShortPLTB =
  basicBinaryTB addShortPL
    $(listToVecTH [ (1, 4, 5) :: (Float, Float, Float)
                  , (2, 5, 7)
                  , (3, 6, 9)
                  ])
{-# ANN addShortPLTB (TestBench 'addShortPL) #-}

subBasic
  :: Clock XilinxSystem
  -> DSignal XilinxSystem 0 Float
  -> DSignal XilinxSystem 0 Float
  -> DSignal XilinxSystem F.SubDefDelay Float
subBasic clk x y = withClock clk $ withEnable enableGen $ F.sub x y
{-# NOINLINE subBasic #-}
{-# ANN subBasic (binaryTopAnn "subBasic") #-}

subBasicTB :: Signal XilinxSystem Bool
subBasicTB = basicRomTB subBasic $(memBlobTH Nothing subBasicSamples)
{-# ANN subBasicTB (TestBench 'subBasic) #-}

mulBasic
  :: Clock XilinxSystem
  -> DSignal XilinxSystem 0 Float
  -> DSignal XilinxSystem 0 Float
  -> DSignal XilinxSystem F.MulDefDelay Float
mulBasic clk x y = withClock clk $ withEnable enableGen $ F.mul x y
{-# NOINLINE mulBasic #-}
{-# ANN mulBasic (binaryTopAnn "mulBasic") #-}

mulBasicTB :: Signal XilinxSystem Bool
mulBasicTB = basicRomTB mulBasic $(memBlobTH Nothing mulBasicSamples)
{-# ANN mulBasicTB (TestBench 'mulBasic) #-}

divBasic
  :: Clock XilinxSystem
  -> DSignal XilinxSystem 0 Float
  -> DSignal XilinxSystem 0 Float
  -> DSignal XilinxSystem F.DivDefDelay Float
divBasic clk x y = withClock clk $ withEnable enableGen $ F.div x y
{-# NOINLINE divBasic #-}
{-# ANN divBasic (binaryTopAnn "divBasic") #-}

divBasicTB :: Signal XilinxSystem Bool
divBasicTB = basicRomTB divBasic $(memBlobTH Nothing divBasicSamples)
{-# ANN divBasicTB (TestBench 'divBasic) #-}

fromUBasic
  :: Clock XilinxSystem
  -> DSignal XilinxSystem 0 (Unsigned 32)
  -> DSignal XilinxSystem F.FromU32DefDelay Float
fromUBasic clk x = withClock clk $ withEnable enableGen $ F.fromU32 x
{-# NOINLINE fromUBasic #-}
{-# ANN fromUBasic (unaryTopAnn "fromUBasic") #-}

fromUBasicTB :: Signal XilinxSystem Bool
fromUBasicTB = done
 where
  (done0, samples) =
    playSampleRom clk rst $(memBlobTH Nothing fromUBasicSamples)
  (input, expectedOutput) = unbundle samples
  -- Only assert while not finished
  done = mux done0 done0 $
    assert clk rst "fromUBasicTB" out expectedOutput done0
  out = ignoreFor clk rst en (SNat @F.FromU32DefDelay) 0 . toSignal .
    fromUBasic clk $ fromSignal input
  clk = tbClockGen (not <$> done)
  rst = resetGen
  en = enableGen
{-# ANN fromUBasicTB (TestBench 'fromUBasic) #-}

fromUEnable
  :: Clock XilinxSystem
  -> Enable XilinxSystem
  -> DSignal XilinxSystem 0 (Unsigned 32)
  -> DSignal XilinxSystem 5 Float
fromUEnable clk en x = withClock clk $ withEnable en $ F.fromU32 x
{-# NOINLINE fromUEnable #-}
{-# ANN fromUEnable (unaryEnTopAnn "fromUEnable") #-}

fromUEnableTB :: Signal XilinxSystem Bool
fromUEnableTB = done
 where
  testInput = fromSignal $
    stimuliGenerator clk rst $(listToVecTH [1 :: Unsigned 32 .. 20])
  en = toEnable $ stimuliGenerator clk rst
        ((replicate d5 True ++ replicate d4 True ++ replicate d4 False) :< True)
  expectedOutput = replicate d5 0 ++
    $(listToVecTH $
         [1 :: Float .. 4]
      -- Stall for four cycles
      <> P.replicate 4 5
      -- Still in the pipeline (5 deep) from before the stall.
      <> P.take 5 [5 .. 20]
      -- We "lose" four samples of what remains due to not being enabled
      -- for those inputs.
      <> P.drop 4 (P.drop 5 [5 .. 20])
    )
  expectOutput = outputVerifier' clk rst expectedOutput
  done = expectOutput . ignoreFor clk rst enableGen d5 0 . toSignal $
    fromUEnable clk en testInput
  clk = tbClockGen (not <$> done)
  rst = resetGen
{-# ANN fromUEnableTB (TestBench 'fromUEnable) #-}
