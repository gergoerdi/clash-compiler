{-|
Copyright  :  (C) 2013-2016, University of Twente,
                  2016     , Myrtle Software Ltd
License    :  BSD2 (see the file LICENSE)
Maintainer :  Christiaan Baaij <christiaan.baaij@gmail.com>
-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}

{-# LANGUAGE Unsafe #-}

{-# OPTIONS_HADDOCK show-extensions not-home #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

module Clash.Sized.Internal.Signed
  ( -- * Datatypes
    Signed (..)
    -- * Accessors
    -- ** Length information
  , size#
    -- * Type classes
    -- ** BitPack
  , pack#
  , unpack#
    -- ** Eq
  , eq#
  , neq#
    -- ** Ord
  , lt#
  , ge#
  , gt#
  , le#
    -- ** Enum (not synthesizable)
  , enumFrom#
  , enumFromThen#
  , enumFromTo#
  , enumFromThenTo#
    -- ** Bounded
  , minBound#
  , maxBound#
    -- ** Num
  , (+#)
  , (-#)
  , (*#)
  , negate#
  , abs#
  , fromInteger#
    -- ** ExtendingNum
  , plus#
  , minus#
  , times#
    -- ** Integral
  , quot#
  , rem#
  , div#
  , mod#
  , toInteger#
    -- ** Bits
  , and#
  , or#
  , xor#
  , complement#
  , shiftL#
  , shiftR#
  , rotateL#
  , rotateR#
    -- ** Resize
  , resize#
  , truncateB#
    -- ** SaturatingNum
  , minBoundSym#
  )
where

import Prelude hiding                 (odd, even)

import Control.DeepSeq                (NFData (..))
import Control.Lens                   (Index, Ixed (..), IxValue)
import Data.Bits                      (Bits (..), FiniteBits (..))
import Data.Data                      (Data)
import Data.Default.Class             (Default (..))
import Data.Proxy                     (Proxy (..))
import Data.Int                       (Int8, Int16, Int32, Int64)
import Text.Read                      (Read (..), ReadPrec)
import GHC.Generics                   (Generic)
import GHC.TypeLits                   (KnownNat, Nat, type (+), natVal, sameNat)
import GHC.TypeLits.Extra             (Max)
import Data.Type.Equality             ((:~:)(..), type (==))
import Data.Type.Bool                 (type (||))
import Unsafe.Coerce                  (unsafeCoerce)
import Language.Haskell.TH            (TypeQ, ExpQ, appT, conT, litT, numTyLit, sigE)
import Language.Haskell.TH.Syntax     (Lift(..))
import Test.QuickCheck.Arbitrary      (Arbitrary (..), CoArbitrary (..),
                                       arbitraryBoundedIntegral,
                                       coarbitraryIntegral, shrinkIntegral)

import Clash.Class.BitPack            (BitPack (..), packXWith)
import Clash.Class.Num                (ExtendingNum (..), SaturatingNum (..),
                                       SaturationMode (..))
import Clash.Class.Parity             (Parity (..))
import Clash.Class.Resize             (Resize (..))
import Clash.Prelude.BitIndex         ((!), msb, replaceBit, split)
import Clash.Prelude.BitReduction     (reduceAnd, reduceOr)
import Clash.Sized.Internal.BitVector (BitVector (BV), Bit, (++#), high, low, undefError)
import qualified Clash.Sized.Internal.BitVector as BV
import Clash.XException
  (ShowX (..), NFDataX (..), errorX, showsPrecXWith, rwhnfX)

eqNat :: forall n m. (KnownNat n, KnownNat m) => Either ((n == m) :~: 'False) (n :~: m)
eqNat =
  case sameNat @n @m Proxy Proxy of
    Just r -> Right r
    Nothing -> Left (unsafeCoerce (Refl :: 'False :~: 'False))

type IsSpecialSize (n :: Nat) = (n == 8) || (n == 16) || (n == 32) || (n == 64)

data SSize (n :: Nat) where
    SSize8 :: SSize 8
    SSize16 :: SSize 16
    SSize32 :: SSize 32
    SSize64 :: SSize 64
    SSizeOther :: (IsSpecialSize n ~ False) => SSize n

sSize :: forall n. (KnownNat n) => SSize n
sSize =
  case eqNat @n @8 of
    Right Refl -> SSize8
    Left Refl -> case eqNat @n @16 of
        Right Refl -> SSize16
        Left Refl -> case eqNat @n @32 of
            Right Refl -> SSize32
            Left Refl -> case eqNat @n @64 of
                Right Refl -> SSize64
                Left Refl -> SSizeOther

type Kit n a8 a16 a32 a64 a0 a =
    ((n ~ 8) => a8) ->
    ((n ~ 16) => a16) ->
    ((n ~ 32) => a32) ->
    ((n ~ 64) => a64) ->
    ((IsSpecialSize n ~ False) => a0) ->
    a

{-# INLINE con #-}
con :: forall n a. (KnownNat n) => Kit n (a -> Int8) (a -> Int16) (a -> Int32) (a -> Int64) (a -> Integer) (a -> Signed n)
con f8 f16 f32 f64 f0 = case sSize @n of
    SSize8 -> S8 . f8
    SSize16 -> S16 . f16
    SSize32 -> S32 . f32
    SSize64 -> S64 . f64
    SSizeOther -> S . f0

{-# INLINE unary #-}
unary :: forall n a. (KnownNat n) => Kit n (Int8 -> a) (Int16 -> a) (Int32 -> a) (Int64 -> a) (Integer -> a) (Signed n -> a)
unary f8 f16 f32 f64 f0 = case sSize @n of
    SSize8     -> \(S8 x)  -> f8  x
    SSize16    -> \(S16 x) -> f16 x
    SSize32    -> \(S32 x) -> f32 x
    SSize64    -> \(S64 x) -> f64 x
    SSizeOther -> \(S x)   -> f0  x

type UnOp a = a -> a

{-# INLINE unOp #-}
unOp :: forall n. (KnownNat n) => Kit n (UnOp Int8) (UnOp Int16) (UnOp Int32) (UnOp Int64) (UnOp Integer) (UnOp (Signed n))
unOp f8 f16 f32 f64 f0 = unary (S8 . f8) (S16 . f16) (S32 . f32) (S64 . f64) (S . f0)

type UnOp2 a b = a -> b -> a

{-# INLINE unOp2 #-}
unOp2 :: forall n a. (KnownNat n) => Kit n (UnOp2 Int8 a) (UnOp2 Int16 a) (UnOp2 Int32 a) (UnOp2 Int64 a) (UnOp2 Integer a) (UnOp2 (Signed n) a)
unOp2 f8 f16 f32 f64 f0 = flip $ \y -> unOp (flip f8 y) (flip f16 y) (flip f32 y) (flip f64 y) (flip f0 y)

type Bin a r = a -> a -> r

{-# INLINE bin #-}
bin :: forall n a. (KnownNat n) => Kit n (Bin Int8 a) (Bin Int16 a) (Bin Int32 a) (Bin Int64 a) (Bin Integer a) (Bin (Signed n) a)
bin f8 f16 f32 f64 f0 = case sSize @n of
    SSize8     -> \ (S8 x)  (S8 y)  -> f8  x y
    SSize16    -> \ (S16 x) (S16 y) -> f16 x y
    SSize32    -> \ (S32 x) (S32 y) -> f32 x y
    SSize64    -> \ (S64 x) (S64 y) -> f64 x y
    SSizeOther -> \ (S x)   (S y)   -> f0  x y

type BinOp a = Bin a a

{-# INLINE binOp #-}
binOp :: forall n. (KnownNat n) => Kit n (BinOp Int8) (BinOp Int16) (BinOp Int32) (BinOp Int64) (BinOp Integer) (BinOp (Signed n))
binOp f8 f16 f32 f64 f0 = bin (S8 ... f8) (S16 ... f16) (S32 ... f32) (S64 ... f64) (S ... f0)
  where
    (...) :: (r -> r') -> (a -> b -> r) -> (a -> b -> r')
    (...) = (.).(.)

-- | Arbitrary-width signed integer represented by @n@ bits, including the sign
-- bit.
--
-- Uses standard 2-complements representation. Meaning that, given @n@ bits,
-- a 'Signed' @n@ number has a range of: [-(2^(@n@-1)) .. 2^(@n@-1)-1]
--
-- __NB__: The 'Num' operators perform @wrap-around@ on overflow. If you want
-- saturation on overflow, check out the 'SaturatingNum' class.
--
-- >>>  maxBound :: Signed 3
-- 3
-- >>> minBound :: Signed 3
-- -4
-- >>> read (show (minBound :: Signed 3)) :: Signed 3
-- -4
-- >>> 1 + 2 :: Signed 3
-- 3
-- >>> 2 + 3 :: Signed 3
-- -3
-- >>> (-2) + (-3) :: Signed 3
-- 3
-- >>> 2 * 3 :: Signed 4
-- 6
-- >>> 2 * 4 :: Signed 4
-- -8
-- >>> (2 :: Signed 3) `mul` (4 :: Signed 4) :: Signed 7
-- 8
-- >>> (2 :: Signed 3) `add` (3 :: Signed 3) :: Signed 4
-- 5
-- >>> (-2 :: Signed 3) `add` (-3 :: Signed 3) :: Signed 4
-- -5
-- >>> satAdd SatSymmetric 2 3 :: Signed 3
-- 3
-- >>> satAdd SatSymmetric (-2) (-3) :: Signed 3
-- -3
data Signed (n :: Nat) where
    S8 :: Int8 -> Signed 8
    S16 :: Int16 -> Signed 16
    S32 :: Int32 -> Signed 32
    S64 :: Int64 -> Signed 64
    S :: (IsSpecialSize n ~ False) => Integer -> Signed n
--   deriving (Data, Generic) -- TODO

instance (KnownNat n) => Data (Signed n) where
  -- TODO

instance (KnownNat n) => Generic (Signed n) where
  -- TODO

instance (KnownNat n) => NFDataX (Signed n) where
  -- TODO
  deepErrorX = undefined -- errorX
  rnfX = undefined -- rwhnfX
  ensureSpine = undefined -- TODO
  hasUndefined = undefined -- TODO

{-# NOINLINE size# #-}
size# :: KnownNat n => Signed n -> Int
size# bv = fromInteger (natVal bv)

instance (KnownNat n) => NFData (Signed n) where
  rnf = unary (\i -> rnf i `seq` ()) (\i -> rnf i `seq` ()) (\i -> rnf i `seq` ()) (\i -> rnf i `seq` ()) (\i -> rnf i `seq` ())
  {-# NOINLINE rnf #-}
  -- NOINLINE is needed so that Clash doesn't trip on the "Signed ~# Integer"
  -- coercion

instance (KnownNat n) => Show (Signed n) where
  show = unary show show show show show
  {-# NOINLINE show #-}

instance (KnownNat n) => ShowX (Signed n) where
  showsPrecX = showsPrecXWith showsPrec

-- | None of the 'Read' class' methods are synthesizable.
instance KnownNat n => Read (Signed n) where
  -- TODO
  -- readPrec = fromIntegral <$> (readPrec :: ReadPrec Integer)

instance KnownNat n => BitPack (Signed n) where
  type BitSize (Signed n) = n
  pack   = packXWith pack#
  unpack = unpack#

{-# NOINLINE pack# #-}
pack# :: forall n . KnownNat n => Signed n -> BitVector n
pack# = unary f f f f f -- TODO
  where
    f :: (Integral a, Bits a, Num a) => a -> BitVector n
    f i = BV 0 . fromIntegral $
          let m = 1 `shiftL` fromInteger (natVal (Proxy @n))
          in  if i < 0 then m + i else i

{-# NOINLINE unpack# #-}
unpack# :: forall n . KnownNat n => BitVector n -> Signed n
unpack# = con f f f f f
  where
    f :: (Num a) => BitVector n -> a
    f (BV 0 i) = fromInteger $ if i >= m then (i-2*m) else i
    f bv = undefError "Signed.unpack" [bv]

    m = 1 `shiftL` fromInteger (natVal (Proxy @n) - 1)

instance (KnownNat n) => Eq (Signed n) where
  (==) = eq#
  (/=) = neq#

{-# NOINLINE eq# #-}
eq# :: (KnownNat n) => Signed n -> Signed n -> Bool
eq# = bin (==) (==) (==) (==) (==)

{-# NOINLINE neq# #-}
neq# :: (KnownNat n) => Signed n -> Signed n -> Bool
neq# = bin (/=) (/=) (/=) (/=) (/=)

instance (KnownNat n) => Ord (Signed n) where
  (<)  = lt#
  (>=) = ge#
  (>)  = gt#
  (<=) = le#

lt#,ge#,gt#,le# :: (KnownNat n) => Signed n -> Signed n -> Bool
{-# NOINLINE lt# #-}
lt# = bin (<) (<) (<) (<) (<)
{-# NOINLINE ge# #-}
ge# = bin (>=) (>=) (>=) (>=) (>=)
{-# NOINLINE gt# #-}
gt# = bin (>) (>) (>) (>) (>)
{-# NOINLINE le# #-}
le# = bin (<=) (<=) (<=) (<=) (<=)

-- | The functions: 'enumFrom', 'enumFromThen', 'enumFromTo', and
-- 'enumFromThenTo', are not synthesizable.
instance KnownNat n => Enum (Signed n) where
  succ           = (+# fromInteger# 1)
  pred           = (-# fromInteger# 1)
  toEnum         = fromInteger# . toInteger
  fromEnum       = fromEnum . toInteger#
  enumFrom       = enumFrom#
  enumFromThen   = enumFromThen#
  enumFromTo     = enumFromTo#
  enumFromThenTo = enumFromThenTo#

{-# NOINLINE enumFrom# #-}
{-# NOINLINE enumFromThen# #-}
{-# NOINLINE enumFromTo# #-}
{-# NOINLINE enumFromThenTo# #-}
enumFrom#       :: KnownNat n => Signed n -> [Signed n]
enumFromThen#   :: KnownNat n => Signed n -> Signed n -> [Signed n]
enumFromTo#     :: Signed n -> Signed n -> [Signed n]
enumFromThenTo# :: Signed n -> Signed n -> Signed n -> [Signed n]
enumFrom# = undefined -- TODO
enumFromThen# = undefined -- TODO
enumFromTo# = undefined -- TODO
enumFromThenTo# = undefined -- TODO
-- enumFrom# x             = map fromInteger_INLINE [unsafeToInteger x ..]
-- enumFromThen# x y       = map fromInteger_INLINE [unsafeToInteger x, unsafeToInteger y ..]
-- enumFromTo# x y         = map S [unsafeToInteger x .. unsafeToInteger y]
-- enumFromThenTo# x1 x2 y = map S [unsafeToInteger x1, unsafeToInteger x2 .. unsafeToInteger y]


instance KnownNat n => Bounded (Signed n) where
  minBound = minBound#
  maxBound = maxBound#

minBound#,maxBound# :: KnownNat n => Signed n
{-# NOINLINE minBound# #-}
minBound# = undefined -- TODO let res = S $ negate $ 2 ^ (natVal res - 1) in res
{-# NOINLINE maxBound# #-}
maxBound# = undefined -- TODO let res = S $ 2 ^ (natVal res - 1) - 1 in res

-- | Operators do @wrap-around@ on overflow
instance KnownNat n => Num (Signed n) where
  (+)         = (+#)
  (-)         = (-#)
  (*)         = (*#)
  negate      = negate#
  abs         = abs#
  signum s    = if s < 0 then (-1) else
                   if s > 0 then 1 else 0
  fromInteger = fromInteger#

(+#), (-#), (*#) :: forall n . KnownNat n => Signed n -> Signed n -> Signed n
{-# NOINLINE (+#) #-}
(+#) = binOp (+) (+) (+) (+) $ \a b ->
  let m  = 1 `shiftL` fromInteger (natVal (Proxy @n) -1)
      z  = a + b
  in  if z >= m then (z - 2*m) else
         if z < negate m then (z + 2*m) else z

{-# NOINLINE (-#) #-}
(-#) = binOp (-) (-) (-) (-) $ \a b ->
  let m  = 1 `shiftL` fromInteger (natVal (Proxy @n) -1)
      z  = a - b
  in  if z < negate m then (z + 2*m) else
         if z >= m then (z - 2*m) else z

{-# NOINLINE (*#) #-}
(*#) = binOp (*) (*) (*) (*) (*)

negate#,abs# :: forall n . KnownNat n => Signed n -> Signed n
{-# NOINLINE negate# #-}
negate# = unOp negate negate negate negate $ \i ->
    let m = 1 `shiftL` fromInteger (natVal (Proxy @n) -1)
        z = negate i
    in  if z == m then i else z

{-# NOINLINE abs# #-}
abs# = unOp abs abs abs abs $ \i ->
  let m = 1 `shiftL` fromInteger (natVal (Proxy @n) -1)
      z = abs i
  in  if z == m then i else z

{-# NOINLINE fromInteger# #-}
fromInteger# :: KnownNat n => Integer -> Signed (n :: Nat)
fromInteger# = fromInteger_INLINE

{-# INLINE fromInteger_INLINE #-}
fromInteger_INLINE :: forall n . KnownNat n => Integer -> Signed n
fromInteger_INLINE = con f f f f f
  where
    f :: (Integral a) => Integer -> a
    f i = if mask == 0 then 0 else fromIntegral res
      where
        mask = 1 `shiftL` fromInteger (natVal (Proxy @n) -1)
        res  = case divMod i mask of
                 (s,i') | even s    -> i'
                        | otherwise -> i' - mask

instance ExtendingNum (Signed m) (Signed n) where
  type AResult (Signed m) (Signed n) = Signed (Max m n + 1)
  add  = plus#
  sub = minus#
  type MResult (Signed m) (Signed n) = Signed (m + n)
  mul = times#

plus#, minus# :: Signed m -> Signed n -> Signed (Max m n + 1)
{-# NOINLINE plus# #-}
plus# = undefined -- TODO (S a) (S b) = S (a + b)

{-# NOINLINE minus# #-}
minus# = undefined -- TODO (S a) (S b) = S (a - b)

{-# NOINLINE times# #-}
times# :: Signed m -> Signed n -> Signed (m + n)
times# = undefined -- TODO (S a) (S b) = S (a * b)

instance KnownNat n => Real (Signed n) where
  toRational = toRational . toInteger#

instance KnownNat n => Integral (Signed n) where
  quot        = quot#
  rem         = rem#
  div         = div#
  mod         = mod#
  quotRem n d = (n `quot#` d,n `rem#` d)
  divMod  n d = (n `div#`  d,n `mod#` d)
  toInteger   = toInteger#

quot#,rem# :: Signed n -> Signed n -> Signed n
{-# NOINLINE quot# #-}
quot# (S a) (S b) = S (a `quot` b)
{-# NOINLINE rem# #-}
rem# (S a) (S b) = S (a `rem` b)

div#,mod# :: Signed n -> Signed n -> Signed n
{-# NOINLINE div# #-}
div# (S a) (S b) = S (a `div` b)
{-# NOINLINE mod# #-}
mod# (S a) (S b) = S (a `mod` b)

{-# NOINLINE toInteger# #-}
toInteger# :: (KnownNat n) => Signed n -> Integer
toInteger# = toInteger_INLINE

{-# INLINE toInteger_INLINE #-}
toInteger_INLINE :: (KnownNat n) => Signed n -> Integer
toInteger_INLINE = unary toInteger toInteger toInteger toInteger id

instance KnownNat n => Parity (Signed n) where
  even = even . pack
  odd = odd . pack

instance KnownNat n => Bits (Signed n) where
  (.&.)             = and#
  (.|.)             = or#
  xor               = xor#
  complement        = complement#
  zeroBits          = 0
  bit i             = replaceBit i high 0
  setBit v i        = replaceBit i high v
  clearBit v i      = replaceBit i low  v
  complementBit v i = replaceBit i (BV.complement## (v ! i)) v
  testBit v i       = v ! i == 1
  bitSizeMaybe v    = Just (size# v)
  bitSize           = size#
  isSigned _        = True
  shiftL v i        = shiftL# v i
  shiftR v i        = shiftR# v i
  rotateL v i       = rotateL# v i
  rotateR v i       = rotateR# v i
  popCount s        = popCount (pack# s)

and#,or#,xor# :: KnownNat n => Signed n -> Signed n -> Signed n
{-# NOINLINE and# #-}
and# (S a) (S b) = fromInteger_INLINE (a .&. b)
{-# NOINLINE or# #-}
or# (S a) (S b)  = fromInteger_INLINE (a .|. b)
{-# NOINLINE xor# #-}
xor# (S a) (S b) = fromInteger_INLINE (xor a b)

{-# NOINLINE complement# #-}
complement# :: KnownNat n => Signed n -> Signed n
complement# (S a) = fromInteger_INLINE (complement a)

shiftL#,shiftR#,rotateL#,rotateR# :: KnownNat n => Signed n -> Int -> Signed n
{-# NOINLINE shiftL# #-}
shiftL# = unOp2 f f f f f
  where
    f n b | b < 0     = error "'shiftL' undefined for negative numbers"
          | otherwise = n `shiftL` b
{-# NOINLINE shiftR# #-}
shiftR# = unOp2 f f f f f
  where
    f n b | b < 0     = error "'shiftR undefined for negative numbers"
          | otherwise = n `shiftR` b
{-# NOINLINE rotateL# #-}
rotateL# _ b | b < 0 = error "'shiftL undefined for negative numbers"
rotateL# s@(S n) b   = fromInteger_INLINE (l .|. r)
  where
    l    = shiftL n b'
    r    = shiftR n b'' .&. mask
    mask = 2 ^ b' - 1

    b'   = b `mod` sz
    b''  = sz - b'
    sz   = fromInteger (natVal s)

{-# NOINLINE rotateR# #-}
rotateR# _ b | b < 0 = error "'shiftR undefined for negative numbers"
rotateR# s@(S n) b   = fromInteger_INLINE (l .|. r)
  where
    l    = shiftR n b' .&. mask
    r    = shiftL n b''
    mask = 2 ^ b'' - 1

    b'  = b `mod` sz
    b'' = sz - b'
    sz  = fromInteger (natVal s)

instance KnownNat n => FiniteBits (Signed n) where
  finiteBitSize        = size#
  countLeadingZeros  s = countLeadingZeros  (pack# s)
  countTrailingZeros s = countTrailingZeros (pack# s)

instance Resize Signed where
  resize       = resize#
  zeroExtend s = unpack# (0 ++# pack s)
  truncateB    = truncateB#

{-# NOINLINE resize# #-}
resize# :: forall m n . (KnownNat n, KnownNat m) => Signed n -> Signed m
resize# = undefined
-- resize# s@(S i) | n' <= m'  = extended
--                 | otherwise = truncated
--   where
--     n  = fromInteger (natVal s)
--     n' = shiftL 1 n
--     m' = shiftL mask 1
--     extended = S i

--     mask      = 1 `shiftL` fromInteger (natVal (Proxy @m) -1)
--     i'        = i `mod` mask
--     truncated = if testBit i (n-1)
--                    then S (i' - mask)
--                    else S i'

{-# NOINLINE truncateB# #-}
truncateB# :: (KnownNat n, KnownNat m) => Signed (m + n) -> Signed m
truncateB# = unary f f f f f
  where
    f :: (Integral a, KnownNat m) => a -> Signed m
    f = fromInteger_INLINE . toInteger

instance KnownNat n => Default (Signed n) where
  def = fromInteger# 0

instance forall n. (KnownNat n) => Lift (Signed n) where
  lift = unary f f f f f
   where
     f :: (Lift a) => a -> ExpQ
     f i = sigE [| fromInteger# i |] (decSigned (natVal (Proxy @n)))
  {-# NOINLINE lift #-}

decSigned :: Integer -> TypeQ
decSigned n = appT (conT ''Signed) (litT $ numTyLit n)

instance KnownNat n => SaturatingNum (Signed n) where
  satAdd SatWrap  a b = a +# b
  satAdd SatBound a b =
    let r      = plus# a b
        (_,r') = split r
    in  case msb r `xor` msb r' of
          0 -> unpack# r'
          _ -> case msb a .&. msb b of
            0 -> maxBound#
            _ -> minBound#
  satAdd SatZero a b =
    let r      = plus# a b
        (_,r') = split r
    in  case msb r `xor` msb r' of
          0 -> unpack# r'
          _ -> fromInteger# 0
  satAdd SatSymmetric a b =
    let r      = plus# a b
        (_,r') = split r
    in  case msb r `xor` msb r' of
          0 -> unpack# r'
          _ -> case msb a .&. msb b of
            0 -> maxBound#
            _ -> minBoundSym#

  satSub SatWrap a b = a -# b
  satSub SatBound a b =
    let r      = minus# a b
        (_,r') = split r
    in  case msb r `xor` msb r' of
          0 -> unpack# r'
          _ -> case BV.pack# (msb a) ++# BV.pack# (msb b) of
            2 -> minBound#
            _ -> maxBound#
  satSub SatZero a b =
    let r      = minus# a b
        (_,r') = split r
    in  case msb r `xor` msb r' of
          0 -> unpack# r'
          _ -> fromInteger# 0
  satSub SatSymmetric a b =
    let r      = minus# a b
        (_,r') = split r
    in  case msb r `xor` msb r' of
          0 -> unpack# r'
          _ -> case BV.pack# (msb a) ++# BV.pack# (msb b) of
            2 -> minBoundSym#
            _ -> maxBound#

  satMul SatWrap a b = a *# b
  satMul SatBound a b =
    let r        = times# a b
        (rL,rR)  = split r
        overflow = complement (reduceOr (BV.pack# (msb rR) ++# pack rL)) .|.
                              reduceAnd (BV.pack# (msb rR) ++# pack rL)
    in  case overflow of
          1 -> unpack# rR
          _ -> case msb rL of
            0 -> maxBound#
            _ -> minBound#
  satMul SatZero a b =
    let r        = times# a b
        (rL,rR)  = split r
        overflow = complement (reduceOr (BV.pack# (msb rR) ++# pack rL)) .|.
                              reduceAnd (BV.pack# (msb rR) ++# pack rL)
    in  case overflow of
          1 -> unpack# rR
          _ -> fromInteger# 0
  satMul SatSymmetric a b =
    let r        = times# a b
        (rL,rR)  = split r
        overflow = complement (reduceOr (BV.pack# (msb rR) ++# pack rL)) .|.
                              reduceAnd (BV.pack# (msb rR) ++# pack rL)
    in  case overflow of
          1 -> unpack# rR
          _ -> case msb rL of
            0 -> maxBound#
            _ -> minBoundSym#

minBoundSym# :: KnownNat n => Signed n
minBoundSym# = minBound# +# fromInteger# 1

instance KnownNat n => Arbitrary (Signed n) where
  arbitrary = arbitraryBoundedIntegral
  shrink    = shrinkSizedSigned

shrinkSizedSigned :: (KnownNat n, Integral (p n)) => p n -> [p n]
shrinkSizedSigned x | natVal x < 2 = case toInteger x of
                                       0 -> []
                                       _ -> [0]
                    -- 'shrinkIntegral' uses "`quot` 2", which for sized types
                    -- less than 2 bits wide results in a division by zero.
                    --
                    -- See: https://github.com/clash-lang/clash-compiler/issues/153
                    | otherwise    = shrinkIntegral x
{-# INLINE shrinkSizedSigned #-}

instance KnownNat n => CoArbitrary (Signed n) where
  coarbitrary = coarbitraryIntegral

type instance Index   (Signed n) = Int
type instance IxValue (Signed n) = Bit
instance KnownNat n => Ixed (Signed n) where
  ix i f s = unpack# <$> BV.replaceBit# (pack# s) i
                     <$> f (BV.index# (pack# s) i)
