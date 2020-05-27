{-|
  Copyright   :  (C) 2019, Myrtle Software Ltd.
  License     :  BSD2 (see the file LICENSE)
  Maintainer  :  QBayLogic B.V. <devops@qbaylogic.com>

This module contains a mini dsl for creating haskell blackbox
instantiations.
-}

{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms   #-}
{-# LANGUAGE QuasiQuotes       #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE ViewPatterns      #-}

module Clash.Primitives.DSL
  (
  -- * Annotations
    blackBoxHaskell

  -- * declarations
  , BlockState (..)
  , TExpr
  , declaration
  , instDecl
  , viaAnnotatedSignal

  -- ** Literals
  , bvLit
  , LitHDL (..)
  , pattern High
  , pattern Low
  , tuple

  -- ** Extraction
  , tInputs
  , tResult
  , getStr
  , getBool
  , exprToInteger
  , tExprToInteger
  , untuple

  -- ** Conversion
  , toBV
  , fromBV
  , boolToBit
  , boolFromBit
  , boolFromBitVector
  , unsignedFromBitVector
  , boolFromBits

  -- ** Operations
  , andExpr
  , notExpr
  , pureToBV
  , pureToBVResized
  , open

  -- ** Utilities
  , toIdentifier
  , tySize
  , clog2
  ) where

import           Clash.Util                      (clogBase)
import           Control.Lens                    hiding (Indexed, assign)
import           Control.Monad.State
import           Data.List                       (intersperse)
import           Data.Maybe                      (fromMaybe)
import           Data.Semigroup                  hiding (Product)
import           Data.Semigroup.Monad
import           Data.String
import           Data.Text                       (Text)
import qualified Data.Text                       as Text
import           Data.Text.Prettyprint.Doc.Extra
import           TextShow                        (showt)

import           Clash.Annotations.Primitive     (HDL (..), Primitive (..))
import           Clash.Backend                   hiding (fromBV, toBV)
import           Clash.Core.Var                  (Attr')
import           Clash.Netlist.BlackBox.Util     (exprToString)
import           Clash.Netlist.Id
import           Clash.Netlist.Types             hiding (toBit)
import           Clash.Netlist.Util              hiding (mkUniqueIdentifier)
import qualified Data.String.Interpolate         as I
import           Data.String.Interpolate.Util    (unindent)
import           Language.Haskell.TH             (Name)
import           Prelude

-- | Create a blackBoxHaskell primitive. To be used as part of an annotation:
--
-- @
-- {-# ANN myFunction (blackBoxHaskell [1,2,3] VHDL 'myFunction 'myBBF) #-}
-- @
blackBoxHaskell
  :: [Int]
  -- ^ Ignored arguments
  -> HDL
  -- ^ hdl the blackbox is for
  -> Name
  -- ^ blackbox name
  -> Name
  -- ^ template function name
  -> Primitive
blackBoxHaskell (show -> ign) hdl bb tf =
  InlinePrimitive [hdl] $ unindent [I.i|
  [ { "BlackBoxHaskell" :
       { "name" : "#{bb}"
       , "templateFunction" : "#{tf}"
       , "ignoredArguments" : #{ign}
       }
    }
  ]
|]

-- | The state of a block. Contains a list of declarations and a the
--   backend state.
data BlockState backend = BlockState
  { _bsDeclarations :: [Declaration]
  , _bsBackend      :: backend
  }

-- | A typed expression.
data TExpr = TExpr
  { ety :: HWType
  , eex :: Expr
  } deriving Show

makeLenses ''BlockState
makeLenses ''TExpr

-- | Run a block declaration.
declaration
  :: Backend backend
  => Text.Text
  -- ^ block name
  -> State (BlockState backend) ()
  -- ^ block builder
  -> State backend Doc
  -- ^ pretty printed block
declaration blockName s = do
  backend0 <- get
  let initState = BlockState [] backend0
      BlockState decs backend1 = execState s initState
  put backend1
  blockNameUnique <- mkUniqueIdentifier Basic blockName
  getMon $ blockDecl blockNameUnique (reverse decs)

-- | Add a declaration to the state.
addDeclaration :: Declaration -> State (BlockState backend) ()
addDeclaration dec = bsDeclarations %= cons dec

-- | Create a new basic unique name using the given Text as a template.
newName :: Backend backend => Text -> State (BlockState backend) Identifier
newName nm = zoom bsBackend $ mkUniqueIdentifier Basic nm

-- | Declare a new signal with the given name and type.
declare :: Backend backend => Identifier -> HWType -> State (BlockState backend) TExpr
declare decName ty = do
  uniqueName <- newName decName
  addDeclaration (NetDecl Nothing uniqueName ty)
  pure (TExpr ty (Identifier uniqueName Nothing))

-- | Assign an expression to an identifier, returns the new typed
--   identifier expression.
assign
  :: Backend backend
  => Text
  -- ^ guide name to be assigned
  -> TExpr
  -- ^ expression to be assigned to
  -> State (BlockState backend) TExpr
  -- ^ the identifier of the expression that actually got assigned
assign aName (TExpr ty aExpr) = do
  texp@(~(TExpr _ (Identifier uniqueName Nothing))) <- declare aName ty
  addDeclaration (Assignment uniqueName aExpr)
  pure texp
{-# ANN assign ("HLint: ignore Redundant bracket" :: String) #-} -- it's not redundant

-- | Extract the elements of a tuple expression and return expressions
--   to them. These new expressions are given unique names and get
--   declared the block scope.
untuple
  :: Backend backend
  => TExpr
  -- ^ Tuple expression
  -> [Identifier]
  -- ^ desired names to assign the tuple elements to
  -> State (BlockState backend) [TExpr]
untuple (TExpr ty@(Product _ _ tys) (Identifier resName _)) vals = do
  newNames <- zipWithM declare vals tys
  addDeclaration $ Assignment resName $ DataCon ty (DC (ty, 0)) (fmap eex newNames)
  pure newNames
untuple e i = error $ "untuple: " <> show e <> " " <> show i

-- | The high literal bit.
pattern High :: TExpr
pattern High <- TExpr Bit (Literal _ (BitLit H))
  where High = TExpr Bit (Literal (Just (Bit,1)) (BitLit H))

-- | The low literal bit.
pattern Low :: TExpr
pattern Low <- TExpr Bit (Literal _ (BitLit L))
  where Low = TExpr Bit (Literal (Just (Bit,1)) (BitLit L))

-- | The true literal bool.
pattern T :: TExpr
pattern T <- TExpr Bool (Literal _ (BoolLit True))
  where T = TExpr Bool (Literal (Just (Bool,1)) (BoolLit True))

-- | The false literal bool.
pattern F :: TExpr
pattern F <- TExpr Bool (Literal _ (BoolLit False))
  where F = TExpr Bool (Literal (Just (Bool,1)) (BoolLit False))

-- | Construct a fully defined BitVector literal
bvLit
  :: Int
  -- ^ BitVector size
  -> Integer
  -- ^ Literal
  -> TExpr
bvLit sz n =
  TExpr
    (BitVector sz)
    (Literal (Just (BitVector sz, sz)) (BitVecLit 0 n))

-- | Convert a bool to a bit.
boolToBit
  :: Backend backend
  => Identifier
  -> TExpr
  -> State (BlockState backend) TExpr
boolToBit bitName = \case
  T -> pure High
  F -> pure Low
  TExpr Bool boolExpr -> do
    texp@(~(TExpr _ (Identifier uniqueBitName Nothing))) <- declare bitName Bit
    addDeclaration $
      CondAssignment uniqueBitName Bit boolExpr Bool
        [ (Just (BoolLit True), Literal Nothing (BitLit H))
        , (Nothing            , Literal Nothing (BitLit L))
        ]
    pure texp
  tExpr -> error $ "boolToBit: Got \"" <> show tExpr <> "\" expected Bool"
{-# ANN boolToBit ("HLint: ignore Redundant bracket" :: String) #-} -- it's not redundant

-- | Use to create an output `Bool` from a `Bit`. The expression given
--   must be the identifier of the bool you wish to get assigned.
--   Returns a reference to a declared `Bit` that should get assigned
--   by something (usually the output port of an entity).
boolFromBit
  :: Backend backend
  => Identifier
  -> TExpr
  -> State (BlockState backend) TExpr
boolFromBit = outputCoerce Bit Bool (<> " = '1'")

-- | Used to create an output `Bool` from a `BitVector` of given size.
-- Works in a similar way to `boolFromBit` above.
boolFromBitVector
  :: Backend backend
  => Size
  -> Identifier
  -> TExpr
  -> State (BlockState backend) TExpr
boolFromBitVector n = outputCoerce (BitVector n) Bool (\i -> "unsigned(" <> i <> ") > 0")

-- | Used to create an output `Unsigned` from a `BitVector` of given
-- size. Works in a similar way to `boolFromBit` above.
unsignedFromBitVector
  :: Backend backend
  => Size
  -> Identifier
  -> TExpr
  -> State (BlockState backend) TExpr
unsignedFromBitVector n = outputCoerce (BitVector n) (Unsigned n) (\i -> "unsigned(" <> i <> ")")

-- | Used to create an output `Bool` from a number of `Bit`s, using
-- conjunction. Similarly to `untuple`, it returns a list of
-- references to declared values (the inputs to the function) which
-- should get assigned by something---usually output ports of an
-- entity.
boolFromBits
  :: Backend backend
  => [Identifier]
  -> TExpr
  -> State (BlockState backend) [TExpr]
boolFromBits inNames = outputFn (map (const Bit) inNames) Bool
  (foldl (<>) "" . intersperse " and " . map (\i -> "(" <> i <> " = '1')")) inNames

-- | Used to create an output value with an arbitrary VHDL coercion.
-- The expression given should be the identifier of the output value
-- you wish to get assigned. Returns a reference to a declared value
-- of the input type that should get assigned by something (usually
-- the output port of an entity).
outputCoerce
  :: Backend backend
  => HWType
  -> HWType
  -> (Identifier -> Identifier)
  -> Identifier
  -> TExpr
  -> State (BlockState backend) TExpr
outputCoerce fromType toType exprStringFn inName (TExpr outType (Identifier outName Nothing))
  | outType == toType = do
      inName' <- newName inName
      let exprIdent = Identifier (exprStringFn inName') Nothing
      addDeclaration (NetDecl Nothing inName' fromType)
      addDeclaration (Assignment outName exprIdent)
      pure (TExpr fromType (Identifier inName' Nothing))
outputCoerce _ toType _ _ texpr = error $ "outputCoerce: the expression " <> show texpr
                                  <> " must be an Identifier with type " <> show toType

-- | Used to create an output value that is an arbitrary function (as
-- VHDL) of existing values. The expression given should be the
-- identifier of the output value you wish to get assigned. Similarly
-- to `untuple`, it returns a list of references to declared values
-- (the inputs to the function) which should get assigned by
-- something---usually output ports of an entity.
outputFn
  :: Backend backend
  => [HWType]
  -> HWType
  -> ([Identifier] -> Identifier)
  -> [Identifier]
  -> TExpr
  -> State (BlockState backend) [TExpr]
outputFn fromTypes toType exprFn inNames (TExpr outType (Identifier outName Nothing))
  | outType == toType = do
      inNames' <- mapM newName inNames
      let exprIdent = Identifier (exprFn inNames') Nothing
      sequenceOf_ each [ addDeclaration (NetDecl Nothing nm t)
                       | (nm,t) <- zip inNames' fromTypes ]
      addDeclaration (Assignment outName exprIdent)
      pure [ TExpr t (Identifier nm Nothing)
           | (nm,t) <- zip inNames' fromTypes ]
outputFn _ outType _ _ texpr =
  error $ "outputBinaryFn: the expression " <> show texpr
  <> " must be an Identifier with type " <> show outType

-- | Create a tuple of 'TExpr'
tuple :: TExpr -> TExpr -> TExpr
tuple a b =
  let
    ty = Product "GHC.Tuple.(,)" Nothing [ety a, ety b]
  in TExpr ty (DataCon ty (DC (ty,0)) [eex a, eex b])

-- | Try to get the literal string value of an expression.
getStr :: TExpr -> Maybe String
getStr (TExpr _ e) = exprToString e

-- | Try to get the literal bool value of an expression.
getBool :: TExpr -> Maybe Bool
getBool (TExpr _ (Literal _ (BoolLit b))) = Just b
getBool _ = Nothing

-- | Try to get the literal nat value of an expression.
tExprToInteger :: TExpr -> Maybe Integer
tExprToInteger (TExpr _ e) = exprToInteger e

exprToInteger :: Expr -> Maybe Integer
exprToInteger (DataCon _ _ [n]) = exprToInteger n
exprToInteger (Literal _ (NumLit n)) = Just n
exprToInteger _ = Nothing

-- | Assign an input bitvector to an expression. Declares a new
--   bitvector if the expression is not already a bitvector.
toBV
  :: Backend backend
  => Identifier
  -- ^ BitVector name
  -> TExpr
  -- ^ expression
  -> State (BlockState backend) TExpr
  -- ^ BitVector expression
toBV bvName a = case a of
  TExpr BitVector{} _ -> pure a
  TExpr aTy aExpr     -> assign bvName $
    TExpr (BitVector (typeSize aTy)) (ConvBV Nothing aTy True aExpr)

-- | Assign an output bitvector to an expression. Declares a new
--   bitvector if the expression is not already a bitvector.
fromBV
  :: Backend backend
  => Identifier
  -- ^ BitVector name
  -> TExpr
  -- ^ expression
  -> State (BlockState backend) TExpr
  -- ^ bv expression
fromBV _ a@(TExpr BitVector{} _) = pure a
fromBV bvName (TExpr aTy (Identifier aName Nothing)) = do
  bvName' <- newName bvName
  let bvExpr = ConvBV Nothing aTy False (Identifier bvName' Nothing)
      bvTy   = BitVector (typeSize aTy)
  addDeclaration (NetDecl Nothing bvName' bvTy)
  addDeclaration (Assignment aName bvExpr)
  pure (TExpr bvTy (Identifier bvName' Nothing))
fromBV _ texpr = error $ "fromBV: the expression " <> show texpr <> "must be an Indentifier"

clog2 :: Num i => Integer -> i
clog2 = fromIntegral . fromMaybe 0 . clogBase 2

tySize :: Num i => HWType -> i
tySize = fromIntegral . typeSize

-- | A literal that can be used for hdl attributes. It has a `Num` and
--   `IsString` instances for convenience.
data LitHDL
  = B Bool
  | S String
  | I Integer
  deriving Show

instance Num LitHDL where
  (+) = undefined
  (*) = undefined
  abs = undefined
  signum = undefined
  negate = undefined
  fromInteger = I

instance IsString LitHDL where
  fromString = S

-- | Instantiate a component/entity in a block state.
instDecl
  :: Backend backend
  => EntityOrComponent
  -- ^ Type of instantiation
  -> Identifier
  -- ^ component/entity name
  -> Identifier
  -- ^ instantiation label
  -> [(Text, LitHDL)]
  -- ^ attributes
  -> [(Text, TExpr)]
  -- ^ in ports
  -> [(Text, TExpr)]
  -- ^ out ports
  -> State (BlockState backend) ()
instDecl entOrComp compName instLbl attrs inPorts outPorts = do

  inPorts' <- mapM (mkPort In) inPorts
  outPorts' <- mapM (mkPort Out) outPorts

  addDeclaration $ InstDecl entOrComp Nothing compName instLbl (mkAttrs attrs) (inPorts' ++ outPorts')
    where
    mkPort inOrOut (nm, pExpr) = do
      TExpr ty pExpr' <- toIdentifier (nm <> "_port")  pExpr
      pure (Identifier nm Nothing, inOrOut, ty, pExpr')

    -- Convert a list of name attributes to the form clash wants
    mkAttrs :: [(Text.Text, LitHDL)] -> [(Expr, HWType, Expr)]
    mkAttrs = map (\(s, ty) -> (Identifier s Nothing, hdlTy ty, litExpr ty))

    litExpr :: LitHDL -> Expr
    litExpr (B b) = Literal Nothing (BoolLit b)
    litExpr (S s) = Literal Nothing (StringLit s)
    litExpr (I i) = Literal Nothing (NumLit i)

    hdlTy :: LitHDL -> HWType
    hdlTy = \case
      B{} -> Bool
      S{} -> String
      I{} -> Integer

-- | Wires the two given `TExpr`s together using a newly declared
-- signal with (exactly) the given name `sigNm`. The new signal has an
-- annotated type, using the given attributes.
viaAnnotatedSignal
  :: Backend backend
  => Text
  -- ^ Name given to signal
  -> TExpr
  -- ^ expression the signal is assigned to
  -> TExpr
  -- ^ expression (must be identifier) to which the signal is assigned
  -> [Attr']
  -- ^ the attributes to annotate the signal with
  -> State (BlockState backend) ()
viaAnnotatedSignal sigNm (TExpr fromTy fromExpr) (TExpr toTy (Identifier outNm Nothing)) attrs
  | fromTy == toTy = do
      addDeclaration (NetDecl Nothing sigNm (Annotated attrs fromTy))
      addDeclaration (Assignment sigNm fromExpr)
      addDeclaration (Assignment outNm (Identifier sigNm Nothing))
viaAnnotatedSignal _ inTExpr outTExpr@(TExpr _ (Identifier _ _)) _ =
  error $ "viaAnnotatedSignal: The in and out expressions \"" <> show inTExpr <>
  "\" and \"" <> show outTExpr <> "\" have non-matching types."
viaAnnotatedSignal _ _ outTExpr _ =
  error $ "viaAnnotatedSignal: The out expression \"" <> show outTExpr <>
  "\" must be an Identifier."

-- | The TExp inputs from a blackbox context.
tInputs :: BlackBoxContext -> [(TExpr, HWType)]
tInputs = map (\(x, t, _) -> (TExpr t x, t)) . bbInputs

-- | The TExp result of a blackbox context.
tResult :: BlackBoxContext -> TExpr
tResult = (\(x,t) -> TExpr t x) . bbResult

-- | Get an identifier to an expression, creating a new assignment if
--   necessary.
toIdentifier'
  :: Backend backend
  => Identifier
  -- ^ desired new identifier name
  -> TExpr
  -- ^ expression to get identifier of
  -> State (BlockState backend) Identifier
  -- ^ identifier to expression
toIdentifier' _ (TExpr _ (Identifier aExpr Nothing)) = pure aExpr
toIdentifier' nm texp = do
  ~(TExpr _ (Identifier nm' Nothing)) <- assign nm texp
  pure nm'

-- | Get an identifier to an expression, creating a new assignment if
--   necessary.
toIdentifier
  :: Backend backend
  => Identifier
  -- ^ desired new identifier name
  -> TExpr
  -- ^ expression to get identifier of
  -> State (BlockState backend) TExpr
  -- ^ identifier to expression
toIdentifier nm texp = do
  id' <- toIdentifier' nm texp
  pure (TExpr (ety texp) (Identifier id' Nothing))

-- | And together @(&&)@ two expressions, assigning it to a new identifier.
andExpr
  :: Backend backend
  => Identifier
  -- ^ desired name
  -> TExpr
  -- ^ a
  -> TExpr
  -- ^ a
  -> State (BlockState backend) TExpr
  -- ^ a && b
andExpr _ T bExpr = pure bExpr
andExpr _ F _     = pure F
andExpr _ aExpr T = pure aExpr
andExpr _ _ F     = pure F
andExpr nm a b = do
  aIdent <- toIdentifier' (nm <> "_a") a
  bIdent <- toIdentifier' (nm <> "_b") b
  -- This is somewhat hacky and relies on the fact that clash doesn't
  -- postprocess the text in Identifier. The alternative is to run
  -- this as a fully fledged @BlackBoxE@ but that involves a lot of
  -- faffing. It should be reasonably safe because we assign each side
  -- to an identifier if it isn't already.
  andTxt <-
    uses bsBackend hdlKind <&> \case
      VHDL          -> aIdent <> " and " <> bIdent
      Verilog       -> aIdent <> " && " <> bIdent
      SystemVerilog -> aIdent <> " && " <> bIdent
  assign nm $ TExpr Bool (Identifier andTxt Nothing)

-- | Negate @(not)@ an expression, assigning it to a new identifier.
notExpr
  :: Backend backend
  => Identifier
  -- ^ desired name
  -> TExpr
  -- ^ a
  -> State (BlockState backend) TExpr
  -- ^ not a
notExpr _ T = pure F
notExpr _ F = pure T
notExpr nm aExpr = do
  aIdent <- toIdentifier' (nm <> "_a") aExpr
  -- See disclaimer in `andExpr` above.
  notTxt <- uses bsBackend hdlKind <&> \case
    VHDL          -> "not " <> aIdent
    Verilog       -> "! " <> aIdent
    SystemVerilog -> "! " <> aIdent
  assign nm $ TExpr Bit (Identifier notTxt Nothing)

-- | Creates a BV that produces the following vhdl:
--
-- @
--    (0 to n => ARG)
-- @
pureToBV
  :: Backend backend
  => Identifier
  -- ^ desired name
  -> Int
  -- ^ Size (n)
  -> TExpr
  -- ^ ARG
  -> State (BlockState backend) TExpr
  -- ^ (0 to n => ARG)
pureToBV nm n arg = do
  arg' <- toIdentifier' nm arg
  -- This is very hard coded and hacky
  let text = "(0 to " <> showt n <> " => " <> arg' <> ")"
  assign nm $ TExpr (BitVector (n+1)) (Identifier text Nothing)

-- | Creates a BV that produces the following vhdl:
--
-- @
--    std_logic_vector(resize(ARG, Size))
-- @
pureToBVResized
  :: Backend backend
  => Identifier
  -- ^ desired name
  -> Int
  -- ^ Size (n)
  -> TExpr
  -- ^ ARG
  -> State (BlockState backend) TExpr
  -- ^ std_logic_vector(resize(ARG, Size))
pureToBVResized nm n arg = do
  arg' <- toIdentifier' nm arg
  -- This is very hard coded and hacky
  let text = "std_logic_vector(resize(" <> arg' <> ", " <> showt n <> "))"
  assign nm $ TExpr (BitVector n) (Identifier text Nothing)

-- | Allows assignment of a port to be "open"
open
  :: Backend backend
  => HWType
  -> State (BlockState backend) TExpr
open hwType = pure $ TExpr hwType (Identifier "open" Nothing)
