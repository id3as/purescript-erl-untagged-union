module Erl.Untagged.Union
  ( Choices
  , Nil
  , Term
  , Item
  , Union
  , type (|+|)
  , Apply
  , type (|$|)
  , inj
  , prj
  , on
  , case_
  , term_
  , ChoicesWithType
  , NilWithType
  , TermWithType
  , ItemWithType
  , class ValidChoices
  , class IsSupportedMessage
  , class IsInChoices
  , class RuntimeType
  , class GatherTypes
  , class AddRuntimeType
  , class IsAmbiguous
  , class IsAmbiguous'
  , class IsAmbiguousType
  , class RuntimeTypeMatch
  , class HasNoConversions
  , class HasNoConversionsRT
  , isMatch
  , WasMatch
  , class MaybeFail
  , class CanShow
  , showItem
  , class CanEq
  , eqItem
  , RTTerm
  , RTWildcard
  , RTOption
  , RTAtom
  , RTLiteralAtom
  , RTLiteralAtomConvert
  , RTInt
  , RTString
  , RTBinary
  , RTList
  , RTNumber
  , RTTuple1
  , RTTuple2
  , RTTuple3
  , RTTuple4
  , RTTuple5
  , RTTuple6
  , RTTuple7
  , RTTuple8
  , RTTuple9
  , RTTuple10
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Symbol (class IsSymbol, reflectSymbol)
import Erl.Atom (Atom, atom)
import Erl.Atom.Symbol as AtomSymbol
import Erl.Data.Binary (Binary)
import Erl.Data.List (List)
import Erl.Data.Tuple (Tuple1, Tuple2, Tuple3, Tuple4, Tuple5, Tuple6, Tuple7, Tuple8, Tuple9, Tuple10, tuple1, tuple2, tuple3, tuple4, tuple5, tuple6, tuple7, tuple8, tuple9, tuple10, uncurry1, uncurry2, uncurry3, uncurry4, uncurry5, uncurry6, uncurry7, uncurry8, uncurry9, uncurry10)
import Foreign (Foreign, unsafeToForeign)
import Partial.Unsafe (unsafeCrashWith)
import Prim.Boolean (False, True)
import Prim.TypeError as TE
import Type.Data.Boolean (class And)
import Type.Prelude (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)

data Choices

foreign import data Nil :: Choices
foreign import data Term :: Choices
foreign import data Item :: Type -> Choices -> Choices

data Union :: Choices -> Type
data Union choices
  = Union

infixr 7 type Item as |+|

type Apply :: forall k1 k2. (k1 -> k2) -> k1 -> k2
type Apply a b
  = a b
infixr 1 type Apply as |$|

inj ::
  forall a choices rem.
  IsInChoices a choices rem =>
  ValidChoices choices =>
  a -> Union choices
inj = unsafeCoerce

prj ::
  forall a choices d rem.
  IsInChoices a choices rem =>
  RuntimeType a d =>
  RuntimeTypeMatch (Item a Nil) d =>
  Union choices -> Maybe a
prj union = do
  case isMatch (Proxy :: _ (Item a Nil)) (Proxy :: _ d) (unsafeToForeign union) of
    Match -> Just $ unsafeCoerce union
    Converted converted -> Just $ unsafeCoerce converted
    NoMatch -> Nothing

on ::
  forall a x d choices rem.
  IsInChoices a choices rem =>
  RuntimeType a d =>
  RuntimeTypeMatch (Item a Nil) d =>
  (a -> x) ->
  (Union rem -> x) ->
  Union choices ->
  x
on f g u =
  case prj u of
    Just a -> f a
    Nothing -> g (rem u)
  where
  rem :: Union choices -> Union rem
  rem = unsafeCoerce

case_ :: forall x. Union Nil -> x
case_ _ = do
  unsafeCrashWith "unmatched data in union"

term_ :: forall x. (Foreign -> x) -> Union Term -> x
term_ f u = f (unsafeToForeign u)

------------------------------------------------------------------------------
-- RuntimeTypeMatch - check a runtime type
data WasMatch
  = Match
  | Converted Foreign
  | NoMatch

class RuntimeTypeMatch :: Choices -> RTTerm -> Constraint
class RuntimeTypeMatch choices d where
  isMatch :: Proxy choices -> Proxy d -> Foreign -> WasMatch

instance evaluateRuntimeTypeWildcard :: RuntimeTypeMatch choices RTWildcard where
  isMatch _ _ _ = Match

instance evaluateRuntimeTypeString :: RuntimeTypeMatch choices RTString where
  isMatch _ _ = matchTest (const Match) <<< isBinary

instance evaluateRuntimeTypeInt :: RuntimeTypeMatch choices RTInt where
  isMatch _ _ = matchTest (const Match) <<< isInt

instance evaluateRuntimeTypeAtom :: RuntimeTypeMatch choices RTAtom where
  isMatch _ _ = matchTest (const Match) <<< isAtom

instance evaluateRuntimeTypeBinary :: RuntimeTypeMatch choices RTBinary where
  isMatch _ _ = matchTest (const Match) <<< isBinary

instance evaluateRuntimeTypeList :: RuntimeTypeMatch choices RTList where
  isMatch _ _ = matchTest (const Match) <<< isList

instance evaluateRuntimeTypeLiteralAtom ::
  (IsSymbol sym) =>
  RuntimeTypeMatch choices (RTLiteralAtom sym) where
  isMatch _ _ = matchTest (const Match) <<< isLiteralAtom (reflectSymbol (Proxy :: _ sym))

instance evaluateRuntimeTypeLiteralAtomConvert ::
  ( IsSymbol sym
  , IsSymbol convSym
  ) =>
  RuntimeTypeMatch choices (RTLiteralAtomConvert sym convSym) where
  isMatch _ _ = matchTest (\_ -> Converted (unsafeToForeign $ atom (reflectSymbol (Proxy :: _ convSym)))) <<< isLiteralAtom (reflectSymbol (Proxy :: _ sym))

instance evaluateRuntimeTypeOption ::
  ( RuntimeTypeMatch choices a
  , RuntimeTypeMatch choices b
  ) =>
  RuntimeTypeMatch choices (RTOption a b) where
  isMatch choices _ val = case isMatch choices (Proxy :: _ a) val of
    Match -> Match
    c@(Converted _) -> c
    NoMatch -> isMatch choices (Proxy :: _ b) val

instance evaluateRuntimeTypeTuple1 ::
  ( RuntimeTypeMatch choices a
  ) =>
  RuntimeTypeMatch choices (RTTuple1 a) where
  isMatch choices _ val = matchTest (\_ -> uncurry1 recurse1 (unsafeCoerce val)) $ isTuple1 val
    where
    recurse1 val1 =
      matchMap (\_ -> resolve false val1) (\val1' -> resolve true val1') $ isMatch choices (Proxy :: _ a) val1

    resolve false _ = Match
    resolve true val1 = Converted $ unsafeToForeign $ tuple1 val1

instance evaluateRuntimeTypeTuple2 ::
  ( RuntimeTypeMatch choices a
  , RuntimeTypeMatch choices b
  ) =>
  RuntimeTypeMatch choices (RTTuple2 a b) where
  isMatch choices _ val = matchTest (\_ -> uncurry2 recurse1 (unsafeCoerce val)) $ isTuple2 val
    where
    recurse1 val1 val2 =
      matchMap (\_ -> recurse2 false val1 val2) (\val1' -> recurse2 true val1' val2) $ isMatch choices (Proxy :: _ a) val1

    recurse2 conv val1 val2 =
      matchMap (\_ -> resolve conv val1 val2) (\val2' -> resolve true val1 val2') $ isMatch choices (Proxy :: _ b) val2

    resolve false _ _ = Match
    resolve true val1 val2 = Converted $ unsafeToForeign $ tuple2 val1 val2

instance evaluateRuntimeTypeTuple3 ::
  ( RuntimeTypeMatch choices a
  , RuntimeTypeMatch choices b
  , RuntimeTypeMatch choices c
  ) =>
  RuntimeTypeMatch choices (RTTuple3 a b c) where
  isMatch choices _ val = matchTest (\_ -> uncurry3 recurse1 (unsafeCoerce val)) $ isTuple3 val
    where
    recurse1 val1 val2 val3 =
      matchMap (\_ -> recurse2 false val1 val2 val3) (\val1' -> recurse2 true val1' val2 val3) $ isMatch choices (Proxy :: _ a) val1

    recurse2 conv val1 val2 val3 =
      matchMap (\_ -> recurse3 conv val1 val2 val3) (\val2' -> recurse3 true val1 val2' val3) $ isMatch choices (Proxy :: _ b) val2

    recurse3 conv val1 val2 val3 =
      matchMap (\_ -> resolve conv val1 val2 val3) (\val3' -> resolve true val1 val2 val3') $ isMatch choices (Proxy :: _ c) val3

    resolve false _ _ _ = Match
    resolve true val1 val2 val3 = Converted $ unsafeToForeign $ tuple3 val1 val2 val3

instance evaluateRuntimeTypeTuple4 ::
  ( RuntimeTypeMatch choices a
  , RuntimeTypeMatch choices b
  , RuntimeTypeMatch choices c
  , RuntimeTypeMatch choices d
  ) =>
  RuntimeTypeMatch choices (RTTuple4 a b c d) where
  isMatch choices _ val = matchTest (\_ -> uncurry4 recurse1 (unsafeCoerce val)) $ isTuple4 val
    where
    recurse1 val1 val2 val3 val4 =
      matchMap (\_ -> recurse2 false val1 val2 val3 val4) (\val1' -> recurse2 true val1' val2 val3 val4) $ isMatch choices (Proxy :: _ a) val1

    recurse2 conv val1 val2 val3 val4 =
      matchMap (\_ -> recurse3 conv val1 val2 val3 val4) (\val2' -> recurse3 true val1 val2' val3 val4) $ isMatch choices (Proxy :: _ b) val2

    recurse3 conv val1 val2 val3 val4 =
      matchMap (\_ -> recurse4 conv val1 val2 val3 val4) (\val3' -> recurse4 true val1 val2 val3' val4) $ isMatch choices (Proxy :: _ c) val3

    recurse4 conv val1 val2 val3 val4 =
      matchMap (\_ -> resolve conv val1 val2 val3 val4) (\val4' -> resolve true val1 val2 val3 val4') $ isMatch choices (Proxy :: _ d) val4

    resolve false _ _ _ _ = Match
    resolve true val1 val2 val3 val4 = Converted $ unsafeToForeign $ tuple4 val1 val2 val3 val4

instance evaluateRuntimeTypeTuple5 ::
  ( RuntimeTypeMatch choices a
  , RuntimeTypeMatch choices b
  , RuntimeTypeMatch choices c
  , RuntimeTypeMatch choices d
  , RuntimeTypeMatch choices e
  ) =>
  RuntimeTypeMatch choices (RTTuple5 a b c d e) where
  isMatch choices _ val = matchTest (\_ -> uncurry5 recurse1 (unsafeCoerce val)) $ isTuple5 val
    where
    recurse1 val1 val2 val3 val4 val5 =
      matchMap (\_ -> recurse2 false val1 val2 val3 val4 val5) (\val1' -> recurse2 true val1' val2 val3 val4 val5) $ isMatch choices (Proxy :: _ a) val1

    recurse2 conv val1 val2 val3 val4 val5 =
      matchMap (\_ -> recurse3 conv val1 val2 val3 val4 val5) (\val2' -> recurse3 true val1 val2' val3 val4 val5) $ isMatch choices (Proxy :: _ b) val2

    recurse3 conv val1 val2 val3 val4 val5 =
      matchMap (\_ -> recurse4 conv val1 val2 val3 val4 val5) (\val3' -> recurse4 true val1 val2 val3' val4 val5) $ isMatch choices (Proxy :: _ c) val3

    recurse4 conv val1 val2 val3 val4 val5 =
      matchMap (\_ -> recurse5 conv val1 val2 val3 val4 val5) (\val4' -> recurse5 true val1 val2 val3 val4' val5) $ isMatch choices (Proxy :: _ d) val4

    recurse5 conv val1 val2 val3 val4 val5 =
      matchMap (\_ -> resolve conv val1 val2 val3 val4 val5) (\val5' -> resolve true val1 val2 val3 val4 val5') $ isMatch choices (Proxy :: _ e) val5

    resolve false _ _ _ _ _ = Match
    resolve true val1 val2 val3 val4 val5 = Converted $ unsafeToForeign $ tuple5 val1 val2 val3 val4 val5

instance evaluateRuntimeTypeTuple6 ::
  ( RuntimeTypeMatch choices a
  , RuntimeTypeMatch choices b
  , RuntimeTypeMatch choices c
  , RuntimeTypeMatch choices d
  , RuntimeTypeMatch choices e
  , RuntimeTypeMatch choices f
  ) =>
  RuntimeTypeMatch choices (RTTuple6 a b c d e f) where
  isMatch choices _ val = matchTest (\_ -> uncurry6 recurse1 (unsafeCoerce val)) $ isTuple6 val
    where
    recurse1 val1 val2 val3 val4 val5 val6 =
      matchMap (\_ -> recurse2 false val1 val2 val3 val4 val5 val6) (\val1' -> recurse2 true val1' val2 val3 val4 val5 val6) $ isMatch choices (Proxy :: _ a) val1

    recurse2 conv val1 val2 val3 val4 val5 val6 =
      matchMap (\_ -> recurse3 conv val1 val2 val3 val4 val5 val6) (\val2' -> recurse3 true val1 val2' val3 val4 val5 val6) $ isMatch choices (Proxy :: _ b) val2

    recurse3 conv val1 val2 val3 val4 val5 val6 =
      matchMap (\_ -> recurse4 conv val1 val2 val3 val4 val5 val6) (\val3' -> recurse4 true val1 val2 val3' val4 val5 val6) $ isMatch choices (Proxy :: _ c) val3

    recurse4 conv val1 val2 val3 val4 val5 val6 =
      matchMap (\_ -> recurse5 conv val1 val2 val3 val4 val5 val6) (\val4' -> recurse5 true val1 val2 val3 val4' val5 val6) $ isMatch choices (Proxy :: _ d) val4

    recurse5 conv val1 val2 val3 val4 val5 val6 =
      matchMap (\_ -> recurse6 conv val1 val2 val3 val4 val5 val6) (\val5' -> recurse6 true val1 val2 val3 val4 val5' val6) $ isMatch choices (Proxy :: _ e) val5

    recurse6 conv val1 val2 val3 val4 val5 val6 =
      matchMap (\_ -> resolve conv val1 val2 val3 val4 val5 val6) (\val6' -> resolve true val1 val2 val3 val4 val5 val6') $ isMatch choices (Proxy :: _ f) val6

    resolve false _ _ _ _ _ _ = Match
    resolve true val1 val2 val3 val4 val5 val6 = Converted $ unsafeToForeign $ tuple6 val1 val2 val3 val4 val5 val6

instance evaluateRuntimeTypeTuple7 ::
  ( RuntimeTypeMatch choices a
  , RuntimeTypeMatch choices b
  , RuntimeTypeMatch choices c
  , RuntimeTypeMatch choices d
  , RuntimeTypeMatch choices e
  , RuntimeTypeMatch choices f
  , RuntimeTypeMatch choices g
  ) =>
  RuntimeTypeMatch choices (RTTuple7 a b c d e f g) where
  isMatch choices _ val = matchTest (\_ -> uncurry7 recurse1 (unsafeCoerce val)) $ isTuple7 val
    where
    recurse1 val1 val2 val3 val4 val5 val6 val7 =
      matchMap (\_ -> recurse2 false val1 val2 val3 val4 val5 val6 val7) (\val1' -> recurse2 true val1' val2 val3 val4 val5 val6 val7) $ isMatch choices (Proxy :: _ a) val1

    recurse2 conv val1 val2 val3 val4 val5 val6 val7 =
      matchMap (\_ -> recurse3 conv val1 val2 val3 val4 val5 val6 val7) (\val2' -> recurse3 true val1 val2' val3 val4 val5 val6 val7) $ isMatch choices (Proxy :: _ b) val2

    recurse3 conv val1 val2 val3 val4 val5 val6 val7 =
      matchMap (\_ -> recurse4 conv val1 val2 val3 val4 val5 val6 val7) (\val3' -> recurse4 true val1 val2 val3' val4 val5 val6 val7) $ isMatch choices (Proxy :: _ c) val3

    recurse4 conv val1 val2 val3 val4 val5 val6 val7 =
      matchMap (\_ -> recurse5 conv val1 val2 val3 val4 val5 val6 val7) (\val4' -> recurse5 true val1 val2 val3 val4' val5 val6 val7) $ isMatch choices (Proxy :: _ d) val4

    recurse5 conv val1 val2 val3 val4 val5 val6 val7 =
      matchMap (\_ -> recurse6 conv val1 val2 val3 val4 val5 val6 val7) (\val5' -> recurse6 true val1 val2 val3 val4 val5' val6 val7) $ isMatch choices (Proxy :: _ e) val5

    recurse6 conv val1 val2 val3 val4 val5 val6 val7 =
      matchMap (\_ -> recurse7 conv val1 val2 val3 val4 val5 val6 val7) (\val6' -> recurse7 true val1 val2 val3 val4 val5 val6' val7) $ isMatch choices (Proxy :: _ f) val6

    recurse7 conv val1 val2 val3 val4 val5 val6 val7 =
      matchMap (\_ -> resolve conv val1 val2 val3 val4 val5 val6 val7) (\val7' -> resolve true val1 val2 val3 val4 val5 val6 val7') $ isMatch choices (Proxy :: _ g) val7

    resolve false _ _ _ _ _ _ _ = Match
    resolve true val1 val2 val3 val4 val5 val6 val7 = Converted $ unsafeToForeign $ tuple7 val1 val2 val3 val4 val5 val6 val7

instance evaluateRuntimeTypeTuple8 ::
  ( RuntimeTypeMatch choices a
  , RuntimeTypeMatch choices b
  , RuntimeTypeMatch choices c
  , RuntimeTypeMatch choices d
  , RuntimeTypeMatch choices e
  , RuntimeTypeMatch choices f
  , RuntimeTypeMatch choices g
  , RuntimeTypeMatch choices h
  ) =>
  RuntimeTypeMatch choices (RTTuple8 a b c d e f g h) where
  isMatch choices _ val = matchTest (\_ -> uncurry8 recurse1 (unsafeCoerce val)) $ isTuple8 val
    where
    recurse1 val1 val2 val3 val4 val5 val6 val7 val8 =
      matchMap (\_ -> recurse2 false val1 val2 val3 val4 val5 val6 val7 val8) (\val1' -> recurse2 true val1' val2 val3 val4 val5 val6 val7 val8) $ isMatch choices (Proxy :: _ a) val1

    recurse2 conv val1 val2 val3 val4 val5 val6 val7 val8 =
      matchMap (\_ -> recurse3 conv val1 val2 val3 val4 val5 val6 val7 val8) (\val2' -> recurse3 true val1 val2' val3 val4 val5 val6 val7 val8) $ isMatch choices (Proxy :: _ b) val2

    recurse3 conv val1 val2 val3 val4 val5 val6 val7 val8 =
      matchMap (\_ -> recurse4 conv val1 val2 val3 val4 val5 val6 val7 val8) (\val3' -> recurse4 true val1 val2 val3' val4 val5 val6 val7 val8) $ isMatch choices (Proxy :: _ c) val3

    recurse4 conv val1 val2 val3 val4 val5 val6 val7 val8 =
      matchMap (\_ -> recurse5 conv val1 val2 val3 val4 val5 val6 val7 val8) (\val4' -> recurse5 true val1 val2 val3 val4' val5 val6 val7 val8) $ isMatch choices (Proxy :: _ d) val4

    recurse5 conv val1 val2 val3 val4 val5 val6 val7 val8 =
      matchMap (\_ -> recurse6 conv val1 val2 val3 val4 val5 val6 val7 val8) (\val5' -> recurse6 true val1 val2 val3 val4 val5' val6 val7 val8) $ isMatch choices (Proxy :: _ e) val5

    recurse6 conv val1 val2 val3 val4 val5 val6 val7 val8 =
      matchMap (\_ -> recurse7 conv val1 val2 val3 val4 val5 val6 val7 val8) (\val6' -> recurse7 true val1 val2 val3 val4 val5 val6' val7 val8) $ isMatch choices (Proxy :: _ f) val6

    recurse7 conv val1 val2 val3 val4 val5 val6 val7 val8 =
      matchMap (\_ -> recurse8 conv val1 val2 val3 val4 val5 val6 val7 val8) (\val7' -> recurse8 true val1 val2 val3 val4 val5 val6 val7' val8) $ isMatch choices (Proxy :: _ g) val7

    recurse8 conv val1 val2 val3 val4 val5 val6 val7 val8 =
      matchMap (\_ -> resolve conv val1 val2 val3 val4 val5 val6 val7 val8) (\val8' -> resolve true val1 val2 val3 val4 val5 val6 val7 val8') $ isMatch choices (Proxy :: _ h) val8

    resolve false _ _ _ _ _ _ _ _ = Match
    resolve true val1 val2 val3 val4 val5 val6 val7 val8 = Converted $ unsafeToForeign $ tuple8 val1 val2 val3 val4 val5 val6 val7 val8

instance evaluateRuntimeTypeTuple9 ::
  ( RuntimeTypeMatch choices a
  , RuntimeTypeMatch choices b
  , RuntimeTypeMatch choices c
  , RuntimeTypeMatch choices d
  , RuntimeTypeMatch choices e
  , RuntimeTypeMatch choices f
  , RuntimeTypeMatch choices g
  , RuntimeTypeMatch choices h
  , RuntimeTypeMatch choices i
  ) =>
  RuntimeTypeMatch choices (RTTuple9 a b c d e f g h i) where
  isMatch choices _ val = matchTest (\_ -> uncurry9 recurse1 (unsafeCoerce val)) $ isTuple9 val
    where
    recurse1 val1 val2 val3 val4 val5 val6 val7 val8 val9 =
      matchMap (\_ -> recurse2 false val1 val2 val3 val4 val5 val6 val7 val8 val9) (\val1' -> recurse2 true val1' val2 val3 val4 val5 val6 val7 val8 val9) $ isMatch choices (Proxy :: _ a) val1

    recurse2 conv val1 val2 val3 val4 val5 val6 val7 val8 val9 =
      matchMap (\_ -> recurse3 conv val1 val2 val3 val4 val5 val6 val7 val8 val9) (\val2' -> recurse3 true val1 val2' val3 val4 val5 val6 val7 val8 val9) $ isMatch choices (Proxy :: _ b) val2

    recurse3 conv val1 val2 val3 val4 val5 val6 val7 val8 val9 =
      matchMap (\_ -> recurse4 conv val1 val2 val3 val4 val5 val6 val7 val8 val9) (\val3' -> recurse4 true val1 val2 val3' val4 val5 val6 val7 val8 val9) $ isMatch choices (Proxy :: _ c) val3

    recurse4 conv val1 val2 val3 val4 val5 val6 val7 val8 val9 =
      matchMap (\_ -> recurse5 conv val1 val2 val3 val4 val5 val6 val7 val8 val9) (\val4' -> recurse5 true val1 val2 val3 val4' val5 val6 val7 val8 val9) $ isMatch choices (Proxy :: _ d) val4

    recurse5 conv val1 val2 val3 val4 val5 val6 val7 val8 val9 =
      matchMap (\_ -> recurse6 conv val1 val2 val3 val4 val5 val6 val7 val8 val9) (\val5' -> recurse6 true val1 val2 val3 val4 val5' val6 val7 val8 val9) $ isMatch choices (Proxy :: _ e) val5

    recurse6 conv val1 val2 val3 val4 val5 val6 val7 val8 val9 =
      matchMap (\_ -> recurse7 conv val1 val2 val3 val4 val5 val6 val7 val8 val9) (\val6' -> recurse7 true val1 val2 val3 val4 val5 val6' val7 val8 val9) $ isMatch choices (Proxy :: _ f) val6

    recurse7 conv val1 val2 val3 val4 val5 val6 val7 val8 val9 =
      matchMap (\_ -> recurse8 conv val1 val2 val3 val4 val5 val6 val7 val8 val9) (\val7' -> recurse8 true val1 val2 val3 val4 val5 val6 val7' val8 val9) $ isMatch choices (Proxy :: _ g) val7

    recurse8 conv val1 val2 val3 val4 val5 val6 val7 val8 val9 =
      matchMap (\_ -> recurse9 conv val1 val2 val3 val4 val5 val6 val7 val8 val9) (\val8' -> recurse9 true val1 val2 val3 val4 val5 val6 val7 val8' val9) $ isMatch choices (Proxy :: _ h) val8

    recurse9 conv val1 val2 val3 val4 val5 val6 val7 val8 val9 =
      matchMap (\_ -> resolve conv val1 val2 val3 val4 val5 val6 val7 val8 val9) (\val9' -> resolve true val1 val2 val3 val4 val5 val6 val7 val8 val9') $ isMatch choices (Proxy :: _ i) val9

    resolve false _ _ _ _ _ _ _ _ _ = Match
    resolve true val1 val2 val3 val4 val5 val6 val7 val8 val9 = Converted $ unsafeToForeign $ tuple9 val1 val2 val3 val4 val5 val6 val7 val8 val9

instance evaluateRuntimeTypeTuple10 ::
  ( RuntimeTypeMatch choices a
  , RuntimeTypeMatch choices b
  , RuntimeTypeMatch choices c
  , RuntimeTypeMatch choices d
  , RuntimeTypeMatch choices e
  , RuntimeTypeMatch choices f
  , RuntimeTypeMatch choices g
  , RuntimeTypeMatch choices h
  , RuntimeTypeMatch choices i
  , RuntimeTypeMatch choices j
  ) =>
  RuntimeTypeMatch choices (RTTuple10 a b c d e f g h i j) where
  isMatch choices _ val = matchTest (\_ -> uncurry10 recurse1 (unsafeCoerce val)) $ isTuple10 val
    where
    recurse1 val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 =
      matchMap (\_ -> recurse2 false val1 val2 val3 val4 val5 val6 val7 val8 val9 val10) (\val1' -> recurse2 true val1' val2 val3 val4 val5 val6 val7 val8 val9 val10) $ isMatch choices (Proxy :: _ a) val1

    recurse2 conv val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 =
      matchMap (\_ -> recurse3 conv val1 val2 val3 val4 val5 val6 val7 val8 val9 val10) (\val2' -> recurse3 true val1 val2' val3 val4 val5 val6 val7 val8 val9 val10) $ isMatch choices (Proxy :: _ b) val2

    recurse3 conv val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 =
      matchMap (\_ -> recurse4 conv val1 val2 val3 val4 val5 val6 val7 val8 val9 val10) (\val3' -> recurse4 true val1 val2 val3' val4 val5 val6 val7 val8 val9 val10) $ isMatch choices (Proxy :: _ c) val3

    recurse4 conv val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 =
      matchMap (\_ -> recurse5 conv val1 val2 val3 val4 val5 val6 val7 val8 val9 val10) (\val4' -> recurse5 true val1 val2 val3 val4' val5 val6 val7 val8 val9 val10) $ isMatch choices (Proxy :: _ d) val4

    recurse5 conv val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 =
      matchMap (\_ -> recurse6 conv val1 val2 val3 val4 val5 val6 val7 val8 val9 val10) (\val5' -> recurse6 true val1 val2 val3 val4 val5' val6 val7 val8 val9 val10) $ isMatch choices (Proxy :: _ e) val5

    recurse6 conv val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 =
      matchMap (\_ -> recurse7 conv val1 val2 val3 val4 val5 val6 val7 val8 val9 val10) (\val6' -> recurse7 true val1 val2 val3 val4 val5 val6' val7 val8 val9 val10) $ isMatch choices (Proxy :: _ f) val6

    recurse7 conv val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 =
      matchMap (\_ -> recurse8 conv val1 val2 val3 val4 val5 val6 val7 val8 val9 val10) (\val7' -> recurse8 true val1 val2 val3 val4 val5 val6 val7' val8 val9 val10) $ isMatch choices (Proxy :: _ g) val7

    recurse8 conv val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 =
      matchMap (\_ -> recurse9 conv val1 val2 val3 val4 val5 val6 val7 val8 val9 val10) (\val8' -> recurse9 true val1 val2 val3 val4 val5 val6 val7 val8' val9 val10) $ isMatch choices (Proxy :: _ h) val8

    recurse9 conv val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 =
      matchMap (\_ -> recurse10 conv val1 val2 val3 val4 val5 val6 val7 val8 val9 val10) (\val9' -> recurse10 true val1 val2 val3 val4 val5 val6 val7 val8 val9' val10) $ isMatch choices (Proxy :: _ i) val9

    recurse10 conv val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 =
      matchMap (\_ -> resolve conv val1 val2 val3 val4 val5 val6 val7 val8 val9 val10) (\val10' -> resolve true val1 val2 val3 val4 val5 val6 val7 val8 val9 val10') $ isMatch choices (Proxy :: _ j) val10

    resolve false _ _ _ _ _ _ _ _ _ _ = Match
    resolve true val1 val2 val3 val4 val5 val6 val7 val8 val9 val10 = Converted $ unsafeToForeign $ tuple10 val1 val2 val3 val4 val5 val6 val7 val8 val9 val10

foreign import isInt :: Foreign -> Boolean
foreign import isAtom :: Foreign -> Boolean
foreign import isBinary :: Foreign -> Boolean
foreign import isList :: Foreign -> Boolean
foreign import isLiteralAtom :: String -> Foreign -> Boolean
foreign import isTuple1 :: Foreign -> Boolean
foreign import isTuple2 :: Foreign -> Boolean
foreign import isTuple3 :: Foreign -> Boolean
foreign import isTuple4 :: Foreign -> Boolean
foreign import isTuple5 :: Foreign -> Boolean
foreign import isTuple6 :: Foreign -> Boolean
foreign import isTuple7 :: Foreign -> Boolean
foreign import isTuple8 :: Foreign -> Boolean
foreign import isTuple9 :: Foreign -> Boolean
foreign import isTuple10 :: Foreign -> Boolean

matchTest :: (Unit -> WasMatch) -> Boolean -> WasMatch
matchTest _match false = NoMatch
matchTest match true = match unit

matchMap :: (Unit -> WasMatch) -> (Foreign -> WasMatch) -> WasMatch -> WasMatch
matchMap _match _conv NoMatch = NoMatch
matchMap match _conv Match = match unit
matchMap _match conv (Converted val) = conv val

class IsInChoices :: Type -> Choices -> Choices -> Constraint
class IsInChoices item choices rem | item choices -> rem

instance IsInChoices item (Item item tail) tail
else instance
  ( IsInChoices item tail remTail
  ) =>
  IsInChoices item (Item t tail) (Item t remTail)

class IsSupportedMessage :: Type -> Type -> Constraint
class IsSupportedMessage msg1 msg2

instance (IsInChoices msg choices t1) => IsSupportedMessage msg (Union choices)
else instance (HasNoConversions msg) => IsSupportedMessage msg msg

class HasNoConversions :: Type -> Constraint
class HasNoConversions msg

instance HasNoConversions (Union choices)
else instance
  ( RuntimeType msg t
  , HasNoConversionsRT t
  ) =>
  HasNoConversions msg

class HasNoConversionsRT :: RTTerm -> Constraint
class HasNoConversionsRT term

instance
  ( HasNoConversionsRT a
  , HasNoConversionsRT b
  ) =>
  HasNoConversionsRT (RTOption a b)
instance HasNoConversionsRT RTWildcard
instance HasNoConversionsRT RTAtom
instance HasNoConversionsRT (RTLiteralAtom symbol)
instance HasNoConversionsRT RTInt
instance HasNoConversionsRT RTString
instance HasNoConversionsRT RTBinary
instance HasNoConversionsRT RTList
instance HasNoConversionsRT RTNumber
instance
  ( HasNoConversionsRT a
  ) =>
  HasNoConversionsRT (RTTuple1 a)
instance
  ( HasNoConversionsRT a
  , HasNoConversionsRT b
  ) =>
  HasNoConversionsRT (RTTuple2 a b)
instance
  ( HasNoConversionsRT a
  , HasNoConversionsRT b
  , HasNoConversionsRT c
  ) =>
  HasNoConversionsRT (RTTuple3 a b c)
instance
  ( HasNoConversionsRT a
  , HasNoConversionsRT b
  , HasNoConversionsRT c
  , HasNoConversionsRT d
  ) =>
  HasNoConversionsRT (RTTuple4 a b c d)
instance
  ( HasNoConversionsRT a
  , HasNoConversionsRT b
  , HasNoConversionsRT c
  , HasNoConversionsRT d
  , HasNoConversionsRT e
  ) =>
  HasNoConversionsRT (RTTuple5 a b c d e)
instance
  ( HasNoConversionsRT a
  , HasNoConversionsRT b
  , HasNoConversionsRT c
  , HasNoConversionsRT d
  , HasNoConversionsRT e
  , HasNoConversionsRT f
  ) =>
  HasNoConversionsRT (RTTuple6 a b c d e f)
instance
  ( HasNoConversionsRT a
  , HasNoConversionsRT b
  , HasNoConversionsRT c
  , HasNoConversionsRT d
  , HasNoConversionsRT e
  , HasNoConversionsRT f
  , HasNoConversionsRT g
  ) =>
  HasNoConversionsRT (RTTuple7 a b c d e f g)
instance
  ( HasNoConversionsRT a
  , HasNoConversionsRT b
  , HasNoConversionsRT c
  , HasNoConversionsRT d
  , HasNoConversionsRT e
  , HasNoConversionsRT f
  , HasNoConversionsRT g
  , HasNoConversionsRT h
  ) =>
  HasNoConversionsRT (RTTuple8 a b c d e f g h)
instance
  ( HasNoConversionsRT a
  , HasNoConversionsRT b
  , HasNoConversionsRT c
  , HasNoConversionsRT d
  , HasNoConversionsRT e
  , HasNoConversionsRT f
  , HasNoConversionsRT g
  , HasNoConversionsRT h
  , HasNoConversionsRT i
  ) =>
  HasNoConversionsRT (RTTuple9 a b c d e f g h i)
instance
  ( HasNoConversionsRT a
  , HasNoConversionsRT b
  , HasNoConversionsRT c
  , HasNoConversionsRT d
  , HasNoConversionsRT e
  , HasNoConversionsRT f
  , HasNoConversionsRT g
  , HasNoConversionsRT h
  , HasNoConversionsRT i
  , HasNoConversionsRT j
  ) =>
  HasNoConversionsRT (RTTuple10 a b c d e f g h i j)

------------------------------------------------------------------------------
-- RuntimeType - get the description of the runtime type
data RTTerm

foreign import data RTWildcard :: RTTerm
foreign import data RTOption :: RTTerm -> RTTerm -> RTTerm
foreign import data RTAtom :: RTTerm
foreign import data RTLiteralAtom :: Symbol -> RTTerm
foreign import data RTLiteralAtomConvert :: Symbol -> Symbol -> RTTerm
foreign import data RTInt :: RTTerm
foreign import data RTString :: RTTerm
foreign import data RTBinary :: RTTerm
foreign import data RTList :: RTTerm
foreign import data RTNumber :: RTTerm
foreign import data RTTuple1 :: RTTerm -> RTTerm
foreign import data RTTuple2 :: RTTerm -> RTTerm -> RTTerm
foreign import data RTTuple3 :: RTTerm -> RTTerm -> RTTerm -> RTTerm
foreign import data RTTuple4 :: RTTerm -> RTTerm -> RTTerm -> RTTerm -> RTTerm
foreign import data RTTuple5 :: RTTerm -> RTTerm -> RTTerm -> RTTerm -> RTTerm -> RTTerm
foreign import data RTTuple6 :: RTTerm -> RTTerm -> RTTerm -> RTTerm -> RTTerm -> RTTerm -> RTTerm
foreign import data RTTuple7 :: RTTerm -> RTTerm -> RTTerm -> RTTerm -> RTTerm -> RTTerm -> RTTerm -> RTTerm
foreign import data RTTuple8 :: RTTerm -> RTTerm -> RTTerm -> RTTerm -> RTTerm -> RTTerm -> RTTerm -> RTTerm -> RTTerm
foreign import data RTTuple9 :: RTTerm -> RTTerm -> RTTerm -> RTTerm -> RTTerm -> RTTerm -> RTTerm -> RTTerm -> RTTerm -> RTTerm
foreign import data RTTuple10 :: RTTerm -> RTTerm -> RTTerm -> RTTerm -> RTTerm -> RTTerm -> RTTerm -> RTTerm -> RTTerm -> RTTerm -> RTTerm

class RuntimeType :: Type -> RTTerm -> Constraint
class RuntimeType a t | a -> t

instance runtimeTypeAtom :: RuntimeType Atom RTAtom

instance runtimeTypeInt :: RuntimeType Int RTInt

instance runtimeTypeString :: RuntimeType String RTString

instance runtimeTypeBinary :: RuntimeType Binary RTBinary

instance runtimeTypeList :: RuntimeType (List a) RTList

instance runtimeTypeNumber :: RuntimeType Number RTNumber

instance runtimeTypeLiteralAtom :: RuntimeType (AtomSymbol.Atom sym) (RTLiteralAtom sym)

instance runtimeTypeTuple1 :: (RuntimeType a a') => RuntimeType (Tuple1 a) (RTTuple1 a')

instance runtimeTypeTuple2 ::
  ( RuntimeType a a'
  , RuntimeType b b'
  ) =>
  RuntimeType (Tuple2 a b) (RTTuple2 a' b')

instance runtimeTypeTuple3 ::
  ( RuntimeType a a'
  , RuntimeType b b'
  , RuntimeType c c'
  ) =>
  RuntimeType (Tuple3 a b c) (RTTuple3 a' b' c')

instance runtimeTypeTuple4 ::
  ( RuntimeType a a'
  , RuntimeType b b'
  , RuntimeType c c'
  , RuntimeType d d'
  ) =>
  RuntimeType (Tuple4 a b c d) (RTTuple4 a' b' c' d')

instance runtimeTypeTuple5 ::
  ( RuntimeType a a'
  , RuntimeType b b'
  , RuntimeType c c'
  , RuntimeType d d'
  , RuntimeType e e'
  ) =>
  RuntimeType (Tuple5 a b c d e) (RTTuple5 a' b' c' d' e')

instance runtimeTypeTuple6 ::
  ( RuntimeType a a'
  , RuntimeType b b'
  , RuntimeType c c'
  , RuntimeType d d'
  , RuntimeType e e'
  , RuntimeType f f'
  ) =>
  RuntimeType (Tuple6 a b c d e f) (RTTuple6 a' b' c' d' e' f')

instance runtimeTypeTuple7 ::
  ( RuntimeType a a'
  , RuntimeType b b'
  , RuntimeType c c'
  , RuntimeType d d'
  , RuntimeType e e'
  , RuntimeType f f'
  , RuntimeType g g'
  ) =>
  RuntimeType (Tuple7 a b c d e f g) (RTTuple7 a' b' c' d' e' f' g')

instance runtimeTypeTuple8 ::
  ( RuntimeType a a'
  , RuntimeType b b'
  , RuntimeType c c'
  , RuntimeType d d'
  , RuntimeType e e'
  , RuntimeType f f'
  , RuntimeType g g'
  , RuntimeType h h'
  ) =>
  RuntimeType (Tuple8 a b c d e f g h) (RTTuple8 a' b' c' d' e' f' g' h')

instance runtimeTypeTuple9 ::
  ( RuntimeType a a'
  , RuntimeType b b'
  , RuntimeType c c'
  , RuntimeType d d'
  , RuntimeType e e'
  , RuntimeType f f'
  , RuntimeType g g'
  , RuntimeType h h'
  , RuntimeType i i'
  ) =>
  RuntimeType (Tuple9 a b c d e f g h i) (RTTuple9 a' b' c' d' e' f' g' h' i')

instance runtimeTypeTuple10 ::
  ( RuntimeType a a'
  , RuntimeType b b'
  , RuntimeType c c'
  , RuntimeType d d'
  , RuntimeType e e'
  , RuntimeType f f'
  , RuntimeType g g'
  , RuntimeType h h'
  , RuntimeType i i'
  , RuntimeType j j'
  ) =>
  RuntimeType (Tuple10 a b c d e f g h i j) (RTTuple10 a' b' c' d' e' f' g' h' i' j')

------------------------------------------------------------------------------
-- ValidChoices - check that a set of choices has no ambiguity
class ValidChoices :: Choices -> Constraint
class ValidChoices choices

instance validChoices ::
  ( GatherTypes choices choicesWithTypes
  , IsAmbiguous choicesWithTypes
  ) =>
  ValidChoices choices

------------------------------------------------------------------------------
-- GatherTypes - for a set of choices, gather all the RuntimeTypes
data ChoicesWithType

foreign import data NilWithType :: ChoicesWithType
foreign import data TermWithType :: ChoicesWithType
foreign import data ItemWithType :: Type -> RTTerm -> ChoicesWithType -> ChoicesWithType

class GatherTypes :: Choices -> ChoicesWithType -> Constraint
class GatherTypes choices choicesWithType | choices -> choicesWithType

instance gatherTypesNil :: GatherTypes Nil NilWithType

instance gatherTypesTerm :: GatherTypes Term TermWithType

instance gatherTypesCons ::
  ( GatherTypes tail tailWithTypes
  , RuntimeType item itemRuntimeType
  , AddRuntimeType item itemRuntimeType tailWithTypes withTypes
  ) =>
  GatherTypes (Item item tail) withTypes --(ItemWithType item itemRuntimeType tailWithTypes)

class AddRuntimeType :: Type -> RTTerm -> ChoicesWithType -> ChoicesWithType -> Constraint
class AddRuntimeType item rtType initial final | item rtType initial -> final

instance addRuntimeTypeOption ::
  ( AddRuntimeType item option1 initial final'
  , AddRuntimeType item option2 final' final
  ) =>
  AddRuntimeType item (RTOption option1 option2) initial final
else instance addRuntimeTypeOther :: AddRuntimeType item rtType initial (ItemWithType item rtType initial)

------------------------------------------------------------------------------
-- IsAmbiguous - given a set of runtime types, check there are no ambiguities
class IsAmbiguous :: ChoicesWithType -> Constraint
class IsAmbiguous choicesWithType

instance isAmbiguousNil :: IsAmbiguous NilWithType

instance isAmbiguousTerm :: IsAmbiguous TermWithType

instance isAmbiguousCons ::
  ( IsAmbiguous tail
  , IsAmbiguous' item itemRuntimeType tail
  ) =>
  IsAmbiguous (ItemWithType item itemRuntimeType tail)

------------------------------------------------------------------------------
-- IsAmbiguous' - given a runtime type and a list of other runtime types, check there are no ambiguities
class IsAmbiguous' :: Type -> RTTerm -> ChoicesWithType -> Constraint
class IsAmbiguous' toCheck toCheckType types

instance isAmbiguous'Nil :: IsAmbiguous' toCheck toCheckType NilWithType

instance isAmbiguous'Term :: IsAmbiguous' toCheck toCheckType TermWithType

instance isAmbiguous'Cons ::
  ( IsAmbiguousType toCheckType compareType isAmbiguous
  , MaybeFail isAmbiguous toCheck toCheckType compare compareType
  , IsAmbiguous' toCheck toCheckType tail
  ) =>
  IsAmbiguous' toCheck toCheckType (ItemWithType compare compareType tail)

class MaybeFail :: Boolean -> Type -> RTTerm -> Type -> RTTerm -> Constraint
class MaybeFail result toCheck toCheckType compare compareType

instance maybeFailTrue ::
  ( TE.Fail ( TE.Above (TE.Text "Ambiguous Union")
        ( TE.Above (TE.Beside (TE.Quote toCheck) (TE.Beside (TE.Text " : ") (TE.Quote (Proxy toCheckType))))
            (TE.Beside (TE.Quote compare) (TE.Beside (TE.Text " : ") (TE.Quote (Proxy compareType))))
        )
    )
  ) =>
  MaybeFail True toCheck toCheckType compare compareType

instance maybeFailFalse :: MaybeFail False toCheck toCheckType compare compareType

------------------------------------------------------------------------------
-- IsAmbiguousType - essentially a basic apartness tester for a pair of types
class IsAmbiguousType :: RTTerm -> RTTerm -> Boolean -> Constraint
class IsAmbiguousType lhs rhs result | lhs rhs -> result

instance isAmbiguousTypeFailExact ::
  IsAmbiguousType a a True
else instance isAmbiguousTypeFailRTWildcardL ::
  IsAmbiguousType RTWildcard a True
else instance isAmbiguousTypeFailRTWildcardR ::
  IsAmbiguousType a RTWildcard True
else instance isAmbiguousTypeFailAtomLiteralAtomR ::
  IsAmbiguousType RTAtom (RTLiteralAtom sym) True
else instance isAmbiguousTypeFailBinaryStringL ::
  IsAmbiguousType RTBinary RTString True
else instance isAmbiguousTypeFailBinaryStringR ::
  IsAmbiguousType RTString RTBinary True
else instance isAmbiguousTypeFailTuple1 ::
  ( IsAmbiguousType a1 b1 result
  ) =>
  IsAmbiguousType (RTTuple1 a1) (RTTuple1 b1) result
else instance isAmbiguousTypeFailTuple2 ::
  ( IsAmbiguousType a1 b1 aResult
  , IsAmbiguousType a2 b2 bResult
  , And aResult bResult result
  ) =>
  IsAmbiguousType (RTTuple2 a1 a2) (RTTuple2 b1 b2) result
else instance isAmbiguousTypeFailTuple3 ::
  ( IsAmbiguousType a1 b1 aResult
  , IsAmbiguousType a2 b2 bResult
  , IsAmbiguousType a3 b3 cResult
  , And aResult bResult abResult
  , And abResult cResult result
  ) =>
  IsAmbiguousType (RTTuple3 a1 a2 a3) (RTTuple3 b1 b2 b3) result
else instance isAmbiguousTypeFailTuple4 ::
  ( IsAmbiguousType a1 b1 aResult
  , IsAmbiguousType a2 b2 bResult
  , IsAmbiguousType a3 b3 cResult
  , IsAmbiguousType a4 b4 dResult
  , And aResult bResult abResult
  , And abResult cResult abcResult
  , And abcResult dResult result
  ) =>
  IsAmbiguousType (RTTuple4 a1 a2 a3 a4) (RTTuple4 b1 b2 b3 b4) result
else instance isAmbiguousTypeFailTuple5 ::
  ( IsAmbiguousType a1 b1 aResult
  , IsAmbiguousType a2 b2 bResult
  , IsAmbiguousType a3 b3 cResult
  , IsAmbiguousType a4 b4 dResult
  , IsAmbiguousType a5 b5 eResult
  , And aResult bResult abResult
  , And abResult cResult abcResult
  , And abcResult dResult abcdResult
  , And abcdResult eResult result
  ) =>
  IsAmbiguousType (RTTuple5 a1 a2 a3 a4 a5) (RTTuple5 b1 b2 b3 b4 b5) result
else instance isAmbiguousTypeFailTuple6 ::
  ( IsAmbiguousType a1 b1 aResult
  , IsAmbiguousType a2 b2 bResult
  , IsAmbiguousType a3 b3 cResult
  , IsAmbiguousType a4 b4 dResult
  , IsAmbiguousType a5 b5 eResult
  , IsAmbiguousType a6 b6 fResult
  , And aResult bResult abResult
  , And abResult cResult abcResult
  , And abcResult dResult abcdResult
  , And abcdResult eResult abcdeResult
  , And abcdeResult fResult result
  ) =>
  IsAmbiguousType (RTTuple6 a1 a2 a3 a4 a5 a6) (RTTuple6 b1 b2 b3 b4 b5 b6) result
else instance isAmbiguousTypeFailTuple7 ::
  ( IsAmbiguousType a1 b1 aResult
  , IsAmbiguousType a2 b2 bResult
  , IsAmbiguousType a3 b3 cResult
  , IsAmbiguousType a4 b4 dResult
  , IsAmbiguousType a5 b5 eResult
  , IsAmbiguousType a6 b6 fResult
  , IsAmbiguousType a7 b7 gResult
  , And aResult bResult abResult
  , And abResult cResult abcResult
  , And abcResult dResult abcdResult
  , And abcdResult eResult abcdeResult
  , And abcdeResult fResult abcdefResult
  , And abcdefResult gResult result
  ) =>
  IsAmbiguousType (RTTuple7 a1 a2 a3 a4 a5 a6 a7) (RTTuple7 b1 b2 b3 b4 b5 b6 b7) result
else instance isAmbiguousTypeFailTuple8 ::
  ( IsAmbiguousType a1 b1 aResult
  , IsAmbiguousType a2 b2 bResult
  , IsAmbiguousType a3 b3 cResult
  , IsAmbiguousType a4 b4 dResult
  , IsAmbiguousType a5 b5 eResult
  , IsAmbiguousType a6 b6 fResult
  , IsAmbiguousType a7 b7 gResult
  , IsAmbiguousType a8 b8 hResult
  , And aResult bResult abResult
  , And abResult cResult abcResult
  , And abcResult dResult abcdResult
  , And abcdResult eResult abcdeResult
  , And abcdeResult fResult abcdefResult
  , And abcdefResult gResult abcdefgResult
  , And abcdefgResult hResult result
  ) =>
  IsAmbiguousType (RTTuple8 a1 a2 a3 a4 a5 a6 a7 a8) (RTTuple8 b1 b2 b3 b4 b5 b6 b7 b8) result
else instance isAmbiguousTypeFailTuple9 ::
  ( IsAmbiguousType a1 b1 aResult
  , IsAmbiguousType a2 b2 bResult
  , IsAmbiguousType a3 b3 cResult
  , IsAmbiguousType a4 b4 dResult
  , IsAmbiguousType a5 b5 eResult
  , IsAmbiguousType a6 b6 fResult
  , IsAmbiguousType a7 b7 gResult
  , IsAmbiguousType a8 b8 hResult
  , IsAmbiguousType a9 b9 iResult
  , And aResult bResult abResult
  , And abResult cResult abcResult
  , And abcResult dResult abcdResult
  , And abcdResult eResult abcdeResult
  , And abcdeResult fResult abcdefResult
  , And abcdefResult gResult abcdefgResult
  , And abcdefgResult hResult abcdefghResult
  , And abcdefghResult iResult result
  ) =>
  IsAmbiguousType (RTTuple9 a1 a2 a3 a4 a5 a6 a7 a8 a9) (RTTuple9 b1 b2 b3 b4 b5 b6 b7 b8 b9) result
else instance isAmbiguousTypeFailTuple10 ::
  ( IsAmbiguousType a1 b1 aResult
  , IsAmbiguousType a2 b2 bResult
  , IsAmbiguousType a3 b3 cResult
  , IsAmbiguousType a4 b4 dResult
  , IsAmbiguousType a5 b5 eResult
  , IsAmbiguousType a6 b6 fResult
  , IsAmbiguousType a7 b7 gResult
  , IsAmbiguousType a8 b8 hResult
  , IsAmbiguousType a9 b9 iResult
  , IsAmbiguousType a10 b10 jResult
  , And aResult bResult abResult
  , And abResult cResult abcResult
  , And abcResult dResult abcdResult
  , And abcdResult eResult abcdeResult
  , And abcdeResult fResult abcdefResult
  , And abcdefResult gResult abcdefgResult
  , And abcdefgResult hResult abcdefghResult
  , And abcdefghResult iResult abcdefghiResult
  , And abcdefghiResult jResult result
  ) =>
  IsAmbiguousType (RTTuple10 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10) (RTTuple10 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10) result
else instance isAmbiguousTypeOk ::
  IsAmbiguousType a b False

instance show_Union :: (CanShow choices) => Show (Union choices) where
  show union = showItem (Proxy :: _ choices) (unsafeToForeign union)

class CanShow :: Choices -> Constraint
class CanShow choices where
  showItem :: Proxy choices -> Foreign -> String

instance canShowNil :: CanShow Nil where
  showItem _ _ = "invalid"
instance canShowTerm :: CanShow Term where
  showItem _ _ = "unhandled"
instance canShowCons ::
  ( CanShow tail
  , Show item
  , RuntimeType item d
  , RuntimeTypeMatch (Item item tail) d
  ) =>
  CanShow (Item item tail) where
  showItem _ union = case isMatch (Proxy :: _ (Item item tail)) (Proxy :: _ d) union of
    Match -> show ((unsafeCoerce union) :: item)
    Converted converted -> show ((unsafeCoerce converted) :: item)
    NoMatch -> showItem (Proxy :: _ tail) union

instance eq_Union :: (CanEq choices) => Eq (Union choices) where
  eq union1 union2 = eqItem (Proxy :: _ choices) (unsafeToForeign union1) (unsafeToForeign union2)

class CanEq :: Choices -> Constraint
class CanEq choices where
  eqItem :: Proxy choices -> Foreign -> Foreign -> Boolean

instance canEqNil :: CanEq Nil where
  eqItem _ _ _ = false
instance canEqTerm :: CanEq Term where
  eqItem _ _ _ = false
instance canEqCons ::
  ( CanEq tail
  , Eq item
  , RuntimeType item d
  , RuntimeTypeMatch (Item item tail) d
  ) =>
  CanEq (Item item tail) where
  eqItem _ union1 union2 =
    case isMatch (Proxy :: _ (Item item tail)) (Proxy :: _ d) union1 of
      Match ->
        case isMatch (Proxy :: _ (Item item tail)) (Proxy :: _ d) union2 of
          Match ->
            eq ((unsafeCoerce union1) :: item) ((unsafeCoerce union2) :: item)
          Converted converted2 ->
            eq ((unsafeCoerce union1) :: item) ((unsafeCoerce converted2) :: item)
          NoMatch ->
            false
      Converted converted1 ->
        case isMatch (Proxy :: _ (Item item tail)) (Proxy :: _ d) union2 of
          Match ->
            eq ((unsafeCoerce converted1) :: item) ((unsafeCoerce union2) :: item)
          Converted converted2 ->
            eq ((unsafeCoerce converted1) :: item) ((unsafeCoerce converted2) :: item)
          NoMatch ->
            false

      NoMatch -> eqItem (Proxy :: _ tail) union1 union2
