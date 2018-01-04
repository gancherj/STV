module Prot.Lang.Types where

import Data.Typeable
import Data.Type.Equality
import Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.Ctx
import Data.SBV
import Data.Data

data TypeableType (a :: *) where
    TypeableType :: (Typeable a, Eq a, Ord a, Show a, Read a, Data a, SymWord a, HasKind a, SatModel a) => TypeableType a

instance TestEquality TypeableType where
    testEquality TypeableType TypeableType = eqT

data TypeableValue (a :: *) where
    TypeableValue :: (Typeable a, Eq a, Ord a, Show a, Read a, Data a, SymWord a, HasKind a, SatModel a) => a -> TypeableValue a

typeableTypeOfValue :: TypeableValue a -> TypeableType a
typeableTypeOfValue (TypeableValue a) = TypeableType

instance Show (TypeableType x) where
    show TypeableType = show $ typeRep (Proxy :: Proxy x)

instance Show (TypeableValue x) where
    show (TypeableValue a) = show a

data BaseType where
    BaseInt :: BaseType
    BaseBool :: BaseType
    BaseUnit :: BaseType

data BaseTypeRepr (tp :: BaseType) :: * where
    BaseIntRepr :: BaseTypeRepr BaseInt
    BaseBoolRepr :: BaseTypeRepr BaseBool
    BaseUnitRepr :: BaseTypeRepr BaseUnit

data Type where
    BaseToType :: BaseType -> Type
    TTuple :: Ctx Type -> Type
    TEnum :: t -> Type
    TSum :: Type -> Type -> Type

type BaseToType = 'BaseToType
type TInt = BaseToType BaseInt
type TBool = BaseToType BaseBool
type TTuple = 'TTuple
type TEnum = 'TEnum
type TUnit = BaseToType BaseUnit

data TypeRepr (t :: Type) :: * where
    TIntRepr :: TypeRepr TInt
    TBoolRepr :: TypeRepr TBool
    TUnitRepr :: TypeRepr TUnit
    TTupleRepr :: !(Ctx.Assignment TypeRepr ctx) -> TypeRepr (TTuple ctx)
    TEnumRepr :: TypeableType a -> TypeRepr (TEnum a)
    TSumRepr :: TypeRepr a -> TypeRepr b -> TypeRepr (TSum a b)


type CtxRepr = Ctx.Assignment TypeRepr
type BaseCtxRepr = Ctx.Assignment BaseTypeRepr

instance Show (TypeRepr tp) where
    show TUnitRepr = "TUnit"
    show TIntRepr = "TInt"
    show TBoolRepr = "TBool"
    show (TTupleRepr t) = show t
    show (TEnumRepr t) = show t 
    show (TSumRepr t1 t2) = (show t1) ++ " + " ++ (show t2)


instance ShowF TypeRepr

instance KnownRepr TypeRepr TInt where
    knownRepr = TIntRepr

instance KnownRepr TypeRepr TBool where
    knownRepr = TBoolRepr

instance KnownRepr TypeRepr TUnit where
    knownRepr = TUnitRepr


type KnownCtx f = KnownRepr (Ctx.Assignment f)

instance KnownCtx TypeRepr ctx => KnownRepr TypeRepr (TTuple ctx) where
    knownRepr = TTupleRepr knownRepr

instance (Eq a, Ord a, Typeable a, Show a, Read a, Data a, SymWord a, HasKind a, SatModel a) => KnownRepr TypeRepr (TEnum a) where
    knownRepr = TEnumRepr TypeableType

instance TestEquality TypeRepr where
    testEquality TUnitRepr TUnitRepr = Just Refl
    testEquality TIntRepr TIntRepr = Just Refl
    testEquality TBoolRepr TBoolRepr = Just Refl
    testEquality (TTupleRepr t) (TTupleRepr t') = 
        case (testEquality t t') of
          Just Refl -> Just Refl
          Nothing -> Nothing
    testEquality (TEnumRepr t) (TEnumRepr t') = 
        case (testEquality t t') of
          Just Refl -> Just Refl
          Nothing -> Nothing
    testEquality (TSumRepr t1 t2) (TSumRepr t1' t2') =
        case (testEquality t1 t1', testEquality t2 t2') of
          (Just Refl, Just Refl) -> Just Refl
          _ -> Nothing
    testEquality _ _ = Nothing


instance TestEquality BaseTypeRepr where
    testEquality BaseIntRepr BaseIntRepr = Just Refl
    testEquality BaseBoolRepr BaseBoolRepr = Just Refl
    testEquality BaseUnitRepr BaseUnitRepr = Just Refl
    testEquality _ _ = Nothing

instance Show (BaseTypeRepr tp) where
    show (BaseIntRepr) = "Int"
    show (BaseBoolRepr) = "Bool"
    show (BaseUnitRepr) = "Unit"

instance ShowF BaseTypeRepr where

-- utility functions
--

data AsBaseType tp where
    AsBaseType :: tp ~ BaseToType btp => BaseTypeRepr btp -> AsBaseType tp
    NotBaseType :: AsBaseType tp

asBaseType :: TypeRepr tp -> AsBaseType tp
asBaseType tp =
    case tp of
      TBoolRepr -> AsBaseType BaseBoolRepr
      TIntRepr -> AsBaseType BaseIntRepr
      TUnitRepr -> AsBaseType BaseUnitRepr
      _ -> NotBaseType

