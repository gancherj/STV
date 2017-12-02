module Prot.Lang.Types where

import Data.Typeable
import Data.Type.Equality
import Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.Ctx
import Data.SBV
import Data.Data

data TypeableType (a :: *) where
    TypeableType :: (Typeable a, Eq a, Ord a, Show a, Read a, Data a, SymWord a, HasKind a, SatModel a, EqSymbolic a) => TypeableType a

data TypeableValue (a :: *) where
    TypeableValue :: (Typeable a, Eq a, Ord a, Show a, Read a, Data a, SymWord a, HasKind a, SatModel a, EqSymbolic a) => a -> TypeableValue a

typeableTypeOfValue :: TypeableValue a -> TypeableType a
typeableTypeOfValue (TypeableValue a) = TypeableType

instance Show (TypeableType x) where
    show TypeableType = show $ typeRep (Proxy :: Proxy x)

instance Show (TypeableValue x) where
    show (TypeableValue a) = show a

data BaseType where
    BaseInt :: BaseType
    BaseBool :: BaseType

data BaseTypeRepr (tp :: BaseType) :: * where
    BaseIntRepr :: BaseTypeRepr BaseInt
    BaseBoolRepr :: BaseTypeRepr BaseBool

data Type where
    BaseToType :: BaseType -> Type
    TTuple :: Ctx Type -> Type
    TEnum :: t -> Type

type BaseToType = 'BaseToType
type TInt = BaseToType BaseInt
type TBool = BaseToType BaseBool
type TTuple = 'TTuple
type TEnum = 'TEnum

data TypeRepr (t :: Type) :: * where
    TIntRepr :: TypeRepr TInt
    TBoolRepr :: TypeRepr TBool
    TTupleRepr :: !(Ctx.Assignment TypeRepr ctx) -> TypeRepr (TTuple ctx)
    TEnumRepr :: TypeableType a -> TypeRepr (TEnum a)


type CtxRepr = Ctx.Assignment TypeRepr
type BaseCtxRepr = Ctx.Assignment BaseTypeRepr

instance Show (TypeRepr tp) where
    show TIntRepr = "TInt"
    show TBoolRepr = "TBool"
    show (TTupleRepr t) = show t
    show (TEnumRepr t) = show t 


instance ShowF TypeRepr

instance KnownRepr TypeRepr TInt where
    knownRepr = TIntRepr

instance KnownRepr TypeRepr TBool where
    knownRepr = TBoolRepr

type KnownCtx f = KnownRepr (Ctx.Assignment f)

instance KnownCtx TypeRepr ctx => KnownRepr TypeRepr (TTuple ctx) where
    knownRepr = TTupleRepr knownRepr

instance (Eq a, Ord a, Typeable a, Show a, Read a, Data a, SymWord a, HasKind a, SatModel a, EqSymbolic a) => KnownRepr TypeRepr (TEnum a) where
    knownRepr = TEnumRepr TypeableType

instance TestEquality TypeRepr where
    testEquality TIntRepr TIntRepr = Just Refl
    testEquality TBoolRepr TBoolRepr = Just Refl
    testEquality (TTupleRepr t) (TTupleRepr t') = 
        case (testEquality t t') of
          Just Refl -> Just Refl
          Nothing -> Nothing
    testEquality _ _ = Nothing


instance TestEquality BaseTypeRepr where
    testEquality BaseIntRepr BaseIntRepr = Just Refl
    testEquality BaseBoolRepr BaseBoolRepr = Just Refl
    testEquality _ _ = Nothing

instance Show (BaseTypeRepr tp) where
    show (BaseIntRepr) = "Int"
    show (BaseBoolRepr) = "Bool"

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
      _ -> NotBaseType

