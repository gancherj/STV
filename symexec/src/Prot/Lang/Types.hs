module Prot.Lang.Types where

import Data.Typeable
import Data.Type.Equality
import Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.Ctx
import Data.SBV
import Data.Data
import qualified Data.Parameterized.TH.GADT as U

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

type BaseToType = 'BaseToType
type TInt = BaseToType BaseInt
type TBool = BaseToType BaseBool
type TTuple = 'TTuple
type TUnit = BaseToType BaseUnit

data TypeRepr (t :: Type) :: * where
    TIntRepr :: TypeRepr TInt
    TBoolRepr :: TypeRepr TBool
    TUnitRepr :: TypeRepr TUnit
    TTupleRepr :: !(CtxRepr ctx) -> TypeRepr (TTuple ctx)


type CtxRepr = Ctx.Assignment TypeRepr
type BaseCtxRepr = Ctx.Assignment BaseTypeRepr

$( return [] )

instance Show (TypeRepr tp) where
    show TUnitRepr = "TUnit"
    show TIntRepr = "TInt"
    show TBoolRepr = "TBool"
    show (TTupleRepr t) = show t


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


instance TestEquality TypeRepr where
    testEquality = $(U.structuralTypeEquality [t|TypeRepr|]
        [(U.TypeApp (U.ConType [t|BaseTypeRepr|]) U.AnyType, [|testEquality|]),
         (U.TypeApp (U.ConType [t|CtxRepr|]) U.AnyType, [|testEquality|])])



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

