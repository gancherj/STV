-- Type system for language.
module Prot.Lang.Types where

import Data.Typeable
import Data.Type.Equality
import Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.Ctx
import Data.SBV
import Data.Data
import qualified Data.Parameterized.TH.GADT as U
import Data.Parameterized.NatRepr
import GHC.TypeLits

data BaseType where
    BaseInt :: BaseType
    BaseNat :: Nat -> BaseType
    BaseBool :: BaseType
    BaseUnit :: BaseType

data BaseTypeRepr (tp :: BaseType) :: * where
    BaseIntRepr :: BaseTypeRepr BaseInt
    BaseNatRepr :: NatRepr w -> BaseTypeRepr (BaseNat w)
    BaseBoolRepr :: BaseTypeRepr BaseBool
    BaseUnitRepr :: BaseTypeRepr BaseUnit

data Type where
    BaseToType :: BaseType -> Type
    TTuple :: Ctx Type -> Type
    TList :: Nat -> Type -> Type

type BaseToType = 'BaseToType
type TInt = BaseToType BaseInt
type TNat w = BaseToType (BaseNat w)
type TBool = BaseToType BaseBool
type TTuple = 'TTuple
type TUnit = BaseToType BaseUnit
type TList w = 'TList w

data TypeRepr (t :: Type) :: * where
    TIntRepr :: TypeRepr TInt
    TNatRepr :: NatRepr w -> TypeRepr (TNat w)
    TBoolRepr :: TypeRepr TBool
    TUnitRepr :: TypeRepr TUnit
    TListRepr :: NatRepr w -> !(TypeRepr tp) -> TypeRepr (TList w tp)
    TTupleRepr :: !(CtxRepr ctx) -> TypeRepr (TTuple ctx)


type CtxRepr = Ctx.Assignment TypeRepr
type BaseCtxRepr = Ctx.Assignment BaseTypeRepr

$( return [] )

instance Show (TypeRepr tp) where
    show TUnitRepr = "TUnit"
    show (TNatRepr w) = "TNat"
    show TIntRepr = "TInt"
    show TBoolRepr = "TBool"
    show (TTupleRepr t) = show t
    show (TListRepr w t) = "[" ++ (show t) ++ "]"


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
         (U.TypeApp (U.ConType [t|CtxRepr|]) U.AnyType, [|testEquality|]),
         (U.TypeApp (U.ConType [t|NatRepr|]) U.AnyType, [|testEquality|]),
         (U.TypeApp (U.ConType [t|TypeRepr|]) U.AnyType, [|testEquality|])])
 --        (U.TypeApp (U.TypeApp (U.ConType [t|NatRepr|]) U.AnyType) (U.TypeApp (U.ConType [t|TypeRepr|]) U.AnyType), [|testEquality|])])



instance TestEquality BaseTypeRepr where
    testEquality = $(U.structuralTypeEquality [t|BaseTypeRepr|]
        [(U.ConType [t|BaseInt|], [|testEquality|]),
        (U.ConType [t|BaseBool|], [|testEquality|]),
        (U.TypeApp (U.ConType [t|NatRepr|]) U.AnyType, [|testEquality|]),
        (U.ConType [t|BaseUnit|], [|testEquality|])])

instance Show (BaseTypeRepr tp) where
    show (BaseIntRepr) = "Int"
    show (BaseNatRepr w) = "Nat"
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
      TNatRepr w -> AsBaseType (BaseNatRepr w)
      TUnitRepr -> AsBaseType BaseUnitRepr
      _ -> NotBaseType



class TypeOf (k :: Type -> *) where
    typeOf :: forall tp. k tp -> TypeRepr tp

class GetCtx (k :: Type -> *) where
    getCtx :: forall ctx. k (TTuple ctx) -> CtxRepr ctx
