module Prot.Lang.Types where

import Data.Typeable
import Data.Type.Equality
import Data.Parameterized.Classes

data Type where
    TInt :: Type
    TBool :: Type

type TInt = 'TInt
type TBool = 'TBool

data TypeRepr (t :: Type) :: * where
    TIntRepr :: TypeRepr TInt
    TBoolRepr :: TypeRepr TBool
    
instance KnownRepr TypeRepr TInt where
    knownRepr = TIntRepr

instance KnownRepr TypeRepr TBool where
    knownRepr = TBoolRepr

instance TestEquality TypeRepr where
    testEquality TIntRepr TIntRepr = Just Refl
    testEquality TBoolRepr TBoolRepr = Just Refl
    testEquality _ _ = Nothing

instance Show (TypeRepr TInt) where
    show t = "Int"

instance Show (TypeRepr TBool) where
    show t = "bool"
