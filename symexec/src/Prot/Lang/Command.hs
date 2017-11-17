
module Prot.Lang.Command where
import Prot.Lang.Types
import Data.Type.Equality
import Prot.Lang.Expr

data Distr tp where
    SymDistr :: String -> TypeRepr tp -> (Expr tp -> [SomeExp] -> [Expr TBool]) -> Distr tp
    UnifInt :: Integer -> Integer -> Distr TInt
    UnifBool :: Distr TBool

ppDistr :: Distr tp -> String
ppDistr (SymDistr x _ _) = x

mkDistr :: String -> TypeRepr tp -> (Expr tp -> [SomeExp] -> [Expr TBool]) -> Distr tp
mkDistr = SymDistr

getConds :: String -> [SomeExp] -> Distr tp -> [Expr TBool]
getConds x es (SymDistr _ tp cs) = cs (mkAtom x tp) es
getConds x [] (UnifInt i1 i2) = 
    let xv = mkAtom x TIntRepr in
    [Expr $ IntLe (Expr $ IntLit i1) xv, Expr $ IntLe xv (Expr $ IntLit i2)]
getConds x [] (UnifBool) = []

instance TypeOf Distr where
    typeOf (SymDistr x t _) = t
    typeOf (UnifInt _ _) = TIntRepr
    typeOf (UnifBool) = TBoolRepr


data Command tp where
    Sampl :: forall tp tp2. String -> Distr tp2 -> [SomeExp] -> Command tp -> Command tp
    Let :: forall tp tp2. String -> Expr tp2 -> Command tp -> Command tp
    Ite :: forall tp. Expr TBool -> Command tp -> Command tp -> Command tp
    Ret :: forall tp. Expr tp -> Command tp

data SomeCommand = forall tp. SomeCommand (TypeRepr tp) (Command tp)


ppCommand :: Command tp -> String
ppCommand (Sampl x d args k) =
    x ++ " <- " ++ (ppDistr d) ++ concatMap ppSomeExp args ++ ";\n" ++ (ppCommand k)
ppCommand (Let x e k) =
    "let " ++ x ++ " = " ++ (ppExpr e) ++ ";\n" ++ (ppCommand k)
ppCommand (Ite b e1 e2) =
    "if " ++ (ppExpr b) ++ " then " ++ (ppCommand e1) ++ " else " ++ (ppCommand e2)
ppCommand (Ret e) = "ret " ++ (ppExpr e)
