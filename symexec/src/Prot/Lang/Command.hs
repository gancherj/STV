
module Prot.Lang.Command where
import Prot.Lang.Types
import Data.Type.Equality
import Prot.Lang.Expr

data Distr tp where
    SymDistr :: String -> TypeRepr tp -> Distr tp
    UnifInt :: Int -> Int -> Distr TInt
    UnifBool :: Distr TBool

ppDistr :: Distr tp -> String
ppDistr (SymDistr x _) = x

instance TypeOf Distr where
    typeOf (SymDistr x t) = t
    typeOf (UnifInt _ _) = TIntRepr
    typeOf (UnifBool) = TBoolRepr


data Command tp where
    Sampl :: forall tp tp2. String -> Distr tp2 -> [SomeExp] -> Command tp -> Command tp
    Let :: forall tp tp2. String -> Expr tp2 -> Command tp -> Command tp
    Ite :: forall tp. Expr TBool -> Command tp -> Command tp -> Command tp
    Ret :: forall tp. Expr tp -> Command tp

cSampl :: String -> Distr tp2 -> [SomeExp] -> Command tp -> Command tp
cSampl = Sampl

cLet :: String -> Expr tp2 -> Command tp -> Command tp
cLet = Let

cIte :: Expr TBool -> Command tp -> Command tp -> Command tp
cIte = Ite

cRet :: Expr tp -> Command tp 
cRet = Ret

ppCommand :: Command tp -> String
ppCommand (Sampl x d args k) =
    x ++ " <- " ++ (ppDistr d) ++ concatMap ppSomeExp args ++ ";\n" ++ (ppCommand k)
ppCommand (Let x e k) =
    "let " ++ x ++ " = " ++ (ppExpr e) ++ ";\n" ++ (ppCommand k)
ppCommand (Ite b e1 e2) =
    "if " ++ (ppExpr b) ++ " then " ++ (ppCommand e1) ++ " else " ++ (ppCommand e2)
ppCommand (Ret e) = "ret " ++ (ppExpr e)

