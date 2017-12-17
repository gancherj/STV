module Prot.Lang.Lang where
import Prot.Lang.Command
import Prot.Lang.Expr
import Prot.Lang.Types
import Prot.Lang.Analyze
import Control.Monad.Except
import Data.Type.Equality
import Data.Parameterized.Some
import Control.Monad.State
import qualified Prot.Lang.SMT as SMT
import qualified Prot.Lang.Run as R
import Control.Monad.Free

-- I need a better translation language.

data DistF k where
    DSamp :: Distr tp -> [SomeExp] -> (Expr tp -> k) -> DistF k
    DIte :: Expr TBool -> k -> k -> DistF k

instance Functor DistF where
    fmap f (DSamp d es k) = DSamp d es (f . k)
    fmap f (DIte e k1 k2) = DIte e (f k1) (f k2)

type Dist = Free DistF

data SomeDist = forall tp. SomeDist (TypeRepr tp) (Dist (Expr tp))

dSamp :: Distr tp -> [SomeExp] -> Dist (Expr tp)
dSamp d args = liftF $ DSamp d args id

dIte :: Expr TBool -> Dist a -> Dist a -> Dist a
dIte x k1 k2 = 
    wrap $ DIte x (k1) (k2)

compileDist' :: Dist (Expr tp) -> State Int (Command tp)
compileDist' (Pure e) = return $ Ret e
compileDist' (Free (DSamp d args k)) = do
    n <- freshName
    cont <- compileDist' (k (mkAtom n (typeOf d)))
    return $ Sampl n d args cont
compileDist' (Free (DIte b k1 k2)) = do
    cont1 <- compileDist' k1
    cont2 <- compileDist' k2
    return $ Ite b cont1 cont2

compileDist :: Dist (Expr tp) -> Command tp
compileDist d = evalState (compileDist' d) 0

freshName :: State Int String
freshName = do
    x <- get
    put $ (x + 1)
    return $ "x" ++ (show x)


distEquiv :: Dist (Expr tp) -> Dist (Expr tp) -> IO Bool
distEquiv d1 d2 = do
    let c = compileDist d1
        c' = compileDist d2
        leaves1_ = map unfoldLets $ commandToLeaves c
        leaves2_ = map unfoldLets $ commandToLeaves c'
    leaves1 <- filterM SMT.leafSatisfiable leaves1_
    leaves2 <- filterM SMT.leafSatisfiable leaves2_
    SMT.leavesEquiv (map mkDag leaves1) (map mkDag leaves2)
      
ppDist :: Dist (Expr tp) -> String
ppDist p =
    ppCommand (compileDist p)

ppDistLeaves :: Dist (Expr tp) -> String
ppDistLeaves p =
    ppLeaves $ commandToLeaves $ compileDist p

ppDistDag :: Dist (Expr tp) -> String
ppDistDag p =
    ppLeafDags $ map mkDag (map unfoldLets $ commandToLeaves $ compileDist p)

ppSatDistLeaves :: Dist (Expr tp) -> IO String
ppSatDistLeaves p = do
    let cmd = compileDist p 
    leaves <- filterM SMT.leafSatisfiable (map unfoldLets $ commandToLeaves cmd)
    return $ show leaves

runDist :: Dist (Expr tp) -> IO R.SomeInterp
runDist p = do
    let cmd = compileDist p 
    e <- R.runCommand cmd
    return $ R.SomeInterp (typeOf cmd) e

--- abbreviations

unifBool = dSamp unifBoolDistr []
unifInt x y = dSamp (unifIntDistr x y) []

dSwitch :: ExprEq (Expr a) => Expr a -> Dist b -> [(Expr a, Dist b)] -> Dist b
dSwitch e def [] = def
dSwitch e def ((cond,a):as) =
    dIte (e |==| cond) a (dSwitch e def as)

