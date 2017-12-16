module Prot.Examples.Rotate where

import Prot.Lang.Expr
import Prot.Lang.Command
import Data.SBV
import Prot.Lang.Lang
import Prot.Lang.Types
import Data.Parameterized.Some

rotateA :: Dist (Expr TInt)
rotateA = do
    let d1 = mkDistr "D" TIntRepr (\_ _ -> [])
        d2 = unifBool 
    z <- dSamp d1 []
    x <- dSamp d1 [mkSome z]
    dIte (x |<=| 5)
        (do
            y <- dSamp d2 []
            dIte y
                (return (x - 5))
                (return (x * 2))
        )
        (do
            y <- dSamp d2 []
            dIte y
                (return (x - 3))
                (return (x - 1))
        )

rotateB :: Dist (Expr TInt)
rotateB = do
    let d1 = mkDistr "D" TIntRepr (\_ _ -> [])
        d2 = unifBool 
    z <- dSamp d1 []
    y <- dSamp d2 []
    dIte y
        (do
            x <- dSamp d1 [mkSome z]
            dIte (x |<=| 5)
                (return (x - 5))
                (return (x - 3))
        )
        (do
            x <- dSamp d1 [mkSome z]
            dIte (x |<=| 5)
                (return (x * 2))
                (return (x - 1))
        )

tryComp :: Dist (Expr TInt)
tryComp = do
    x <- rotateB
    y <- rotateB
    return (x + y)


tryWrongRet0 :: Dist Integer
tryWrongRet0 = do
    return 37

tryWrongRet :: Dist (Expr TInt)
tryWrongRet = do
    x <- tryWrongRet0
    return (fromInteger x)
