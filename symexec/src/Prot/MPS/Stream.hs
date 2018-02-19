
module Prot.MPS.Stream where
import Prot.Lang.Expr
import Prot.Lang.Lang

data Stream tp = Stream { initStream :: Dist (Expr tp)
                        , streamTr :: Expr tp -> Dist (Expr tp)}


