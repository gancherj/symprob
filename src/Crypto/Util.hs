module Crypto.Util where
import Data.SBV

symSwitch :: Mergeable a => [(SBool, a)] -> a -> a
symSwitch [] def = def 
symSwitch ((cond, a) : conds) def =
    iteLazy cond a (symSwitch conds def)
