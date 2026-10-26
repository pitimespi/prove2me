import Definitions.Def_BitcoinSer

theorem BitcoinSer.readLE_leBytes (k n : Nat) (rest : Bytes) (h : n < 2 ^ (8 * k)) :
    BitcoinSer.readLE k (BitcoinSer.leBytes k n ++ rest) = some (n, rest) := by sorry
