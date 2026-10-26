import Definitions.Def_BitcoinSer

theorem BitcoinSer.compactSize_canonical (rc : Bool) (b : Bytes) (n : Nat) (rest : Bytes)
    (h : BitcoinSer.readCompactSize rc b = some (n, rest)) : b = BitcoinSer.writeCompactSize n ++ rest := by sorry
