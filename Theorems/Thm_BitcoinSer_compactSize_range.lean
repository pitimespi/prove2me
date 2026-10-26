import Definitions.Def_BitcoinSer

theorem BitcoinSer.compactSize_range (rc : Bool) (b : Bytes) (n : Nat) (rest : Bytes)
    (h : BitcoinSer.readCompactSize rc b = some (n, rest)) :
    n < 2 ^ 64 ∧ (rc = true → n ≤ BitcoinSer.MAX_SIZE) := by sorry
