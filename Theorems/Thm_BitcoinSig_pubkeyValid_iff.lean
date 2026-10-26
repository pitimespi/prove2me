import Definitions.Def_BitcoinSig
open BitcoinSig BitcoinSer

theorem BitcoinSig.pubkeyValid_iff (pk : Bytes) :
    BitcoinSig.pubkeyValid pk = true ↔
      (pk.length = 33 ∧ ((pk.getD 0 0).toNat = 2 ∨ (pk.getD 0 0).toNat = 3)) ∨
      (pk.length = 65 ∧ ((pk.getD 0 0).toNat = 4 ∨ (pk.getD 0 0).toNat = 6 ∨ (pk.getD 0 0).toNat = 7)) := by sorry
