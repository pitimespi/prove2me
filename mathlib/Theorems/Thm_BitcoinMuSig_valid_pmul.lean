import Definitions.Def_BitcoinMuSig
open BitcoinMuSig BitcoinSig BitcoinTaproot

theorem BitcoinMuSig.valid_pmul (k : ℕ) (P : Point) (hP : Valid P) (hk : k < 2 ^ 257) :
    Valid (pmul k P) := by sorry
