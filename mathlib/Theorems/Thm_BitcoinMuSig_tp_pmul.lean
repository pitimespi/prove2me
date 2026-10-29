import Definitions.Def_BitcoinMuSig
open BitcoinMuSig BitcoinSig BitcoinTaproot

theorem BitcoinMuSig.tp_pmul (k : ℕ) (P : Point) (hP : Valid P) (hk : k < 2 ^ 257) :
    tp (pmul k P) = k • tp P := by sorry
