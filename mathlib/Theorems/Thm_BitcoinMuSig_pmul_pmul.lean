import Definitions.Def_BitcoinMuSig
open BitcoinMuSig BitcoinSig BitcoinTaproot

theorem BitcoinMuSig.pmul_pmul (a b : ℕ) (P : Point) (hP : Valid P) (hPr : Reduced P)
    (ha : a < 2 ^ 257) (hb : b < 2 ^ 257) (hab : a * b < 2 ^ 257) :
    pmul a (pmul b P) = pmul (a * b) P := by sorry
