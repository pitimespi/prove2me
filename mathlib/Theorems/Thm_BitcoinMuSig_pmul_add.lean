import Definitions.Def_BitcoinMuSig
open BitcoinMuSig BitcoinSig BitcoinTaproot

theorem BitcoinMuSig.pmul_add (a b : ℕ) (P : Point) (hP : Valid P) (hPr : Reduced P)
    (hab : a + b < 2 ^ 257) :
    pmul (a + b) P = padd (pmul a P) (pmul b P) := by sorry
