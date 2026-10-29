import Definitions.Def_BitcoinMuSig
open BitcoinMuSig BitcoinSig BitcoinTaproot

theorem BitcoinMuSig.pmul_padd (k : ℕ) (P Q : Point) (hP : Valid P) (hQ : Valid Q) (hPr : Reduced P)
    (hQr : Reduced Q) (hk : k < 2 ^ 257) :
    pmul k (padd P Q) = padd (pmul k P) (pmul k Q) := by sorry
