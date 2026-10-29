import Definitions.Def_BitcoinMuSig
open BitcoinMuSig BitcoinSig BitcoinTaproot

theorem BitcoinMuSig.padd_assoc (P Q R : Point) (hP : Valid P) (hQ : Valid Q) (hR : Valid R)
    (hPr : Reduced P) (hQr : Reduced Q) (hRr : Reduced R) :
    padd (padd P Q) R = padd P (padd Q R) := by sorry
