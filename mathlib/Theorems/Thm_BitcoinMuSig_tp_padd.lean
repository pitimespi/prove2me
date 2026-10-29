import Definitions.Def_BitcoinMuSig
open BitcoinMuSig BitcoinSig BitcoinTaproot

theorem BitcoinMuSig.tp_padd (P Q : Point) (hP : Valid P) (hQ : Valid Q) :
    tp (padd P Q) = tp P + tp Q := by sorry
