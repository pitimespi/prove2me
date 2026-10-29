import Definitions.Def_BitcoinMuSig
open BitcoinMuSig BitcoinSig BitcoinTaproot

theorem BitcoinMuSig.toPoint_padd (P Q : Point) (hP : Valid P) (hQ : Valid Q) :
    toPoint (padd P Q) = some (tp P + tp Q) := by sorry
