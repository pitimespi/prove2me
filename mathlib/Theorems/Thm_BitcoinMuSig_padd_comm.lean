import Definitions.Def_BitcoinMuSig
open BitcoinMuSig BitcoinSig BitcoinTaproot

theorem BitcoinMuSig.padd_comm (P Q : Point) (hP : Valid P) (hQ : Valid Q) :
    padd P Q = padd Q P := by sorry
