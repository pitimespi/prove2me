import Definitions.Def_BitcoinMuSig
open BitcoinMuSig BitcoinSig BitcoinTaproot

theorem BitcoinMuSig.valid_padd (P Q : Point) (hP : Valid P) (hQ : Valid Q) :
    Valid (padd P Q) := by sorry
