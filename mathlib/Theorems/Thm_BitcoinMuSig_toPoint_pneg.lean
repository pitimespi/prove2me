import Definitions.Def_BitcoinMuSig
open BitcoinMuSig BitcoinSig BitcoinTaproot

theorem BitcoinMuSig.toPoint_pneg (P : Point) (hP : Valid P) : toPoint (pneg P) = some (-tp P) := by sorry
