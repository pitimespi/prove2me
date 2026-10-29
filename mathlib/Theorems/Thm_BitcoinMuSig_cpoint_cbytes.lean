import Definitions.Def_BitcoinMuSig
open BitcoinMuSig BitcoinSig BitcoinTaproot

theorem BitcoinMuSig.cpoint_cbytes (P : ℕ × ℕ) (hP : onCurve P = true) (hx : P.1 < p) (hy : P.2 < p) :
    cpoint (cbytes P) = some P := by sorry
