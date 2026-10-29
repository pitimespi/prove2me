import Definitions.Def_BitcoinMuSig
import Definitions.Def_BitcoinSer
open BitcoinMuSig BitcoinSig BitcoinTaproot

theorem BitcoinMuSig.cpoint_spec (b : BitcoinSer.Bytes) (P : ℕ × ℕ) (h : cpoint b = some P) :
    onCurve P = true ∧ P.1 < p ∧ P.2 < p := by sorry
