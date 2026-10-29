import Definitions.Def_BitcoinMuSig
open BitcoinMuSig BitcoinSig BitcoinTaproot

theorem BitcoinMuSig.eq_of_tp_eq (P Q : Point) (hP : Valid P) (hQ : Valid Q) (hPr : Reduced P)
    (hQr : Reduced Q) (h : tp P = tp Q) : P = Q := by sorry
