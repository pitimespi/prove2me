import Definitions.Def_BitcoinMuSig
open BitcoinMuSig BitcoinSig BitcoinTaproot

theorem BitcoinMuSig.lagrange_interpolate_zero (S : Finset ℕ) (hS : ∀ i ∈ S, i < n)
    (f : Polynomial (ZMod n)) (hdeg : f.degree < S.card) :
    ∑ i ∈ S, lagrangeCoeff S i * f.eval (i : ZMod n) = f.eval 0 := by sorry
