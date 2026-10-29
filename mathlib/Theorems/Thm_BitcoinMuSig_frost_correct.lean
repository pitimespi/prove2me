import Definitions.Def_BitcoinMuSig
open BitcoinMuSig BitcoinSig BitcoinTaproot

theorem BitcoinMuSig.frost_correct {M : Type*} [AddCommGroup M] [Module (ZMod n) M] (G : M)
    (S : Finset ℕ) (hS : ∀ i ∈ S, i < n) (f : Polynomial (ZMod n)) (hdeg : f.degree < S.card)
    (D E : ℕ → M) (ρ z : ℕ → ZMod n) (c : ZMod n)
    (hz : ∀ i ∈ S, z i • G = D i + ρ i • E i + (c * lagrangeCoeff S i) • (f.eval (i : ZMod n) • G)) :
    (∑ i ∈ S, z i) • G = ∑ i ∈ S, (D i + ρ i • E i) + c • (f.eval 0 • G) := by sorry
