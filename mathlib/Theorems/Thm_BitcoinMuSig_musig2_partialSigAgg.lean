import Definitions.Def_BitcoinMuSig
open BitcoinMuSig BitcoinSig BitcoinTaproot

theorem BitcoinMuSig.musig2_partialSigAgg {ι K M : Type*} [CommRing K] [AddCommGroup M] [Module K M]
    (S : Finset ι) (G : M) (X R₁ R₂ : ι → M) (a s : ι → K) (b e g gacc tacc ε : K) (Q : M)
    (hQ : Q = gacc • ∑ i ∈ S, a i • X i + tacc • G)
    (hpart : ∀ i ∈ S, s i • G = ε • (R₁ i + b • R₂ i) + (e * a i * (g * gacc)) • X i) :
    (∑ i ∈ S, s i + e * g * tacc) • G = ε • (∑ i ∈ S, R₁ i + b • ∑ i ∈ S, R₂ i) + e • (g • Q) := by sorry
