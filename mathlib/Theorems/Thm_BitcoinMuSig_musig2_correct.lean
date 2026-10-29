import Definitions.Def_BitcoinMuSig
open BitcoinMuSig BitcoinSig BitcoinTaproot

theorem BitcoinMuSig.musig2_correct {ι K M : Type*} [CommRing K] [AddCommGroup M] [Module K M]
    (S : Finset ι) (G : M) (d k₁ k₂ a : ι → K) (b e g gacc tacc ε : K) :
    (∑ i ∈ S, (ε * k₁ i + b * (ε * k₂ i) + e * a i * (g * gacc * d i)) + e * g * tacc) • G =
      ε • (∑ i ∈ S, k₁ i • G + b • ∑ i ∈ S, k₂ i • G) +
        e • (g • (gacc • ∑ i ∈ S, a i • (d i • G) + tacc • G)) := by sorry
