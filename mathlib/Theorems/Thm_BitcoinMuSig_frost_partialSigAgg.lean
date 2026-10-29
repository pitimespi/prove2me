import Definitions.Def_BitcoinMuSig
open BitcoinMuSig BitcoinSig BitcoinTaproot

theorem BitcoinMuSig.frost_partialSigAgg {ι K M : Type*} [CommRing K] [AddCommGroup M] [Module K M]
    (S : Finset ι) (G : M) (D E Y : ι → M) (ρ lam z : ι → K) (c : K)
    (hz : ∀ i ∈ S, z i • G = D i + ρ i • E i + (c * lam i) • Y i) :
    (∑ i ∈ S, z i) • G = ∑ i ∈ S, (D i + ρ i • E i) + c • ∑ i ∈ S, lam i • Y i := by sorry
