import Definitions.Def_BitcoinMuSig
open BitcoinMuSig BitcoinSig BitcoinTaproot

theorem BitcoinMuSig.musig2_partialSigAgg_secp256k1 {ι : Type*} (S : Finset ι) (X R₁ R₂ : ι → W.Point)
    (a s : ι → ℤ) (b e g gacc tacc ε : ℤ) (Q : W.Point)
    (hQ : Q = gacc • ∑ i ∈ S, a i • X i + tacc • Gpt)
    (hpart : ∀ i ∈ S, s i • Gpt = ε • (R₁ i + b • R₂ i) + (e * a i * (g * gacc)) • X i) :
    (∑ i ∈ S, s i + e * g * tacc) • Gpt = ε • (∑ i ∈ S, R₁ i + b • ∑ i ∈ S, R₂ i) + e • (g • Q) := by sorry
