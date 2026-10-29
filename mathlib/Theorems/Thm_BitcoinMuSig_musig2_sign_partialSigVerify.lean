import Definitions.Def_BitcoinMuSig
open BitcoinMuSig BitcoinSig BitcoinTaproot

theorem BitcoinMuSig.musig2_sign_partialSigVerify {K M : Type*} [CommRing K] [AddCommGroup M]
    [Module K M] (G : M) (d k₁ k₂ a b e g gacc ε : K) :
    (ε * k₁ + b * (ε * k₂) + e * a * (g * gacc * d)) • G =
      ε • (k₁ • G + b • (k₂ • G)) + (e * a * (g * gacc)) • (d • G) := by sorry
