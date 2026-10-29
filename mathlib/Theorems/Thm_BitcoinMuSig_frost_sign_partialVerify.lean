import Definitions.Def_BitcoinMuSig
open BitcoinMuSig BitcoinSig BitcoinTaproot

theorem BitcoinMuSig.frost_sign_partialVerify {K M : Type*} [CommRing K] [AddCommGroup M] [Module K M]
    (G : M) (d e ρ lam s c : K) :
    (d + e * ρ + lam * s * c) • G = d • G + ρ • (e • G) + (c * lam) • (s • G) := by sorry
