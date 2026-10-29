import Definitions.Def_BitcoinMuSig
open BitcoinMuSig BitcoinSig BitcoinTaproot

theorem BitcoinMuSig.frost_correct_secp256k1 (S : Finset ℕ) (hS : ∀ i ∈ S, i < n)
    (f : Polynomial (ZMod n)) (hdeg : f.degree < S.card) (D E : ℕ → W.Point) (ρ z : ℕ → ZMod n)
    (c : ZMod n)
    (hz : ∀ i ∈ S, (z i).val • Gpt =
      D i + (ρ i).val • E i + (c * lagrangeCoeff S i).val • ((f.eval (i : ZMod n)).val • Gpt)) :
    (∑ i ∈ S, z i).val • Gpt = ∑ i ∈ S, (D i + (ρ i).val • E i) + c.val • ((f.eval 0).val • Gpt) := by sorry
