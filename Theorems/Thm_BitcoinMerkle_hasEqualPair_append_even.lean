import Definitions.Def_BitcoinMerkle

theorem BitcoinMerkle.hasEqualPair_append_even {H : Type} [DecidableEq H] :
    ∀ (l r : List H), l.length % 2 = 0 →
      BitcoinMerkle.hasEqualPair (l ++ r) = (BitcoinMerkle.hasEqualPair l || BitcoinMerkle.hasEqualPair r) := by sorry
