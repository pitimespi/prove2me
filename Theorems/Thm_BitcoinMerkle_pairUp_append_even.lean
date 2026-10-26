import Definitions.Def_BitcoinMerkle

theorem BitcoinMerkle.pairUp_append_even {H : Type} [DecidableEq H] (c : H → H → H) :
    ∀ (l r : List H), l.length % 2 = 0 → BitcoinMerkle.pairUp c (l ++ r) = BitcoinMerkle.pairUp c l ++ BitcoinMerkle.pairUp c r := by sorry
