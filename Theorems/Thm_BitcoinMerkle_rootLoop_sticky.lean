import Definitions.Def_BitcoinMerkle

theorem BitcoinMerkle.rootLoop_sticky {H : Type} [DecidableEq H] (c : H → H → H) (z : H)
    (hs : List H) : (BitcoinMerkle.rootLoop c z hs true).2 = true := by sorry
