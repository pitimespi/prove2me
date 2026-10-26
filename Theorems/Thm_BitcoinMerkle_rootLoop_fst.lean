import Definitions.Def_BitcoinMerkle

theorem BitcoinMerkle.rootLoop_fst {H : Type} [DecidableEq H] (c : H → H → H) (z : H)
    (hs : List H) (m m' : Bool) : (BitcoinMerkle.rootLoop c z hs m).1 = (BitcoinMerkle.rootLoop c z hs m').1 := by sorry
