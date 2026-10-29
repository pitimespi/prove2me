import Definitions.Def_BitcoinTapSoundness
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinTaproot
open BitcoinTapSoundness BitcoinSer BitcoinTaproot

theorem BitcoinTapSoundness.leaf_ne_branch (v : BitcoinSer.Byte) (s a b : BitcoinSer.Bytes)
    (h : BitcoinTaproot.tapleafHash v s = BitcoinTaproot.tapbranchHash a b) : BitcoinTapSoundness.Sha256Collision := by sorry
