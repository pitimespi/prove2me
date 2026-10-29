import Definitions.Def_BitcoinTapSoundnessV2
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinTaproot
import Definitions.Def_BitcoinSig
open BitcoinTapSoundnessV2 BitcoinSer BitcoinTaproot

theorem BitcoinTapSoundnessV2.tagged_collision (t t' : String) (m m' : BitcoinSer.Bytes)
    (h : BitcoinTaproot.tagged t m = BitcoinTaproot.tagged t' m') :
    (BitcoinSer.sha256 (BitcoinSig.ascii t) = BitcoinSer.sha256 (BitcoinSig.ascii t') ∧ m = m') ∨
      BitcoinTapSoundnessV2.Collides (BitcoinTapSoundnessV2.taggedPre t m) (BitcoinTapSoundnessV2.taggedPre t' m') := by sorry
