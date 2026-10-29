import Definitions.Def_BitcoinTapSoundnessV2
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinTaproot
open BitcoinTapSoundnessV2 BitcoinSer BitcoinTaproot

theorem BitcoinTapSoundnessV2.tagged_pre (t : String) (m : BitcoinSer.Bytes) :
    BitcoinTaproot.tagged t m = BitcoinSer.sha256 (BitcoinTapSoundnessV2.taggedPre t m) := by sorry
