import Definitions.Def_BitcoinTapSoundnessV2
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinTaproot
open BitcoinTapSoundnessV2 BitcoinSer BitcoinTaproot

theorem BitcoinTapSoundnessV2.branch_eq (a b c d : BitcoinSer.Bytes) (ha : a.length = 32) (hb : b.length = 32)
    (hc : c.length = 32) (hd : d.length = 32) (h : BitcoinTaproot.tapbranchHash a b = BitcoinTaproot.tapbranchHash c d) :
    ((a = c ∧ b = d) ∨ (a = d ∧ b = c)) ∨
      BitcoinTapSoundnessV2.Collides (BitcoinTapSoundnessV2.taggedPre "TapBranch" (BitcoinTapSoundnessV2.branchMsg a b))
        (BitcoinTapSoundnessV2.taggedPre "TapBranch" (BitcoinTapSoundnessV2.branchMsg c d)) := by sorry
