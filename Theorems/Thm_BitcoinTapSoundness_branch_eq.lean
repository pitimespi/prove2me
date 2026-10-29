import Definitions.Def_BitcoinTapSoundness
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinTaproot
open BitcoinTapSoundness BitcoinSer BitcoinTaproot

theorem BitcoinTapSoundness.branch_eq (a b c d : BitcoinSer.Bytes) (ha : a.length = 32) (hb : b.length = 32)
    (hc : c.length = 32) (hd : d.length = 32) (h : BitcoinTaproot.tapbranchHash a b = BitcoinTaproot.tapbranchHash c d) :
    ((a = c ∧ b = d) ∨ (a = d ∧ b = c)) ∨ BitcoinTapSoundness.Sha256Collision := by sorry
