import Definitions.Def_BitcoinTapSoundness
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinTaproot
open BitcoinTapSoundness BitcoinSer BitcoinTaproot

theorem BitcoinTapSoundness.script_path_soundness (T : BitcoinTapSoundness.TapTree) (control : BitcoinSer.Bytes) (k : Nat)
    (hc : control.length = BitcoinTaproot.TAPROOT_CONTROL_BASE_SIZE + BitcoinTaproot.TAPROOT_CONTROL_NODE_SIZE * k)
    (v : BitcoinSer.Byte) (s : BitcoinSer.Bytes)
    (h : BitcoinTaproot.taprootMerkleRoot control (BitcoinTaproot.tapleafHash v s) = T.hash) :
    BitcoinTaproot.tapleafHash v s ∈ T.leaves ∨ BitcoinTapSoundness.Sha256Collision := by sorry
