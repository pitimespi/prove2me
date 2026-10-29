import Definitions.Def_BitcoinTapSoundness
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinTaproot
import Definitions.Def_BitcoinSig
open BitcoinTapSoundness BitcoinSer BitcoinTaproot

theorem BitcoinTapSoundness.commitment_soundness (q internal32 : BitcoinSer.Bytes) (parity : Bool)
    (T : BitcoinTapSoundness.TapTree) (hT : BitcoinTapSoundness.HonestOutput q internal32 parity T)
    (control : BitcoinSer.Bytes) (k : Nat)
    (hc : control.length = BitcoinTaproot.TAPROOT_CONTROL_BASE_SIZE + BitcoinTaproot.TAPROOT_CONTROL_NODE_SIZE * k)
    (hkey : BitcoinTapSoundness.controlInternalKey control = internal32) (hpar : BitcoinTapSoundness.controlParity control = parity)
    (v : BitcoinSer.Byte) (s : BitcoinSer.Bytes)
    (h : BitcoinTaproot.verifyTaprootCommitment control q (BitcoinTaproot.tapleafHash v s) = true) :
    BitcoinTaproot.tapleafHash v s ∈ T.leaves ∨ BitcoinTapSoundness.Sha256Collision ∨
      ∃ P, BitcoinSig.liftX (BitcoinSig.beVal internal32) = some P ∧ BitcoinTapSoundness.TweakCollision q parity P := by sorry
