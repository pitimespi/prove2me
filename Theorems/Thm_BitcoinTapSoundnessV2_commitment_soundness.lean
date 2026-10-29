import Definitions.Def_BitcoinTapSoundnessV2
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinTaproot
import Definitions.Def_BitcoinSig
open BitcoinTapSoundnessV2 BitcoinSer BitcoinTaproot

theorem BitcoinTapSoundnessV2.commitment_soundness (q internal32 : BitcoinSer.Bytes) (parity : Bool)
    (T : BitcoinTapSoundnessV2.TapTree) (hT : BitcoinTapSoundnessV2.HonestOutput q internal32 parity T)
    (control : BitcoinSer.Bytes) (k : Nat)
    (hc : control.length = BitcoinTaproot.TAPROOT_CONTROL_BASE_SIZE + BitcoinTaproot.TAPROOT_CONTROL_NODE_SIZE * k)
    (hkey : BitcoinTapSoundnessV2.controlInternalKey control = internal32) (hpar : BitcoinTapSoundnessV2.controlParity control = parity)
    (v : BitcoinSer.Byte) (s : BitcoinSer.Bytes)
    (h : BitcoinTaproot.verifyTaprootCommitment control q (BitcoinTaproot.tapleafHash v s) = true) :
    (BitcoinTaproot.taprootMerkleRoot control (BitcoinTaproot.tapleafHash v s) = T.hash ∧
      ((BitcoinTapSoundnessV2.scriptPathWitness T control v s = none ∧ BitcoinTaproot.tapleafHash v s ∈ T.leaves) ∨
        (∃ x y, BitcoinTapSoundnessV2.scriptPathWitness T control v s = some (x, y) ∧ BitcoinTapSoundnessV2.Collides x y))) ∨
    (BitcoinTaproot.taprootMerkleRoot control (BitcoinTaproot.tapleafHash v s) ≠ T.hash ∧
      BitcoinTapSoundnessV2.Collides
        (BitcoinTapSoundnessV2.taggedPre "TapTweak" (internal32 ++ BitcoinTaproot.taprootMerkleRoot control (BitcoinTaproot.tapleafHash v s)))
        (BitcoinTapSoundnessV2.taggedPre "TapTweak" (internal32 ++ T.hash))) ∨
    (BitcoinTaproot.taprootMerkleRoot control (BitcoinTaproot.tapleafHash v s) ≠ T.hash ∧
      ∃ P, BitcoinSig.liftX (BitcoinSig.beVal internal32) = some P ∧
        BitcoinTapSoundnessV2.TweakCollision q parity P
          (BitcoinTaproot.tapTweakHash internal32 (BitcoinTaproot.taprootMerkleRoot control (BitcoinTaproot.tapleafHash v s)))
          (BitcoinTaproot.tapTweakHash internal32 T.hash)) := by sorry
