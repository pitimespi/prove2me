import Definitions.Def_BitcoinTaproot

/-!
# Soundness of the Taproot script path

A Taproot output commits to a tree of scripts through its tweaked key. A spender opens one leaf by
presenting a control block: the internal key, a parity bit, and a Merkle path. The claim behind the
design is that nobody can open a leaf the output's creator did not put in the tree. In the model
that claim reduces to two hardness assumptions, which this file names so that the theorem can be
stated as a reduction: a collision of SHA-256, or two different tweak scalars carrying the same
internal key to the same output key (a discrete-logarithm relation on secp256k1).
-/

namespace BitcoinTapSoundness

open BitcoinSer BitcoinTaproot

/-- A collision of SHA-256: two different messages with the same digest. -/
def Sha256Collision : Prop := ∃ x y : Bytes, x ≠ y ∧ sha256 x = sha256 y

/-- A tree of tapscript leaves as the output's creator built it (BIP341). -/
inductive TapTree where
  | leaf (version : Byte) (script : Bytes)
  | branch (l r : TapTree)

/-- The hash of a tree: `ComputeTapleafHash` for a leaf, `ComputeTapbranchHash` of the children's
hashes for a branch. -/
def TapTree.hash : TapTree → Bytes
  | .leaf v s => tapleafHash v s
  | .branch l r => tapbranchHash l.hash r.hash

/-- The leaf hashes committed in a tree. -/
def TapTree.leaves : TapTree → List Bytes
  | .leaf v s => [tapleafHash v s]
  | .branch l r => l.leaves ++ r.leaves

/-- The subtrees at depth `d`. -/
def TapTree.subtreesAt : TapTree → Nat → List TapTree
  | T, 0 => [T]
  | .leaf _ _, _ + 1 => []
  | .branch l r, d + 1 => l.subtreesAt d ++ r.subtreesAt d

/-- Two different tweak scalars (32-byte strings) that both carry the internal point `P` to the
output key `q` with parity `parity` under `secp256k1_xonly_pubkey_tweak_add_check`: a
discrete-logarithm relation, outside the model's reach. -/
def TweakCollision (q : Bytes) (parity : Bool) (P : Nat × Nat) : Prop :=
  ∃ t₁ t₂ : Bytes, t₁ ≠ t₂ ∧ xonlyTweakAddCheck q parity P t₁ = true ∧ xonlyTweakAddCheck q parity P t₂ = true

/-- An honestly constructed Taproot output: `q` is the tweak of the internal key `internal32` by the
tree's root, with the given parity (`XOnlyPubKey::CheckTapTweak`). -/
def HonestOutput (q internal32 : Bytes) (parity : Bool) (T : TapTree) : Prop :=
  checkTapTweak q internal32 T.hash parity = true

/-- The internal key of a control block (bytes 1 to 32). -/
def controlInternalKey (control : Bytes) : Bytes := (control.drop 1).take 32

/-- The parity bit of a control block (bit 0 of its first byte). -/
def controlParity (control : Bytes) : Bool := decide ((control.getD 0 0).toNat % 2 = 1)

end BitcoinTapSoundness
