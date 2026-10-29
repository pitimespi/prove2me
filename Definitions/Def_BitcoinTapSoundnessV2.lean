import Definitions.Def_BitcoinTaproot

/-!
# Soundness of the Taproot script path, revision 2

A Taproot output commits to a tree of scripts through its tweaked key; a spender opens one leaf
with a control block (internal key, parity bit, Merkle path). The claim behind the design is that
nobody can open a leaf the creator did not put in the tree. This file states that claim as a
*constructive* reduction: whenever a control block passes verification for a leaf outside the tree,
the statement names two different byte strings with the same SHA-256, computed from the inputs, or
two different 32-byte tweak scalars, computed from the inputs, that both carry the internal key to
the output key.

Revision 2 replaces the first revision's closed propositions ("some collision exists"), which are
provable by counting and therefore said nothing, by explicit witnesses.
-/

namespace BitcoinTapSoundnessV2

open BitcoinSer BitcoinTaproot

/-- Two different byte strings with the same SHA-256. -/
def Collides (x y : Bytes) : Prop := x ≠ y ∧ sha256 x = sha256 y

/-- The preimage of a tagged hash: `SHA256(tag) ‖ SHA256(tag) ‖ m`, so that
`tagged t m = sha256 (taggedPre t m)`. -/
def taggedPre (t : String) (m : Bytes) : Bytes :=
  sha256 (BitcoinSig.ascii t) ++ sha256 (BitcoinSig.ascii t) ++ m

/-- The message of `ComputeTapleafHash`: the leaf version, the compact-size length, the script. -/
def leafMsg (v : Byte) (s : Bytes) : Bytes := [v] ++ BitcoinSer.writeCompactSize s.length ++ s

/-- The message of `ComputeTapbranchHash`: the two children in lexicographic order. -/
def branchMsg (a b : Bytes) : Bytes := if lexLt a b then a ++ b else b ++ a

/-- A tree of tapscript leaves as the output's creator built it (BIP341). -/
inductive TapTree where
  | leaf (version : Byte) (script : Bytes)
  | branch (l r : TapTree)
  deriving DecidableEq, Repr

/-- The hash of a tree: `ComputeTapleafHash` at a leaf, `ComputeTapbranchHash` at a branch. -/
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

/-- Walk a Merkle path from the hash `h` up to the root of `T`, descending the tree in step with the
path: the result is the subtree the path lands on, or a candidate pair of colliding strings found
where the tree and the path disagree. At each level the hash below is either one of the two
children (continue into that child) or neither (two different `TapBranch` preimages with the same
hash); a leaf met before the path is exhausted gives a `TapLeaf` and a `TapBranch` preimage with
the same hash. -/
def walk : TapTree → List Bytes → Bytes → TapTree ⊕ (Bytes × Bytes)
  | T, [], _ => .inl T
  | T, n :: rest, h =>
    match walk T rest (tapbranchHash h n) with
    | .inr c => .inr c
    | .inl (.leaf v s) => .inr (taggedPre "TapLeaf" (leafMsg v s), taggedPre "TapBranch" (branchMsg h n))
    | .inl (.branch l r) =>
      if h = l.hash then .inl l
      else if h = r.hash then .inl r
      else .inr (taggedPre "TapBranch" (branchMsg l.hash r.hash), taggedPre "TapBranch" (branchMsg h n))

/-- The colliding pair a control block exhibits, if any, when its path carries the leaf hash of
`(v, s)` to the root of `T`: the pair found by `walk`, or, when the walk lands on a branch whose hash
is the leaf hash, that branch's `TapBranch` preimage against the leaf's `TapLeaf` preimage. `none`
means the walk landed on a leaf, which is then a leaf of `T`. -/
def scriptPathWitness (T : TapTree) (control : Bytes) (v : Byte) (s : Bytes) : Option (Bytes × Bytes) :=
  match walk T (controlNodes control) (tapleafHash v s) with
  | .inr c => some c
  | .inl (.leaf _ _) => none
  | .inl (.branch l r) => some (taggedPre "TapLeaf" (leafMsg v s), taggedPre "TapBranch" (branchMsg l.hash r.hash))

/-- Two different 32-byte tweak scalars that both carry the internal point `P` to the output key
`q` with parity `parity` under `secp256k1_xonly_pubkey_tweak_add_check`: a discrete-logarithm
relation on secp256k1. -/
def TweakCollision (q : Bytes) (parity : Bool) (P : Nat × Nat) (t₁ t₂ : Bytes) : Prop :=
  t₁ ≠ t₂ ∧ t₁.length = 32 ∧ t₂.length = 32 ∧
    xonlyTweakAddCheck q parity P t₁ = true ∧ xonlyTweakAddCheck q parity P t₂ = true

/-- An honestly constructed Taproot output: `q` is the tweak of the internal key `internal32` by the
tree's root, with the given parity (`XOnlyPubKey::CheckTapTweak`). -/
def HonestOutput (q internal32 : Bytes) (parity : Bool) (T : TapTree) : Prop :=
  checkTapTweak q internal32 T.hash parity = true

/-- The internal key of a control block (bytes 1 to 32). -/
def controlInternalKey (control : Bytes) : Bytes := (control.drop 1).take 32

/-- The parity bit of a control block (bit 0 of its first byte). -/
def controlParity (control : Bytes) : Bool := decide ((control.getD 0 0).toNat % 2 = 1)

end BitcoinTapSoundnessV2
