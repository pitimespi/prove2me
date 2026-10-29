SRC = ("Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyTaprootCommitment, ComputeTaprootMerkleRoot, ComputeTapleafHash, ComputeTapbranchHash "
       "(src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); "
       "XOnlyPubKey::CheckTapTweak, ComputeTapTweakHash (src/pubkey.cpp); secp256k1_xonly_pubkey_tweak_add_check; BIP341")
TAGS = ["bitcoin", "taproot", "bip341", "merkle", "soundness", "tagged-hash", "collision", "formal-verification", "bitcoin-mainnet"]

DEFINITION = {
    "definition_name": "BitcoinTapSoundnessV2",
    "definition_title": "Script trees, explicit collision witnesses, and honest Taproot outputs (revision 2)",
    "natural_language_statement": r"""Names over the Taproot mission's `BitcoinTaproot`; nothing of Core is re-transcribed. Revision 2 of `BitcoinTapSoundness`: the closed propositions "some SHA-256 collision exists" and "some pair of tweaks collides" of the first revision are provable by counting and said nothing; here every collision is a pair of explicit byte strings computed from the inputs.

**`Collides x y`** — the two given byte strings differ and have the same `sha256`. **`taggedPre t m`** $=$ `sha256 (ascii t) ++ sha256 (ascii t) ++ m`, the preimage of the tagged hash, so `tagged t m = sha256 (taggedPre t m)`. **`leafMsg v s`** and **`branchMsg a b`** — the messages of `ComputeTapleafHash` (version, compact-size length, script) and `ComputeTapbranchHash` (the two children in lexicographic order).

**`TapTree`** — a binary tree of leaves (version byte, script); **`TapTree.hash`**, **`TapTree.leaves`**, **`TapTree.subtreesAt T d`** as in revision 1.

**`walk T nodes h`** — follows a Merkle path from the hash $h$ up to the root of $T$ while descending the tree in step with the path, returning either the subtree the path lands on or a pair of candidate colliding strings: where the hash below is neither child of the current branch, the two `TapBranch` preimages; where a leaf is met before the path ends, the `TapLeaf` and `TapBranch` preimages. **`scriptPathWitness T control v s`** — the pair `walk` finds on the control block's path from `tapleafHash v s`, or, if the walk lands on a branch, that branch's `TapBranch` preimage against the leaf's `TapLeaf` preimage; `none` when the walk lands on a leaf.

**`TweakCollision q parity P t₁ t₂`** — the two given tweak scalars differ, are both 32 bytes, and both pass `xonlyTweakAddCheck q parity P` (Core's `secp256k1_xonly_pubkey_tweak_add_check`): a discrete-logarithm relation on secp256k1.

**`HonestOutput q internal32 parity T`**, **`controlInternalKey`**, **`controlParity`** — as in revision 1 (`XOnlyPubKey::CheckTapTweak` with the tree's root; bytes 1–32 and bit 0 of the control block).

**Formalization Note.** `tagged`, `tapleafHash`, `tapbranchHash`, `lexLt`, `controlNodes`, `taprootMerkleRoot`, `tapTweakHash`, `xonlyTweakAddCheck`, `checkTapTweak`, `verifyTaprootCommitment` are the Taproot mission's; `sha256`, `writeCompactSize`, `taggedHash`, `ascii`, `liftX`, `beVal` the serialization and signature missions'. Only `Std` is imported.""",
}

THEOREMS = {
"BitcoinTapSoundnessV2.tagged_pre": dict(title="A tagged hash is the SHA-256 of its preimage",
    nl=r"""`tagged t m = sha256 (taggedPre t m)`, by definition of `taggedHash`.""", ms=None),
"BitcoinTapSoundnessV2.tagged_collision": dict(title="Equal tagged hashes have equal tag hashes and messages, or their two preimages collide",
    nl=r"""For tags $t, t'$ and messages $m, m'$: if `tagged t m = tagged t' m'` then either `sha256 (ascii t) = sha256 (ascii t')` and $m = m'$, or `Collides (taggedPre t m) (taggedPre t' m')`: the two explicit 64-byte-prefixed preimages differ and hash alike.""", ms=None),
"BitcoinTapSoundnessV2.tapleaf_ne_tapbranch": dict(title="The TapLeaf and TapBranch tags hash differently",
    nl=r"""`sha256 (ascii "TapLeaf") ≠ sha256 (ascii "TapBranch")`, by kernel computation of the model's SHA-256.""", ms=None),
"BitcoinTapSoundnessV2.leaf_ne_branch": dict(title="A leaf hash equal to a branch hash: the TapLeaf and TapBranch preimages collide",
    nl=r"""For any leaf version $v$, script $s$ and byte strings $a, b$: `tapleafHash v s = tapbranchHash a b` implies `Collides (taggedPre "TapLeaf" (leafMsg v s)) (taggedPre "TapBranch" (branchMsg a b))`. The two strings differ in their first 32 bytes (`tapleaf_ne_tapbranch`).""", ms=None),
"BitcoinTapSoundnessV2.branch_eq": dict(title="Equal branch hashes of 32-byte children have the same children up to order, or the two TapBranch preimages collide",
    nl=r"""For 32-byte strings $a, b, c, d$: `tapbranchHash a b = tapbranchHash c d` implies $(a = c \land b = d) \lor (a = d \land b = c)$, or `Collides (taggedPre "TapBranch" (branchMsg a b)) (taggedPre "TapBranch" (branchMsg c d))`.""",
    ms=("The sorted concatenation splits", "`tagged_collision` reduces to equal messages; the four cases of the two lexicographic comparisons each split at byte 32.")),
"BitcoinTapSoundnessV2.path_lands": dict(title="Walking a Merkle path lands on a subtree at the path's depth, or returns two colliding strings",
    nl=r"""For a tree $T$, a list of 32-byte path nodes and a 32-byte starting hash $h$ with `nodes.foldl tapbranchHash h = T.hash`: either `walk T nodes h = .inl U` for a subtree $U$ of $T$ at depth equal to the number of nodes with `U.hash = h`, or `walk T nodes h = .inr (x, y)` with `Collides x y`. The collision, when there is one, is the pair `walk` computes from the inputs.""",
    ms=("Induction on the path", "The fold is unrolled from the leaf; at each level the hash below is one of the children (continue) or `branch_eq` gives the explicit pair; a leaf met early gives `leaf_ne_branch`'s pair.")),
"BitcoinTapSoundnessV2.script_path_soundness": dict(title="Script-path soundness at the Merkle level: a verified path opens a committed leaf, or scriptPathWitness names a collision",
    nl=r"""For a tree $T$, a control block of length $33 + 32k$, a leaf version $v$ and a script $s$ with `taprootMerkleRoot control (tapleafHash v s) = T.hash`: either `scriptPathWitness T control v s = none` and `tapleafHash v s ∈ T.leaves`, or `scriptPathWitness T control v s = some (x, y)` with `Collides x y`.""", ms=None),
"BitcoinTapSoundnessV2.commitment_soundness": dict(title="Script-path soundness at the commitment level: VerifyTaprootCommitment opens only committed leaves, or names an explicit SHA-256 or tweak collision",
    nl=r"""For an output key $q$, internal key `internal32`, parity bit and tree $T$ with `HonestOutput q internal32 parity T`, and any control block of length $33 + 32k$ whose internal-key bytes are `internal32` and parity bit is `parity`, and any leaf $(v, s)$ with `verifyTaprootCommitment control q (tapleafHash v s) = true`, writing `root` for `taprootMerkleRoot control (tapleafHash v s)`, one of:

1. `root = T.hash`, and either `scriptPathWitness T control v s = none` with `tapleafHash v s ∈ T.leaves`, or it is `some (x, y)` with `Collides x y`;
2. `root ≠ T.hash` and `Collides (taggedPre "TapTweak" (internal32 ++ root)) (taggedPre "TapTweak" (internal32 ++ T.hash))`;
3. `root ≠ T.hash` and, for the point $P$ with `liftX (beVal internal32) = some P`, `TweakCollision q parity P (tapTweakHash internal32 root) (tapTweakHash internal32 T.hash)`: the two 32-byte tweak hashes differ and both carry $P$ to $q$.

Every collision is an explicit pair of strings computed from the inputs. This is the BIP341 claim that a spender cannot open a leaf the output's creator did not commit to, stated as a reduction to SHA-256 collision resistance and to the hardness of finding two tweaks for one output key.""",
    ms=None),
}
ORDER = ["BitcoinTapSoundnessV2.tagged_pre", "BitcoinTapSoundnessV2.tagged_collision", "BitcoinTapSoundnessV2.tapleaf_ne_tapbranch",
         "BitcoinTapSoundnessV2.leaf_ne_branch", "BitcoinTapSoundnessV2.branch_eq", "BitcoinTapSoundnessV2.path_lands",
         "BitcoinTapSoundnessV2.script_path_soundness", "BitcoinTapSoundnessV2.commitment_soundness"]
