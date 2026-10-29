SRC = ("Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyTaprootCommitment, ComputeTaprootMerkleRoot, ComputeTapleafHash, ComputeTapbranchHash "
       "(src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); "
       "XOnlyPubKey::CheckTapTweak, ComputeTapTweakHash (src/pubkey.cpp); secp256k1_xonly_pubkey_tweak_add_check; BIP341")
TAGS = ["bitcoin", "taproot", "bip341", "merkle", "soundness", "tagged-hash", "formal-verification", "bitcoin-mainnet"]

DEFINITION = {
    "definition_name": "BitcoinTapSoundness",
    "definition_title": "Script trees, honest Taproot outputs, and the two hardness assumptions of the script path",
    "natural_language_statement": r"""Names over the Taproot mission's `BitcoinTaproot`; nothing of Core is re-transcribed.

**`Sha256Collision`** — there exist two different byte strings with the same `sha256`.

**`TapTree`** — a binary tree whose leaves carry a leaf version byte and a script (the tree the output's creator built, BIP341). **`TapTree.hash`** is `tapleafHash version script` at a leaf and `tapbranchHash` of the children's hashes at a branch; **`TapTree.leaves`** lists the leaf hashes in order; **`TapTree.subtreesAt T d`** lists the subtrees at depth $d$ (the tree itself at depth 0, nothing below a leaf).

**`TweakCollision q parity P`** — two different 32-byte tweak scalars that both pass `xonlyTweakAddCheck q parity P` (Core's `secp256k1_xonly_pubkey_tweak_add_check`): both carry the internal point $P$ to the output key $q$ with the given parity. This is a discrete-logarithm relation ($t_1 - t_2$ times $G$ is the point at infinity, with $t_1 \ne t_2$ below the group order), which the model does not attempt to rule out.

**`HonestOutput q internal32 parity T`** — `checkTapTweak q internal32 T.hash parity = true`: the output key $q$ is the internal key tweaked by the root of $T$, with parity `parity` (`XOnlyPubKey::CheckTapTweak`).

**`controlInternalKey control`** — bytes 1 to 32 of a control block; **`controlParity control`** — bit 0 of its first byte. These are the two fields `VerifyTaprootCommitment` reads from the control block besides the path.

**Formalization Note.** `tagged`, `tapleafHash`, `tapbranchHash`, `controlNodes`, `taprootMerkleRoot`, `tapTweakHash`, `xonlyTweakAddCheck`, `checkTapTweak`, `verifyTaprootCommitment` are the Taproot mission's; `sha256`, `taggedHash`, `liftX`, `beVal` the serialization and signature missions'. Only `Std` is imported.""",
}

THEOREMS = {
"BitcoinTapSoundness.tagged_collision": dict(title="Equal tagged hashes have equal tag hashes and messages, or exhibit a SHA-256 collision",
    nl=r"""For tags $t, t'$ and messages $m, m'$: if `tagged t m = tagged t' m'` then either `sha256 (ascii t) = sha256 (ascii t')` and $m = m'$, or `Sha256Collision`. The tagged hash is `sha256 (sha256 tag ++ sha256 tag ++ m)` and `sha256` always returns 32 bytes, so equal outer digests of different inputs are a collision and equal inputs split at the 64-byte boundary.""",
    ms=None),
"BitcoinTapSoundness.tapleaf_ne_tapbranch": dict(title="The TapLeaf and TapBranch tags hash differently",
    nl=r"""`sha256 (ascii "TapLeaf") ≠ sha256 (ascii "TapBranch")`, by kernel computation of the model's SHA-256 on the two tags.""",
    ms=None),
"BitcoinTapSoundness.leaf_ne_branch": dict(title="A leaf hash equal to a branch hash is a SHA-256 collision",
    nl=r"""For any leaf version $v$, script $s$ and byte strings $a, b$: `tapleafHash v s = tapbranchHash a b` implies `Sha256Collision`. From `tagged_collision` and `tapleaf_ne_tapbranch`.""",
    ms=None),
"BitcoinTapSoundness.branch_eq": dict(title="Equal branch hashes of 32-byte children have the same children up to order, or exhibit a collision",
    nl=r"""For 32-byte strings $a, b, c, d$: `tapbranchHash a b = tapbranchHash c d` implies $(a = c \land b = d) \lor (a = d \land b = c)$, or `Sha256Collision`. The branch hash sorts its two children lexicographically before concatenating; the length hypotheses split the concatenation.""",
    ms=("The sorted concatenation splits", "`tagged_collision` reduces to equal messages; the four cases of the two lexicographic comparisons each split at byte 32.")),
"BitcoinTapSoundness.path_lands": dict(title="A Merkle path from a 32-byte hash to a tree's root lands on a subtree at the path's depth",
    nl=r"""For a tree $T$, a list of 32-byte path nodes and a 32-byte starting hash $h$: if folding `tapbranchHash` over the nodes from $h$ gives `T.hash`, then there is a subtree $U$ of $T$ at depth equal to the number of nodes with `U.hash = h`, or `Sha256Collision`. By induction on the path: at each step the current hash is a branch hash, so the subtree it lands on is a branch (else `leaf_ne_branch`) and by `branch_eq` the previous hash is one of its children's.""",
    ms=("Induction on the path", "The fold is unrolled from the leaf; `branch_eq` chooses the child, and a leaf at an interior position is `leaf_ne_branch`.")),
"BitcoinTapSoundness.script_path_soundness": dict(title="Script-path soundness at the Merkle level: a verified path opens a committed leaf",
    nl=r"""For a tree $T$, a control block of length $33 + 32k$, a leaf version $v$ and a script $s$: if `taprootMerkleRoot control (tapleafHash v s) = T.hash` (Core's `ComputeTaprootMerkleRoot` lands on the root) then `tapleafHash v s ∈ T.leaves` or `Sha256Collision`. The path nodes of a well-sized control block are 32 bytes each, `path_lands` gives a subtree with the leaf's hash, and that subtree is a leaf (else `leaf_ne_branch`).""",
    ms=None),
"BitcoinTapSoundness.commitment_soundness": dict(title="Script-path soundness at the commitment level: VerifyTaprootCommitment opens only committed leaves, up to a hash collision or a tweak collision",
    nl=r"""For an output key $q$, internal key `internal32`, parity bit and tree $T$ with `HonestOutput q internal32 parity T`, and any control block of length $33 + 32k$ whose internal-key bytes are `internal32` and whose parity bit is `parity`, and any leaf $(v, s)$: if `verifyTaprootCommitment control q (tapleafHash v s) = true` then

`tapleafHash v s ∈ T.leaves`, or `Sha256Collision`, or there is a point $P$ with `liftX (beVal internal32) = some P` and `TweakCollision q parity P`.

If the control block's Merkle root equals the tree's root, `script_path_soundness` applies. Otherwise the two roots give two tweak hashes `tapTweakHash internal32 ·`; equal tweak hashes of different roots are a collision (`tagged_collision`, the internal key being a fixed 32-byte prefix), and different tweak hashes that both pass `xonlyTweakAddCheck` are a `TweakCollision`. This is the BIP341 claim that a spender cannot open a leaf the output's creator did not commit to, stated as a reduction to SHA-256 collision resistance and to the hardness of finding two tweaks for one output key.""",
    ms=None),
}
ORDER = ["BitcoinTapSoundness.tagged_collision", "BitcoinTapSoundness.tapleaf_ne_tapbranch", "BitcoinTapSoundness.leaf_ne_branch",
         "BitcoinTapSoundness.branch_eq", "BitcoinTapSoundness.path_lands", "BitcoinTapSoundness.script_path_soundness",
         "BitcoinTapSoundness.commitment_soundness"]
