## The claim

A Taproot output commits to a tree of scripts through its tweaked key, and a spender opens one leaf by presenting a control block: the internal key, a parity bit, and a Merkle path. The design claim of BIP341 is that nobody can open a leaf the output's creator did not put in the tree. The Taproot mission transcribed `VerifyTaprootCommitment` and the tagged hashes; this mission proves the claim about them as a *constructive* reduction: any control block that passes verification for an honestly built output either opens a committed leaf, or names two different byte strings with the same SHA-256, or names two different 32-byte tweak scalars that carry the same internal key to the same output key (a discrete-logarithm relation on secp256k1).

## Revision 2

The first revision (`BitcoinTapSoundness`, deprecated) stated the collision alternatives as closed propositions, "some collision exists", which are provable by counting and therefore made every row trivially true; its tweak alternative also lacked a length constraint, so a passing tweak and its zero-prefixed copy already satisfied it. Here every collision is a pair of explicit strings built from the inputs (`Collides x y` with `x`, `y` named in the statement or returned by the computable `walk` / `scriptPathWitness`), and the two tweaks are the two 32-byte `TapTweak` hashes of the control block's root and the tree's root.

## What is proved

- **Tagged hashes** (`tagged_pre`, `tagged_collision`, `tapleaf_ne_tapbranch`, `leaf_ne_branch`): a tagged hash is the SHA-256 of its explicit preimage; equal tagged hashes have equal tag hashes and messages or their preimages collide; the `TapLeaf` and `TapBranch` tags hash differently (by computation); so a leaf hash equal to a branch hash names a collision.
- **Branches** (`branch_eq`): equal branch hashes of 32-byte children have the same two children in some order, or the two `TapBranch` preimages collide.
- **Paths** (`path_lands`): `walk` along a path of 32-byte nodes from a 32-byte hash to the root lands on a subtree at the path's depth, or returns a colliding pair.
- **Merkle level** (`script_path_soundness`): a well-sized control block whose `ComputeTaprootMerkleRoot` lands on a tree's root opens one of the tree's leaves, or `scriptPathWitness` names a collision.
- **Commitment level** (`commitment_soundness`, the goal): if `q` is `internal32` tweaked by the root of `T`, then any control block with that internal key and parity that passes `VerifyTaprootCommitment` for a leaf opens a leaf of `T`, or names a SHA-256 collision (in the path, or between the two `TapTweak` preimages), or names two 32-byte tweaks for `q`.

## What this rests on and what it does not say

The theorems are about the model's SHA-256 and secp256k1 arithmetic as the serialization, signature and Taproot missions define them. The commitment theorem fixes the internal key and parity of the control block to the honest output's: a control block with a different internal key is a claim about a different key pair, which is the discrete-logarithm problem itself and outside the model. Nothing is said about the key path, about tapscript execution after the commitment check, or about the annex. ([`interpreter.cpp`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp), [`pubkey.cpp`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/pubkey.cpp))
