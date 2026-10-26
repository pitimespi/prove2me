## Why the Merkle root and its mutation check matter

A Bitcoin block header commits to its transactions through a single 32-byte **Merkle root**: the transaction hashes are paired and hashed, the results paired and hashed again, until one hash remains. Every node recomputes this root from the block body and rejects the block if it does not match the header. Bitcoin's construction has a quirk that later became a vulnerability: when a level has an odd number of hashes, the last one is **duplicated** before pairing. Consequently the transaction lists $[1,2,3,4,5,6]$ and $[1,2,3,4,5,6,5,6]$ have the same root, and an attacker could relay the second, invalid, block with the first block's header; a node that marked that header permanently invalid would then reject the genuine block (CVE-2012-2459). Bitcoin Core defends by detecting, at every level, two **equal adjacent hashes in an aligned pair** and treating the block as having a bad root. ([`ComputeMerkleRoot`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/merkle.cpp#L51) and the comment above it.)

This mission transcribes that loop and proves that the defence does what its comment claims for the general form of the construction: duplicating any aligned block of $2^k$ trailing leaves preserves the root and is detected, at the level where that block has collapsed to one node.

## The loop, as a function on lists

Hashes are an arbitrary type $H$ with decidable equality; the pairwise hash is an abstract $c : H \times H \to H$ (in the source, `SHA256D64` on the two concatenated hashes), and the zero hash returned for an empty list is an abstract $z$. The three operations are, for a list of hashes $\ell$:

- **pairUp**$(\ell)$: $c$ applied to successive aligned pairs; an odd trailing element $a$ contributes $c(a, a)$. This is `hashes.push_back(hashes.back())` followed by the pairwise hashing.
- **hasEqualPair**$(\ell)$: true when some aligned pair $(\ell_{2i}, \ell_{2i+1})$ with $2i + 1 < |\ell|$ consists of equal hashes. The duplicated trailing element is *not* tested: the check runs before the duplication.
- **rootLoop**$(\ell, m)$: while $|\ell| > 1$, replace $m$ by $m \lor \mathrm{hasEqualPair}(\ell)$ and $\ell$ by $\mathrm{pairUp}(\ell)$; on exit return the single remaining hash (or $z$ if the list is empty) together with $m$.

**computeMerkleRoot**$(\ell) = \mathrm{rootLoop}(\ell, \mathtt{false})$ returns the pair (root, mutated), exactly as `ComputeMerkleRoot(hashes, &mutated)`.

## Formalization targets

### Goal — duplication of an aligned block is root-preserving and detected
For every $k$, every non-empty prefix $\ell$ whose length is a multiple of $2^{k+1}$, and every block $t$ of exactly $2^k$ hashes,
$$
\mathrm{root}(\ell \mathbin{+\!\!+} t) = \mathrm{root}(\ell \mathbin{+\!\!+} t \mathbin{+\!\!+} t)
\qquad\text{and}\qquad
\mathrm{mutated}(\ell \mathbin{+\!\!+} t \mathbin{+\!\!+} t) = \mathtt{true}.
$$
This is `BitcoinMerkle.dup_block`. The alignment hypotheses are what make $t$ collapse to a single node at level $k$, where the duplicate then sits in an aligned pair; $\ell \ne [\,]$ is needed because a list of one hash is its own root while a list of two is not. With $k = 0$ it is the classic duplicated-last-transaction case; with $k = 1$ it is the $[1,\dots,6,5,6]$ example of the source comment.

### Supporting milestones
1. **Base cases** (`root_nil`, `root_single`, `root_pair`): the empty list gives $(z, \mathtt{false})$; one hash gives $(a, \mathtt{false})$; two give $(c(a,b),\ a = b)$.
2. **Flag independence** (`rootLoop_fst`): the root does not depend on the incoming flag.
3. **Flag is sticky** (`rootLoop_sticky`): once set, the flag stays set through the remaining levels.
4. **One level distributes over an even split** (`pairUp_append_even`, `hasEqualPair_append_even`): for $|\ell|$ even, $\mathrm{pairUp}(\ell \mathbin{+\!\!+} r) = \mathrm{pairUp}(\ell) \mathbin{+\!\!+} \mathrm{pairUp}(r)$ and likewise for the pair test.
5. **Leaf-level case** (`dup_leaf`): the goal at $k = 0$, stated directly.

## What the result establishes

The goal is a kernel-checked statement about the transcribed loop: for the entire family of duplications that CVE-2012-2459 is built on, the root is unchanged and the mutation flag is raised. Together with the base cases it fixes the exact semantics of the odd-level rule and of the check, including the fact that the self-pairing of a duplicated trailing element is never itself flagged.

What the result does not say is also worth stating. It does not claim that every root collision is detected; that would require assumptions on the hash function (the source comment says "assuming no double-SHA256 collisions"), and $c$ is here an arbitrary function. Nor does it claim anything about the byte-level `SHA256D64` or about transaction serialization; those belong to the hash and serialization layer. What formalizing adds is the general $k$ statement with its precise alignment conditions, which the source states only by example.

Status: all statements are open with intentional placeholder proofs. Nothing about compiled Bitcoin Core is claimed.

## Where the obvious argument fails

The natural first attempt is to compute both sides for small lists and generalize. It fails on the $k$-level statement because the two lists differ in length by $2^k$ and go through $k$ levels before the duplicate appears as a pair. The argument has to track two facts through the loop at once: that the root is insensitive to the flag (so the two runs can be compared level by level with different flags), and that the flag, once raised at level $k$, survives to the end. Both are separate milestones for that reason.

The alignment hypotheses are the second trap. Without $2^{k+1} \mid |\ell|$ the block $t$ straddles a pair boundary and its two copies do not collapse to equal nodes; without $|t| = 2^k$ the copies collapse at different levels. The theorem is false without them, and the base case $\ell = [\,]$ shows that non-emptiness is needed too.

## Formalization scope

$H$ is a type parameter with `DecidableEq`; $c$ and $z$ are parameters. Lists are Lean `List`s, so `pairUp` and `hasEqualPair` are structurally recursive, and `rootLoop` is defined by well-founded recursion on the list length with the lemma $|\mathrm{pairUp}(\ell)| = \lceil |\ell| / 2 \rceil$ supplied in the definition file to justify termination. Equality in `hasEqualPair` is `decide (a = b)` on $H$, matching `hashes[pos] == hashes[pos + 1]` on `uint256`. The `mutated` pointer being null in the source (as in `BlockWitnessMerkleRoot`) only suppresses the output; the model always computes the flag.

A trivializing formalization would restrict $H$ to a type with a trivial hash or define the root by a different, non-duplicating rule; the definitions are fixed to the source's loop. Out of scope: `MerkleComputation` (Merkle branches), `BlockMerkleRoot`'s leaf extraction, the witness root's zero coinbase leaf, and any collision-resistance assumption on $c$.

No Mathlib is required; the development imports only `Std`. Proofs of milestones in any order are welcome, and the distribution lemmas are reusable by any later Merkle-branch work.

## Selected references

- Bitcoin Core contributors. *`ComputeMerkleRoot`*, `src/consensus/merkle.cpp` at revision `a773e1e33b349dc819b5a0edc1c7a4839dc73b48`, lines 16–73 including the CVE-2012-2459 comment. [Source](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/merkle.cpp)
- Forrest Voight. *CVE-2012-2459: Bitcoin block Merkle root duplication*, 2012. [Advisory](https://bitcointalk.org/?topic=102395)
- Satoshi Nakamoto. *Bitcoin: A Peer-to-Peer Electronic Cash System*, 2008, section 7. [Paper](https://bitcoin.org/bitcoin.pdf)
