SRC = ("Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48, ComputeMerkleRoot, src/consensus/merkle.cpp lines 51-73, with the CVE-2012-2459 comment at lines 16-50: "
       "https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/merkle.cpp#L51")
TAGS = ["bitcoin", "consensus", "merkle-tree", "cve-2012-2459", "formal-verification", "bitcoin-mainnet"]

DEFINITION = {
    "definition_name": "BitcoinMerkle",
    "definition_title": "ComputeMerkleRoot with Bitcoin's odd-level duplication and mutation check",
    "natural_language_statement": r"""Hashes form an arbitrary type $H$ with decidable equality. The pairwise hash (`SHA256D64` on two concatenated hashes in the source) is an abstract function $c : H \to H \to H$, and the all-zero hash returned for an empty list is an abstract $z : H$.

**One level.** $\mathrm{pairUp}_c$ maps a list to the list of $c(\ell_{2i}, \ell_{2i+1})$ over aligned pairs; an odd trailing element $a$ contributes $c(a, a)$, which is the source's `hashes.push_back(hashes.back())` followed by pairwise hashing. Its length is $\lceil |\ell| / 2 \rceil$ (`pairUp_length`, used to justify termination).

**The mutation test.** $\mathrm{hasEqualPair}(\ell)$ is true when some aligned pair $(\ell_{2i}, \ell_{2i+1})$ with $2i+1 < |\ell|$ has equal entries. The duplicated trailing element is not tested, because in the source the test runs before the duplication.

**The loop.** $\mathrm{rootLoop}_{c,z}(\ell, m)$: while $|\ell| > 1$, replace $m$ by $m \lor \mathrm{hasEqualPair}(\ell)$ and $\ell$ by $\mathrm{pairUp}_c(\ell)$; on exit return the remaining hash (or $z$ for an empty list) together with $m$.

**The root.** $\mathrm{computeMerkleRoot}_{c,z}(\ell) = \mathrm{rootLoop}_{c,z}(\ell, \mathtt{false})$, a pair (root, mutated), as `ComputeMerkleRoot(hashes, &mutated)`.

These definitions fix the semantics of the block Merkle root and of the CVE-2012-2459 defence for use by block-structure validation.

**Formalization Note.** `rootLoop` is defined by well-founded recursion on the list length. Equality in `hasEqualPair` is `decide (a = b)` on $H$. Nothing is assumed about $c$; in particular no collision-resistance. Only `Std` is imported.""",
}

THEOREMS = {
"BitcoinMerkle.root_nil": dict(title="Merkle root of no transactions",
    nl=r"""For every pairwise hash $c$ and zero hash $z$, $\mathrm{computeMerkleRoot}_{c,z}([\,]) = (z, \mathtt{false})$: the empty list yields the zero hash with the mutation flag clear, as `if (hashes.size() == 0) return uint256();`.""",
    ms=("ComputeMerkleRoot — empty list", "Evaluate the loop on the empty list: zero hash, flag clear.")),
"BitcoinMerkle.root_single": dict(title="Merkle root of a single hash",
    nl=r"""For every $c$, $z$ and hash $a$, $\mathrm{computeMerkleRoot}_{c,z}([a]) = (a, \mathtt{false})$: a single hash is its own root and no level is processed, so the flag stays clear. In a block with only a coinbase, the Merkle root is the coinbase transaction id.""",
    ms=("ComputeMerkleRoot — single hash", "Evaluate the loop on a singleton: the hash itself, flag clear.")),
"BitcoinMerkle.root_pair": dict(title="Merkle root of two hashes",
    nl=r"""For every $c$, $z$ and hashes $a, b$, $\mathrm{computeMerkleRoot}_{c,z}([a, b]) = (c(a, b),\ [a = b])$: one level is processed, producing $c(a,b)$, and the flag is set exactly when the two leaves are equal. This is the smallest instance of the mutation check.""",
    ms=("ComputeMerkleRoot — two hashes", "Evaluate one level: the pair hash, flag iff the leaves are equal.")),
"BitcoinMerkle.rootLoop_fst": dict(title="The root does not depend on the incoming flag",
    nl=r"""For every $c$, $z$, list $\ell$ and flags $m, m'$, the first components agree: $\mathrm{rootLoop}_{c,z}(\ell, m).1 = \mathrm{rootLoop}_{c,z}(\ell, m').1$. The mutation flag is carried alongside the computation and never influences which hashes are produced.""",
    ms=("Loop — root independent of the flag", "Show by induction on the loop that the first component ignores the flag.")),
"BitcoinMerkle.rootLoop_sticky": dict(title="Once set, the mutation flag stays set",
    nl=r"""For every $c$, $z$ and list $\ell$, $\mathrm{rootLoop}_{c,z}(\ell, \mathtt{true}).2 = \mathtt{true}$: the flag is only ever combined with further tests by disjunction, so a mutation detected at one level is reported at the end regardless of what later levels contain.""",
    ms=("Loop — the flag is sticky", "Show by induction on the loop that a set flag is returned set.")),
"BitcoinMerkle.pairUp_append_even": dict(title="One level distributes over an even split",
    nl=r"""For every $c$ and lists $\ell, r$ with $|\ell|$ even, $\mathrm{pairUp}_c(\ell \mathbin{+\!\!+} r) = \mathrm{pairUp}_c(\ell) \mathbin{+\!\!+} \mathrm{pairUp}_c(r)$. When the prefix has even length the pair boundaries of the concatenation align with those of the two parts, so a level can be computed blockwise. The hypothesis is necessary: an odd prefix would pair its last element with the first element of $r$.""",
    ms=("pairUp — distributes over even-length prefixes", "Prove pairUp (l ++ r) = pairUp l ++ pairUp r for even |l|, by induction two elements at a time.")),
"BitcoinMerkle.hasEqualPair_append_even": dict(title="The mutation test distributes over an even split",
    nl=r"""For all lists $\ell, r$ with $|\ell|$ even, $\mathrm{hasEqualPair}(\ell \mathbin{+\!\!+} r) = \mathrm{hasEqualPair}(\ell) \lor \mathrm{hasEqualPair}(r)$. With aligned pair boundaries, an equal aligned pair of the concatenation lies entirely in $\ell$ or entirely in $r$.""",
    ms=("hasEqualPair — distributes over even-length prefixes", "Prove the pair test of a concatenation is the disjunction of the parts' tests for even |l|.")),
"BitcoinMerkle.dup_leaf": dict(title="CVE-2012-2459 at the leaf level: duplicate last transaction",
    nl=r"""For every $c$, $z$, non-empty list $\ell$ of even length and hash $a$,
$$\mathrm{root}(\ell \mathbin{+\!\!+} [a]) = \mathrm{root}(\ell \mathbin{+\!\!+} [a, a]) \qquad\text{and}\qquad \mathrm{mutated}(\ell \mathbin{+\!\!+} [a, a]) = \mathtt{true}.$$
The list $\ell \mathbin{+\!\!+} [a]$ has odd length, so the loop duplicates its last element; appending a second copy of $a$ explicitly produces the same first level, hence the same root, while the explicit copy forms an equal aligned pair and is flagged. Non-emptiness of $\ell$ is required: $[a]$ is its own root but $[a, a]$ hashes to $c(a,a)$.""",
    ms=("CVE-2012-2459 — leaf level", "Prove root equality and detection for a duplicated last leaf after a non-empty even prefix.")),
"BitcoinMerkle.dup_block": dict(title="CVE-2012-2459 in general: duplicating an aligned trailing block",
    nl=r"""For every pairwise hash $c$, zero hash $z$, level $k \in \mathbb N$, non-empty list $\ell$ whose length is a multiple of $2^{k+1}$, and block $t$ of exactly $2^{k}$ hashes,
$$\mathrm{root}(\ell \mathbin{+\!\!+} t) = \mathrm{root}(\ell \mathbin{+\!\!+} t \mathbin{+\!\!+} t) \qquad\text{and}\qquad \mathrm{mutated}(\ell \mathbin{+\!\!+} t \mathbin{+\!\!+} t) = \mathtt{true},$$
where root and mutated are the two components of $\mathrm{computeMerkleRoot}_{c,z}$, the transcription of `ComputeMerkleRoot`.

Under the alignment hypotheses, $t$ occupies a complete aligned subtree that collapses to a single node after $k$ levels; at that level $\ell \mathbin{+\!\!+} t$ has odd length and the source duplicates the node, while $\ell \mathbin{+\!\!+} t \mathbin{+\!\!+} t$ already carries the copy as an equal aligned pair. The two computations then coincide, and the copy is detected by the per-level check. With $k = 0$ this is the duplicated last transaction; with $k = 1$ and $\ell$ of length four it is the $[1,2,3,4,5,6]$ versus $[1,2,3,4,5,6,5,6]$ example of the source comment.

This is the general statement of the defence against CVE-2012-2459: every duplication of this shape is root-preserving, which is the attack, and is flagged, which is the defence. Nothing is assumed about $c$; the result is about the loop structure alone.

**Formalization Note.** The non-emptiness of $\ell$ is necessary, since a single-node list is returned without processing while its doubled form is hashed once more. The statement is proved for the loop with an arbitrary incoming flag and specialized to `computeMerkleRoot`.""",
    ms=None),
}
ORDER = ["BitcoinMerkle.root_nil","BitcoinMerkle.root_single","BitcoinMerkle.root_pair","BitcoinMerkle.rootLoop_fst",
         "BitcoinMerkle.rootLoop_sticky","BitcoinMerkle.pairUp_append_even","BitcoinMerkle.hasEqualPair_append_even",
         "BitcoinMerkle.dup_leaf","BitcoinMerkle.dup_block"]
