# Read-back: `BitcoinTaproot.merkleRoot_snoc`

**Binders.** $\mathrm{control}$, $\mathrm{node}$, $\mathrm{leaf}$ : byte strings (finite lists of 8-bit values).

**Hypotheses.**
1. $33 \le |\mathrm{control}|$ (where $33$ is `TAPROOT_CONTROL_BASE_SIZE`);
2. $(|\mathrm{control}| - 33) \bmod 32 = 0$ (the subtraction is natural-number subtraction, but by hypothesis 1 it is an ordinary difference here; $32$ is `TAPROOT_CONTROL_NODE_SIZE`);
3. $|\mathrm{node}| = 32$.

**Conclusion.**

$$\mathrm{taprootMerkleRoot}(\mathrm{control} \,\Vert\, \mathrm{node},\; \mathrm{leaf}) \;=\; \mathrm{tapbranchHash}\big(\mathrm{taprootMerkleRoot}(\mathrm{control}, \mathrm{leaf}),\; \mathrm{node}\big).$$

Unfolded. $\mathrm{taprootMerkleRoot}(c, h)$ is the left fold $h_0 = h,\ h_{j+1} = \mathrm{tapbranchHash}(h_j, N_j)$ over the list $N_0, \dots, N_{k-1} = \mathrm{controlNodes}(c)$, where $k = \lfloor(|c| \dot- 33)/32\rfloor$ (truncated natural subtraction) and $N_j$ is the $j$-th consecutive $32$-byte chunk of $c$ after its first $33$ bytes (each chunk is the "take $32$" of the remaining suffix; a trailing partial chunk is never produced because $k$ is the floor). $\mathrm{tapbranchHash}(x, y) = \mathrm{tagged}(\texttt{"TapBranch"}, x\Vert y)$ if $x <_{\mathrm{lex}} y$, and $\mathrm{tagged}(\texttt{"TapBranch"}, y \Vert x)$ otherwise, where $<_{\mathrm{lex}}$ is byte-wise lexicographic strict order (empty is less than non-empty, equal strings are not less), and $\mathrm{tagged}(T, m) = \mathrm{SHA256}(\mathrm{SHA256}(T)\Vert\mathrm{SHA256}(T)\Vert m)$ with $T$ the UTF-8 bytes of the tag. So the statement says: under the hypotheses, the node list of $\mathrm{control}\Vert\mathrm{node}$ is the node list of $\mathrm{control}$ followed by $\mathrm{node}$ as one more $32$-byte chunk, and the fold over the extended list equals one more $\mathrm{tapbranchHash}$ step applied to the fold over the original list, with the accumulated hash as first argument and $\mathrm{node}$ as second.

**Edge cases the quantifiers include.** $|\mathrm{control}| = 33$ (then the inner root is just $\mathrm{leaf}$ and the claim is $\mathrm{tapbranchHash}(\mathrm{leaf}, \mathrm{node})$); $\mathrm{leaf}$ of arbitrary length; $\mathrm{control}$ longer than the $4129$-byte maximum used elsewhere (no maximum is assumed here); control bytes otherwise unconstrained.
