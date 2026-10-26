# Read-back: `BitcoinTaproot.merkleRoot_base`

**Binders.** $\mathrm{control}$, $\mathrm{leaf}$ : byte strings (finite lists of 8-bit values).

**Hypothesis.** $|\mathrm{control}| = 33$ (the constant `TAPROOT_CONTROL_BASE_SIZE`, which is $33$).

**Conclusion.**

$$\mathrm{taprootMerkleRoot}(\mathrm{control}, \mathrm{leaf}) = \mathrm{leaf}.$$

Unfolded: $\mathrm{taprootMerkleRoot}(c, h)$ is the left fold of $\mathrm{tapbranchHash}$ over the list $\mathrm{controlNodes}(c)$ starting from $h$, i.e. $h_0 = h$, $h_{j+1} = \mathrm{tapbranchHash}(h_j, N_j)$, result $h_k$. Here $\mathrm{controlNodes}(c)$ is built by first computing the node count $k = \lfloor (|c| \dot- 33)/32 \rfloor$ (natural-number subtraction, truncated at $0$), dropping the first $33$ bytes of $c$, and then taking $k$ successive chunks of $32$ bytes (each chunk is "take $32$" of what remains, then "drop $32$"). With $|\mathrm{control}| = 33$ the count is $k = 0$, the node list is empty, and the fold returns its starting value $\mathrm{leaf}$ unchanged; $\mathrm{tapbranchHash}$ (the tagged hash $\mathrm{tagged}(\texttt{"TapBranch"}, \cdot)$ of the lexicographically ordered concatenation of its two arguments) is never applied.

**Edge cases the quantifiers include.** $\mathrm{leaf}$ of any length including empty; the contents of the $33$ control bytes are unconstrained (no parity, key, or on-curve condition is involved).
