# Read-back: `BitcoinTaproot.sigops_budget`

**Binders.** $c$ : a `TapCtx` record (flags; transaction $\mathrm{tx}$; list $\mathrm{spent}$; index $\mathrm{nIn}$); $\mathrm{ed}$ : an `ExecData` record; $\mathrm{ts}$ : a `TapState` record ($\mathrm{st}$ : interpreter state; $\mathrm{weightLeft} \in \mathbb{Z}$; $\mathrm{codeseparatorPos}, \mathrm{opcodePos} \in \mathbb{N}$); $\mathrm{pubkey}, \mathrm{sig}$ : byte strings; $\mathrm{rest}$ : a list of byte strings.

**Hypotheses.**
1. $\mathrm{ts}.\mathrm{st}.\mathrm{stack} = \mathrm{pubkey} :: \mathrm{sig} :: \mathrm{rest}$ (main stack, top first);
2. $\mathrm{sig} \neq [\,]$;
3. $\mathrm{ts}.\mathrm{weightLeft} < 50$ as integers (the constant `VALIDATION_WEIGHT_PER_SIGOP_PASSED`, which is the integer $50$).

**Conclusion.**

$$\mathrm{tapExecOp}(c, \mathrm{ed}, \mathrm{true}, \texttt{0xac}, \mathrm{ts}) = \mathrm{none},$$

where $\texttt{0xac}$ is `OP_CHECKSIG`.

Unfolded. For `OP_CHECKSIG`, $\mathrm{tapExecOp}$ requires the stack shape of hypothesis 1 (else $\mathrm{none}$) and calls $\mathrm{evalChecksigTapscript}(c, \mathrm{ed}', \mathrm{sig}, \mathrm{pubkey}, \mathrm{ts}.\mathrm{weightLeft})$, where $\mathrm{ed}'$ is $\mathrm{ed}$ with `codeseparatorPos` replaced by $\mathrm{ts}.\mathrm{codeseparatorPos}$. In that function $\mathrm{success} := (\mathrm{sig} \neq [\,]) = \mathrm{true}$ by hypothesis 2, so $\mathrm{weight} := \mathrm{weightLeft} - 50$ (integer subtraction); the first test "if $\mathrm{success} \land \mathrm{weight} < 0$ then $\mathrm{none}$" fires because $\mathrm{weightLeft} < 50$ gives $\mathrm{weight} < 0$. This test precedes the public-key length tests ($|\mathrm{pubkey}| = 0 \Rightarrow \mathrm{none}$; $|\mathrm{pubkey}| = 32 \Rightarrow$ Schnorr check; other lengths $\Rightarrow$ accept) and the signature verification, none of which are reached. A $\mathrm{none}$ from $\mathrm{evalChecksigTapscript}$ makes $\mathrm{tapExecOp}$ return $\mathrm{none}$.

**Edge cases the quantifiers include.** $\mathrm{pubkey}$ of any length, including empty or non-32-byte; $\mathrm{sig}$ of any non-zero length (not only 64/65); $\mathrm{weightLeft}$ negative or exactly $49$; $\mathrm{rest}$ empty; arbitrary $c$ and $\mathrm{ed}$ (never consulted).
