# Read-back: `BitcoinVerify.unknown_witness_version`

**Binders and hypothesis.** Universally quantified: `tap`, a Taproot handler (any function from a context, a list of byte strings and a byte string to a Boolean); $c$, a verification context with consensus flags `c.flags`, transaction `c.tx`, input index `c.nIn`, integer amount `c.amount`; $v$, a natural number; `prog`, a byte string; $w$, a list of byte strings (the witness). Five hypotheses:

- `hf`: `c.flags.witness = true`;
- `hv`: $v \le 16$;
- `hu`: $2 \le v$, or ($v = 1$ and $|\mathrm{prog}| \ne 32$);
- `h2`: $2 \le |\mathrm{prog}|$;
- `h40`: $|\mathrm{prog}| \le 40$.

Together `hv` and `hu` give $1 \le v \le 16$, excluding $v = 0$ entirely and excluding the single combination $v = 1$ with a 32-byte program.

**Conclusion.** With $\pi = \mathrm{witnessBytes}(v, \mathrm{prog}) = (\mathtt{0x50} + v)\ \ |\mathrm{prog}|\ \ \mathrm{prog}$ (the opcode `OP_v`, a direct-push length byte, then the program; $|\pi| = |\mathrm{prog}| + 2 \in [4, 42]$):
$$\mathrm{verifyScript}(\mathrm{tap}, c, [], \pi, w) = \mathrm{castToBool}(\mathrm{prog}).$$
This is an equality of Booleans: the verification succeeds exactly when the program bytes cast to true, and fails exactly when they cast to false (all zero bytes, or all zero but a final $\mathtt{0x80}$).

**Unfolding the left-hand side.** The empty scriptSig evaluates to the empty stack. $\pi$ is evaluated with version `base`: the opcode byte $\mathtt{0x50} + v \in [\mathtt{0x51}, \mathtt{0x60}]$ is `OP_v`, which pushes the minimal encoding of the number $v$; the push adds `prog`. The top-first stack is $[\mathrm{prog}, \mathrm{serialize}(v)]$ and `topTrue` is $\mathrm{castToBool}(\mathrm{prog})$; when it is false `verifyScript` returns false, matching the right side. Otherwise, since the `witness` flag is on (`hf`), the native branch computes `isWitnessProgram π`: length in $[4, 42]$ by `h2`, `h40`; first byte in $[\mathtt{0x51}, \mathtt{0x60}]$ by `hv` and $v \ge 1$; second byte $|\mathrm{prog}| = |\pi| - 2$; so it yields $\mathrm{some}(v, \mathrm{prog})$ with $\mathrm{decodeOpN}(\mathtt{0x50} + v) = v$. The scriptSig is empty, so the verdict is `verifyWitnessProgram tap c w v prog false`.

**Unfolding `verifyWitnessProgram`.** $v \ne 0$, so the version-0 arm is skipped. The Taproot arm requires $v = 1$ and $|\mathrm{prog}| = 32$ and not-P2SH; hypothesis `hu` rules out the first two together. The remaining arm returns true both when `isPayToAnchor v prog` holds ($v = 1$ and $\mathrm{prog} = [\mathtt{0x4e}, \mathtt{0x73}]$) and when it does not. So the verdict is true, the witness $w$ being ignored entirely — it may be empty or arbitrary. Combining: the left side is $\mathrm{castToBool}(\mathrm{prog})$.

**Logical content.** For every handler, every context with the witness flag on, every version $1..16$ and every program of $2..40$ bytes except the (version $1$, 32-byte) case, and every witness, the full verification with an empty scriptSig succeeds iff the program bytes cast to true. The handler `tap` and the `taproot`, `p2sh` and other flags do not affect the result; neither does the content of $w$.

**What is not said.** Nothing about $v = 0$ (P2WSH/P2WPKH, where lengths matter); nothing about $v = 1$ with a 32-byte program (the Taproot case, which depends on `c.flags.taproot` and `tap`); nothing about $v > 16$ (where `witnessBytes` is not a witness program); nothing when the `witness` flag is off; nothing for a non-empty scriptSig; nothing about P2SH-wrapped programs. The theorem does not say the outcome is "true": for a program of all zero bytes it asserts the verification is false.
