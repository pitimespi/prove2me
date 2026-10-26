# Read-back: `BitcoinVerify.witness_unexpected`

**Binders and hypothesis.** Universally quantified: `tap`, a Taproot handler (any function from a context, a list of byte strings and a byte string to a Boolean); $c$, a verification context with consensus flags `c.flags`, transaction `c.tx`, input index `c.nIn`, integer amount `c.amount`; `scriptSig` and `spk`, byte strings; $w$, a list of byte strings (the witness). Four hypotheses:

- `hf`: `c.flags.witness = true`;
- `hw`: `isWitnessProgram spk` is nothing — `spk` is not of the form (first byte $0$ or in $[\mathtt{0x51}, \mathtt{0x60}]$, second byte equal to the length minus 2, total length $4..42$);
- `hp`: `isPayToScriptHash spk = false` — `spk` is not a 23-byte string with $\mathtt{0xa9}$, $\mathtt{0x14}$ at indices $0, 1$ and $\mathtt{0x87}$ at index $22$;
- `hne`: $w \ne []$, the witness has at least one element.

The `p2sh` flag is not constrained.

**Conclusion.**

$$\mathrm{verifyScript}(\mathrm{tap}, c, \mathrm{scriptSig}, \mathrm{spk}, w) = \mathrm{false}.$$

**Unfolding `verifyScript` along the hypotheses.** `verifyScript` evaluates `scriptSig` on the empty stack (version `base`, with the $10000$-byte test and the byte-level parse); failure gives false. It evaluates `spk` on the result; failure gives false. If the resulting stack is empty or its top casts to false, false. Otherwise the native verdict: the `witness` flag is on, but by `hw` `spk` is not a witness program, so `native` is `none`. The P2SH branch is entered only if `c.flags.p2sh` is true and `isPayToScriptHash spk` is true; by `hp` the latter is false, so regardless of the `p2sh` flag the branch is skipped. The final branch returns false when `c.flags.witness` is true and $w$ is non-empty — both given by `hf` and `hne` — and true otherwise. Hence every path yields false: either a preliminary evaluation fails or a true top is not produced, or the "unexpected witness" rejection fires.

**Role of each hypothesis.** `hf` enables the final rejection (and would also have enabled the native branch, which `hw` disables); `hw` keeps the native verdict at `none`; `hp` keeps the P2SH branch (which has its own witness handling) out; `hne` makes the final rejection fire. The handler `tap`, the `p2sh`, `taproot`, `dersig`, `cltv`, `csv`, `nulldummy` flags, the transaction, and the contents of `scriptSig` and $w$ (beyond non-emptiness) do not affect the conclusion.

**Logical content.** For every handler, every context with the witness flag on, every scriptSig, every output script that is neither a witness program nor a P2SH script, and every non-empty witness, the verification fails.

**What is not said.** Nothing when $w = []$ (then the result would depend on the two evaluations and the top of the stack); nothing when the `witness` flag is off (then a non-empty witness is not rejected by this path); nothing for P2SH output scripts (their witness handling is separate: a non-witness redeem script with a non-empty witness is rejected there too, but that is not this theorem); nothing for witness-program output scripts. The theorem does not say that the evaluations of `scriptSig` or `spk` succeed, nor that they fail — the conclusion is false either way. It does not say anything about which element of $w$ is "unexpected"; a witness of a single empty byte string already satisfies `hne`.
