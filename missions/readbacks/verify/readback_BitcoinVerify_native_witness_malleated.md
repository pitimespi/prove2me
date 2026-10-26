# Read-back: `BitcoinVerify.native_witness_malleated`

**Binders and hypothesis.** Universally quantified: `tap`, a Taproot handler (any function from a context, a list of byte strings, and a byte string to a Boolean — completely unconstrained); $c$, a verification context (a record of a consensus flag set `c.flags`, a transaction `c.tx`, an input index `c.nIn`, and an integer amount `c.amount`); `scriptSig` and `spk`, byte strings; $w$, a list of byte strings (the witness stack). Three hypotheses:

- `hf`: the `witness` field of `c.flags` is true;
- `hw`: `isWitnessProgram spk` is not "nothing", i.e. `spk` has between 4 and 42 bytes, its first byte is $0$ or lies in $[\mathtt{0x51}, \mathtt{0x60}]$, and its second byte plus $2$ equals its length;
- `hs`: `scriptSig` is not the empty byte string.

**Conclusion.**

$$\mathrm{verifyScript}(\mathrm{tap}, c, \mathrm{scriptSig}, \mathrm{spk}, w) = \mathrm{false}.$$

**Unfolding `verifyScript` along the hypotheses.** `verifyScript` first evaluates `scriptSig` on the empty stack with signature version `base` (after the $10000$-byte size test and the byte-level parse); if that fails, the result is false. Otherwise it evaluates `spk` on the resulting stack; failure gives false. If the resulting stack is empty or its top casts to false (`topTrue`), the result is false. Otherwise it computes the "native" verdict: because `c.flags.witness` is true (hypothesis `hf`) and `isWitnessProgram spk` yields some pair (hypothesis `hw`), the native verdict is `some false` whenever `scriptSig` is non-empty — which hypothesis `hs` guarantees — and `verifyWitnessProgram` is never called. A native verdict of `some false` makes `verifyScript` return false. Hence on every path the result is false: either one of the preliminary evaluations fails, or the native check rejects because of the non-empty `scriptSig`.

**Role of each hypothesis.** `hf` is what makes the native branch be computed at all (with the witness flag off, `native` is `none` and the function would proceed to the P2SH / plain branches). `hw` is what selects the witness-program arm. `hs` is what forces the `some false` arm. The handler `tap`, the witness $w$, the version and program recovered from `spk`, and the other flags in `c.flags` play no role in the conclusion.

**What is not said.** The theorem does not say what happens when `scriptSig` is empty (then `verifyWitnessProgram` would be consulted, and the result could be true or false); it does not say that the evaluations of `scriptSig` and `spk` succeed or fail — the conclusion is false either way; it does not say anything when the `witness` flag is off (in that case the function may well return true for the same inputs, via the plain branch); it does not mention the `p2sh` flag or `isPayToScriptHash` (irrelevant since a witness program's first byte is never $\mathtt{0xa9}$); it does not constrain the witness $w$ (empty or not); and it does not say that the version or program of `spk` is of any particular kind — all versions $0$ through $16$ and all program lengths $2$ through $40$ are covered uniformly.
