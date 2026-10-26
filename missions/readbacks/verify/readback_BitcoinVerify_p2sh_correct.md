# Read-back: `BitcoinVerify.p2sh_correct`

**Binders and hypothesis.** Universally quantified: `tap`, a Taproot handler (an arbitrary function from a context, a list of byte strings and a byte string to a Boolean); $c$, a verification context (flags `c.flags`, transaction `c.tx`, input index `c.nIn`, integer amount `c.amount`); `args`, a list of byte strings; `redeem` and $h$, byte strings. Seven hypotheses:

- `hp`: `c.flags.p2sh = true`;
- `hh`: $|h| = 20$;
- `hargs`: every element $a$ of `args` has $|a| \le 520$ (`MAX_SCRIPT_ELEMENT_SIZE`);
- `hred`: $|\mathrm{redeem}| \le 520$;
- `hn`: $|\mathrm{args}| + 2 \le 1000$ (`MAX_STACK_SIZE`), where $|\mathrm{args}|$ is the number of elements;
- `hsz`: the byte length of `pushesBytes (args ++ [redeem])` is at most $10000$ (`MAX_SCRIPT_SIZE`);
- `hnw`: `isWitnessProgram redeem` is "nothing" (the redeem script is not of the form version-byte, length byte $2..40$, program, with total length $4..42$).

Note that `c.flags.witness` is **not** constrained by any hypothesis; the statement is claimed for both values.

**Conclusion.** A biconditional. Let
$$\sigma = \mathrm{pushesBytes}(\mathrm{args} \,\|\, [\mathrm{redeem}]), \qquad \pi = \mathrm{p2shBytes}(h) = \mathtt{0xa9}\ \mathtt{0x14}\ h\ \mathtt{0x87}.$$
Then
$$\mathrm{verifyScript}(\mathrm{tap}, c, \sigma, \pi, []) = \mathrm{true} \iff \mathrm{hash160}(\mathrm{redeem}) = h \ \wedge\ \exists\, st,\ \mathrm{evalBytes}(c, \mathrm{base}, \mathrm{reverse}(\mathrm{args}), \mathrm{redeem}) = \mathrm{some}(st) \ \wedge\ \mathrm{topTrue}(st) = \mathrm{true}.$$
The witness passed to `verifyScript` is the **empty** list.

**Unfolding the left-hand side.** $\sigma$ is the concatenation of the canonical pushes of $a_1, \ldots, a_k$ (the elements of `args` in order) followed by the canonical push of `redeem`. `verifyScript` evaluates $\sigma$ on the empty stack with version `base`: the size test uses `hsz`; each push is executed; a push fails if its data exceeds 520 bytes (excluded by `hargs`, `hred`) or if the stack would exceed 1000 elements (`hn` gives $k + 1 \le 998$). The resulting top-first stack is `stackSig` $= [\mathrm{redeem}, a_k, \ldots, a_1]$ (redeem on top). It then evaluates $\pi$ on that stack: `OP_HASH160` replaces the top by $\mathrm{hash160}(\mathrm{redeem})$, the push adds $h$, and `OP_EQUAL` replaces the two top elements by $[\mathtt{0x01}]$ if $\mathrm{hash160}(\mathrm{redeem}) = h$ and by the empty string otherwise; the top therefore casts to true iff the hashes agree, else `verifyScript` returns false. Next, the native branch: $\pi$ starts with $\mathtt{0xa9}$, which is neither $0$ nor in $[\mathtt{0x51}, \mathtt{0x60}]$, so `isWitnessProgram π` is nothing and `native` is `none` whatever the `witness` flag. With `hp`, and `isPayToScriptHash π` true (23 bytes, $\mathtt{0xa9}$, $\mathtt{0x14}$, $\mathtt{0x87}$ at the right indices, using `hh`), the P2SH branch runs: `isPushOnly σ` must hold (it does, since $\sigma$ is a concatenation of canonical pushes); `stackSig` is non-empty with top `redeem` and remainder $[a_k, \ldots, a_1] = \mathrm{reverse}(\mathrm{args})$; `evalBytes c base (reverse args) redeem` is run — failure gives false — and its result `stack2` must have a true top. Then, if `c.flags.witness` is true, `isWitnessProgram redeem` is nothing by `hnw`, so the result is false iff the witness is non-empty, which it is not (the witness is `[]`), hence true; if `c.flags.witness` is false the result is true directly.

**Logical content.** The theorem says that, under the listed hypotheses and with an empty witness, `verifyScript` accepts the push-only scriptSig and the P2SH output exactly when the redeem script's `hash160` equals $h$ and the redeem script, run as a legacy (`base`) script on the stack consisting of the arguments with the last-pushed argument on top, succeeds with a stack whose top casts to true. `evalBytes` on the redeem script includes its own $10000$-byte test, byte-level parse, and the interpreter with flags `scriptFlagsOf c.flags` and the oracle built from `sigFlagsOf c.flags`, `c.tx`, `c.nIn`, `c.amount`, version `base`, and script code `redeem`.

**What is not said.** Nothing is claimed for a non-empty witness, for `redeem` that *is* a witness program, for `c.flags.p2sh = false`, for $|h| \ne 20$, for arguments or redeem scripts above 520 bytes, for more than 998 arguments, or for a scriptSig over 10000 bytes. The theorem does not say the redeem evaluation leaves exactly one element (no clean-stack condition). It does not say anything about the handler `tap` (it is never invoked on this path). It does not say that `stackSig` has a particular length beyond what the pushes produce. It does not assert the final stack of the whole verification, only the Boolean verdict.
