# Read-back: `BitcoinMalleability.native_scriptSig_empty`

## Statement in words

For every consensus flag set $f$, every ledger $u$ and every transaction $\mathrm{tx}$, if the witness flag of $f$ is on and every input script of $\mathrm{tx}$ verifies against $u$ under $f$ (in the sense of $\mathrm{inputScriptsOk}$, unfolded below), then every input $i$ occurring in $\mathrm{tx}.\mathrm{vin}$ whose spent output script (looked up in $u$) is a witness program has an empty $\mathrm{scriptSig}$.

## Binders and hypotheses

Universally quantified, with no other constraints than those listed:

- $f$: a record of seven Booleans $(\mathrm{p2sh}, \mathrm{witness}, \mathrm{taproot}, \mathrm{dersig}, \mathrm{cltv}, \mathrm{csv}, \mathrm{nulldummy})$. Only $\mathrm{witness}$ is constrained (below); the other six are arbitrary.
- $u$: a ledger, i.e. a finite association list of pairs (outpoint, coin), where an outpoint is $(h, n)$ with $h$ a byte string of any length and $n \in \mathbb N$, and a coin is $(\mathrm{out}, \mathrm{height}, \mathrm{isCoinbase})$ with $\mathrm{out} = (\mathrm{nValue} \in \mathbb Z, \mathrm{scriptPubKey})$. Keys need not be distinct.
- $\mathrm{tx}$: a transaction $(\mathrm{version} \in \mathbb N, \mathrm{vin}, \mathrm{vout}, \mathrm{nLockTime} \in \mathbb N)$, where each input is $(\mathrm{prevout}, \mathrm{scriptSig}, \mathrm{nSequence}, \mathrm{witness})$ (outpoint, byte string, natural number, list of byte strings) and each output is $(\mathrm{nValue} \in \mathbb Z, \mathrm{scriptPubKey})$. No well-formedness is assumed.
- Hypothesis $h_f$: $f.\mathrm{witness} = \mathrm{true}$.
- Hypothesis $h$: $\mathrm{inputScriptsOk}(f, u, \mathrm{tx}) = \mathrm{true}$.

## Conclusion

$$
\forall\, i \in \mathrm{tx}.\mathrm{vin}:\quad \mathrm{isWitnessProgram}\big(\mathrm{accessCoin}(u, i.\mathrm{prevout}).\mathrm{out}.\mathrm{scriptPubKey}\big) \text{ is defined} \;\Longrightarrow\; i.\mathrm{scriptSig} = [\,].
$$

Membership "$i \in \mathrm{tx}.\mathrm{vin}$" is list membership: the input equals some element of the list (its position does not matter).

## The notions, unfolded

**Lookup.** $\mathrm{accessCoin}(u, o)$ is the coin of the first pair in $u$ whose outpoint equals $o$, or, if there is none, the dummy coin $((-1, [\,]), 0, \mathrm{false})$, whose output script is empty.

**Witness program.** For a byte string $s$ of length $k$, $\mathrm{isWitnessProgram}(s)$ is defined iff $4 \le k \le 42$, the first byte $s_0$ is $0$ or in $[\mathrm{0x51}, \mathrm{0x60}]$, and $s_1 + 2 = k$; it then yields $(\mathrm{version}, \mathrm{program})$ with $\mathrm{version} = 0$ if $s_0 = 0$ else $s_0 - \mathrm{0x50}$, and $\mathrm{program} = s_2 \ldots s_{k-1}$ (length $2$ to $40$). The empty string is not a witness program, so the conclusion's antecedent fails for any input whose outpoint is absent from $u$.

**Input scripts OK.** Let $\mathrm{vin} = [i_0, \ldots, i_{m-1}]$ and $\mathrm{spent} = [\mathrm{accessCoin}(u, i_0.\mathrm{prevout}).\mathrm{out}, \ldots, \mathrm{accessCoin}(u, i_{m-1}.\mathrm{prevout}).\mathrm{out}]$. Then $\mathrm{inputScriptsOk}(f,u,\mathrm{tx}) = \mathrm{true}$ means: for every index $n$ with $0 \le n < m$, writing $c_n = \mathrm{accessCoin}(u, i_n.\mathrm{prevout})$,

$$
\mathrm{verifyScript}\big(T_{\mathrm{spent}},\ (f, \mathrm{tx}, n, c_n.\mathrm{out}.\mathrm{nValue}),\ i_n.\mathrm{scriptSig},\ c_n.\mathrm{out}.\mathrm{scriptPubKey},\ i_n.\mathrm{witness}\big) = \mathrm{true},
$$

where $(f, \mathrm{tx}, n, a)$ is a verification context (flags, spending transaction, input index, amount $a \in \mathbb Z$; for a missing coin, $a = -1$), and $T_{\mathrm{spent}}$ is the Taproot handler of the Taproot file for the spent-output list (described below). When $m = 0$ the condition is vacuously true.

**verifyScript** $(T, c, \sigma, \pi, w)$ for a handler $T$, context $c$, scriptSig $\sigma$, scriptPubKey $\pi$ and witness stack $w$ (a list of byte strings in serialized order, last element on top) is the Boolean computed as follows:

1. Evaluate $\sigma$ with signature version *base* on the empty stack: $E_c^{\mathrm{base}}([\,], \sigma)$. If this fails, the result is false; otherwise let $S_\sigma$ be the resulting stack (top first).
2. Evaluate $\pi$ on $S_\sigma$: $E_c^{\mathrm{base}}(S_\sigma, \pi)$. If this fails, false; otherwise let $S$ be the resulting stack. If $S$ is empty or its top element is "false" under $\mathrm{castToBool}$ (a byte string is true iff some byte is non-zero, except that a string whose only non-zero byte is a final $\mathrm{0x80}$ is false), the result is false.
3. *Native witness branch*, taken only if $c.\mathrm{flags}.\mathrm{witness}$ is on and $\mathrm{isWitnessProgram}(\pi) = (v, p)$ is defined: the result is false if $\sigma \ne [\,]$, and otherwise is $\mathrm{verifyWitnessProgram}(T, c, w, v, p, \mathrm{isP2sh} = \mathrm{false})$. This verdict is final.
4. Otherwise, if $c.\mathrm{flags}.\mathrm{p2sh}$ is on and $\pi$ is pay-to-script-hash ($|\pi| = 23$, $\pi_0 = \mathrm{0xa9}$, $\pi_1 = \mathrm{0x14}$, $\pi_{22} = \mathrm{0x87}$): false unless $\sigma$ is push-only (every instruction of $\sigma$ parses and is a data push or an opcode $\le \mathrm{0x60}$); false if $S_\sigma$ is empty; otherwise with $S_\sigma = r :: \mathrm{rest}$ ($r$ the top), evaluate $E_c^{\mathrm{base}}(\mathrm{rest}, r)$; false on failure or on a non-true top; then, if $c.\mathrm{flags}.\mathrm{witness}$ is on and $\mathrm{isWitnessProgram}(r) = (v, p)$: false unless $\sigma = \mathrm{pushBytes}(r)$, else $\mathrm{verifyWitnessProgram}(T, c, w, v, p, \mathrm{true})$; if $c.\mathrm{flags}.\mathrm{witness}$ is on and $r$ is not a witness program: false if $w \ne [\,]$, else true; if the witness flag is off: true.
5. Otherwise (neither branch): false if $c.\mathrm{flags}.\mathrm{witness}$ is on and $w \ne [\,]$; else true.

Here $E_c^{v}(S, s)$ ("evalBytes") is: undefined if $|s| > 10000$; undefined if $s$ does not parse into a sequence of script instructions; otherwise the final stack (top first) of the Script interpreter run from stack $S$ on the parsed $s$, with interpreter flags $(c.\mathrm{flags}.\mathrm{cltv}, c.\mathrm{flags}.\mathrm{csv}, c.\mathrm{flags}.\mathrm{nulldummy})$ and the legacy signature/lock-time oracle built from $(c.\mathrm{flags}.\mathrm{dersig}$, $c.\mathrm{tx}$, $c.\mathrm{nIn}$, $c.\mathrm{amount}$, $v$, script code $s)$; undefined if the interpreter fails. $\mathrm{pushBytes}(d)$ is the canonical push of $d$: a length byte then $d$ if $|d| < \mathrm{0x4c}$; $\mathrm{0x4c}$, one length byte, $d$ if $|d| \le \mathrm{0xff}$; $\mathrm{0x4d}$, two little-endian length bytes, $d$ if $|d| \le \mathrm{0xffff}$; else $\mathrm{0x4e}$, four little-endian length bytes, $d$.

**verifyWitnessProgram** $(T, c, w, v, p, \mathrm{isP2sh})$: if $v = 0$ and $|p| = 32$: false if $w$ is empty; else with $s$ the last element of $w$, false if $\mathrm{SHA256}(s) \ne p$, else "execute witness script" with the reversed remaining elements as stack and script $s$. If $v = 0$ and $|p| = 20$: false unless $|w| = 2$, else execute with stack $w$ reversed and the implied script $\mathrm{0x76}\,\mathrm{0xa9}\,\mathrm{pushBytes}(p)\,\mathrm{0x88}\,\mathrm{0xac}$. If $v = 0$ and $|p| \notin \{20, 32\}$: false. If $v = 1$, $|p| = 32$ and $\mathrm{isP2sh} = \mathrm{false}$: true when $c.\mathrm{flags}.\mathrm{taproot}$ is off, else $T(c, w, p)$. Every other case (other versions, version-1 programs of other lengths, version 1 inside P2SH, pay-to-anchor) is true. "Execute witness script" with stack $S$ and script $s$ is: false if any element of $S$ exceeds $520$ bytes; else $E_c^{\mathrm{witnessV0}}(S, s)$ must be defined, leave exactly one element, and that element must be true.

**The Taproot handler** $T_{\mathrm{spent}}(c, w, p)$: false if $w$ is empty; otherwise an annex (a last element starting with byte $\mathrm{0x50}$ when $|w| \ge 2$) is split off; if one element remains it is checked as a Schnorr key-path signature for $p$ over $c.\mathrm{tx}$, $\mathrm{spent}$ and $c.\mathrm{nIn}$; otherwise the last element is a control block whose length must be $33 + 32k$ for some $0 \le k \le 128$, the element before it is the leaf script, the control block must commit $p$ to the leaf, and for leaf version $\mathrm{0xc0}$ the tapscript is executed on the remaining elements with a validation-weight budget; other leaf versions give true. (The handler is consulted only in the case $v = 1$, $|p| = 32$, not P2SH, taproot flag on.)

## Edge cases made explicit

- If $\mathrm{tx}.\mathrm{vin}$ is empty, both $h$ and the conclusion hold vacuously.
- The hypothesis $h$ ranges over inputs by **position** $n$ (with the amount and context index $n$), while the conclusion ranges over inputs by **membership**; an input occurring twice in $\mathrm{vin}$ is verified at both positions.
- $h$ requires every input to verify, including inputs spending non-witness-program outputs and inputs whose outpoint is absent from $u$ (then the output script is $[\,]$ and the amount is $-1$); the conclusion speaks only of inputs whose looked-up script is a witness program.
- Any witness version $0$–$16$ and program length $2$–$40$ counts as a witness program in the conclusion.
- No well-formedness of $\mathrm{tx}$ or $u$, no distinctness of ledger keys, no coinbase exclusion, and no constraint on $f.\mathrm{p2sh}$, $f.\mathrm{taproot}$, $f.\mathrm{dersig}$, $f.\mathrm{cltv}$, $f.\mathrm{csv}$, $f.\mathrm{nulldummy}$ is assumed.
- The statement says nothing about witnesses, sequence numbers, outputs, or the transaction identifier.
