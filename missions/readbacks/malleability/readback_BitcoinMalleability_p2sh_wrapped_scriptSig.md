# Read-back: `BitcoinMalleability.p2sh_wrapped_scriptSig`

## Statement in words

For every Taproot handler $T$, every verification context $c$ whose P2SH flag and witness flag are both on, every pair of byte strings $\sigma$ (a scriptSig) and $\pi$ (a scriptPubKey) with $\pi$ of pay-to-script-hash shape, and every non-empty witness stack $w$: if $\mathrm{verifyScript}(T, c, \sigma, \pi, w)$ is true, then there exist a byte string $r$ and a list of byte strings $\mathrm{rest}$ such that evaluating $\sigma$ on the empty stack yields the stack with $r$ on top and $\mathrm{rest}$ beneath, $r$ is a witness program, and $\sigma$ is exactly the canonical single push of $r$.

## Binders and hypotheses

- $T$: any function from (context, list of byte strings, byte string) to Booleans. It is **not** required to be the Taproot file's handler; it is an arbitrary handler.
- $c$: a verification context $(\mathrm{flags}, \mathrm{tx}, \mathrm{nIn}, \mathrm{amount})$: $\mathrm{flags}$ is a record of seven Booleans $(\mathrm{p2sh}, \mathrm{witness}, \mathrm{taproot}, \mathrm{dersig}, \mathrm{cltv}, \mathrm{csv}, \mathrm{nulldummy})$; $\mathrm{tx}$ is a transaction; $\mathrm{nIn} \in \mathbb N$; $\mathrm{amount} \in \mathbb Z$. The transaction, index and amount are arbitrary and are not linked to $\sigma$, $\pi$ or $w$ by any hypothesis (e.g. $\mathrm{nIn}$ need not index an input of $\mathrm{tx}$, and $\pi$ need not be the script of any coin).
- $\sigma, \pi$: byte strings (finite lists of 8-bit values).
- $w$: a finite list of byte strings.
- $h_p$: $c.\mathrm{flags}.\mathrm{p2sh} = \mathrm{true}$.
- $h_f$: $c.\mathrm{flags}.\mathrm{witness} = \mathrm{true}$. The remaining five flags are unconstrained.
- $h_{\mathrm{spk}}$: $\mathrm{isPayToScriptHash}(\pi) = \mathrm{true}$, i.e. $|\pi| = 23$, $\pi_0 = \mathrm{0xa9}$, $\pi_1 = \mathrm{0x14}$, $\pi_{22} = \mathrm{0x87}$ (the 20 middle bytes are arbitrary).
- $h_w$: $w \ne [\,]$ (at least one witness element; the elements themselves are arbitrary).
- $h_v$: $\mathrm{verifyScript}(T, c, \sigma, \pi, w) = \mathrm{true}$.

## Conclusion

$$
\exists\, r,\ \exists\, \mathrm{rest}:\quad E_c^{\mathrm{base}}([\,], \sigma) = r :: \mathrm{rest}
\;\wedge\; \mathrm{isWitnessProgram}(r) \text{ is defined}
\;\wedge\; \sigma = \mathrm{pushBytes}(r),
$$

where $r$ ranges over byte strings and $\mathrm{rest}$ over lists of byte strings. "$r :: \mathrm{rest}$" is the stack whose top element is $r$ and whose remaining elements, top to bottom, are $\mathrm{rest}$. The existential is plain existence, not uniqueness; $\mathrm{rest}$ is not asserted to be empty.

## The notions, unfolded

**Evaluation.** $E_c^{v}(S, s)$ ("evalBytes" with signature version $v$) is undefined if $|s| > 10000$; undefined if $s$ does not parse into a sequence of script instructions; otherwise it is the final stack (top first) of the Script interpreter run from the stack $S$ on the parsed $s$, with interpreter flags $(c.\mathrm{flags}.\mathrm{cltv}, c.\mathrm{flags}.\mathrm{csv}, c.\mathrm{flags}.\mathrm{nulldummy})$ and the legacy oracle built from $(c.\mathrm{flags}.\mathrm{dersig}, c.\mathrm{tx}, c.\mathrm{nIn}, c.\mathrm{amount}, v$, script code $s)$; undefined if the interpreter fails. In the conclusion $v$ is *base* and $S = [\,]$. The first conjunct says this evaluation is defined and produces a non-empty stack.

**Witness program.** For $r$ of length $k$, $\mathrm{isWitnessProgram}(r)$ is defined iff $4 \le k \le 42$, $r_0 = 0$ or $\mathrm{0x51} \le r_0 \le \mathrm{0x60}$, and $r_1 + 2 = k$; it then yields version $0$ (if $r_0 = 0$) or $r_0 - \mathrm{0x50}$ ($1$–$16$) and program $r_2 \ldots r_{k-1}$ (length $2$–$40$). Note that $\pi$ itself, having first byte $\mathrm{0xa9}$, is never a witness program under this definition.

**Canonical push.** $\mathrm{pushBytes}(d)$ is: the single byte $|d|$ followed by $d$ if $|d| < \mathrm{0x4c}$; $\mathrm{0x4c}$, one byte $|d|$, then $d$ if $|d| \le \mathrm{0xff}$; $\mathrm{0x4d}$, two little-endian bytes of $|d|$, then $d$ if $|d| \le \mathrm{0xffff}$; else $\mathrm{0x4e}$, four little-endian bytes of $|d|$, then $d$. For a witness program $r$ ($4 \le |r| \le 42$) this is the byte $|r|$ followed by $r$, so the third conjunct says $\sigma$ has length $|r| + 1$, first byte $|r|$, and tail $r$.

**verifyScript** $(T, c, \sigma, \pi, w)$ is computed as:

1. $S_\sigma = E_c^{\mathrm{base}}([\,], \sigma)$; undefined gives false.
2. $S = E_c^{\mathrm{base}}(S_\sigma, \pi)$; undefined gives false; false if $S$ is empty or its top is not true under $\mathrm{castToBool}$ (true iff some byte is non-zero, except that a string whose only non-zero byte is a final $\mathrm{0x80}$ is false).
3. If $c.\mathrm{flags}.\mathrm{witness}$ is on and $\mathrm{isWitnessProgram}(\pi) = (v,p)$: false if $\sigma \ne [\,]$, else $\mathrm{verifyWitnessProgram}(T,c,w,v,p,\mathrm{isP2sh}=\mathrm{false})$, and this verdict is final. (Under $h_{\mathrm{spk}}$ this branch is not taken, since $\pi_0 = \mathrm{0xa9}$.)
4. Otherwise, if $c.\mathrm{flags}.\mathrm{p2sh}$ is on and $\mathrm{isPayToScriptHash}(\pi)$: false unless $\sigma$ is push-only (every instruction parses and is a data push or an opcode $\le \mathrm{0x60}$); false if $S_\sigma = [\,]$; otherwise write $S_\sigma = r :: \mathrm{rest}$ and compute $S_2 = E_c^{\mathrm{base}}(\mathrm{rest}, r)$; false if undefined or if $S_2$ is empty or its top is not true; then, since $c.\mathrm{flags}.\mathrm{witness}$ is on: if $\mathrm{isWitnessProgram}(r) = (v,p)$ then false unless $\sigma = \mathrm{pushBytes}(r)$, else $\mathrm{verifyWitnessProgram}(T,c,w,v,p,\mathrm{isP2sh}=\mathrm{true})$; if $r$ is not a witness program then false if $w \ne [\,]$, else true. (If the witness flag were off the P2SH path would end with true; here it is on.)
5. Otherwise: false if $c.\mathrm{flags}.\mathrm{witness}$ is on and $w \ne [\,]$, else true.

**verifyWitnessProgram** $(T,c,w,v,p,\mathrm{isP2sh})$: if $v = 0$ and $|p| = 32$: false if $w$ is empty; else the last element $s$ of $w$ must satisfy $\mathrm{SHA256}(s) = p$ and then "execute" $s$ on the reversed remaining elements; if $v = 0$ and $|p| = 20$: false unless $|w| = 2$, else execute the implied script $\mathrm{0x76}\,\mathrm{0xa9}\,\mathrm{pushBytes}(p)\,\mathrm{0x88}\,\mathrm{0xac}$ on $w$ reversed; $v = 0$ with any other $|p|$: false; $v = 1$, $|p| = 32$, $\mathrm{isP2sh} = \mathrm{false}$: true if $c.\mathrm{flags}.\mathrm{taproot}$ is off, else $T(c, w, p)$; every other case (including $v = 1$ with $\mathrm{isP2sh} = \mathrm{true}$, which is the case reachable through the P2SH path, versions $2$–$16$, and pay-to-anchor): true. "Execute" with stack $S$ and script $s$: false if any element of $S$ exceeds $520$ bytes; else $E_c^{\mathrm{witnessV0}}(S, s)$ must be defined, consist of exactly one element, and that element must be true.

## Edge cases made explicit

- $T$ is arbitrary; under $h_{\mathrm{spk}}$ step 3 is not reachable, and inside the P2SH path $\mathrm{verifyWitnessProgram}$ is called with $\mathrm{isP2sh} = \mathrm{true}$, in which the handler $T$ is never consulted; so $T$ does not influence $h_v$.
- $c.\mathrm{tx}$, $c.\mathrm{nIn}$, $c.\mathrm{amount}$ are unconstrained; they only enter through signature and lock-time checks inside script evaluation.
- $h_w$ requires only that $w$ be non-empty; its elements may be anything (for instance a single empty byte string).
- The conclusion fixes the top of $S_\sigma$ and the shape of $\sigma$; it does not assert $\mathrm{rest} = [\,]$, does not say which witness version or program length $r$ has (any version $0$–$16$, any program length $2$–$40$ is possible under the definition), and does not say anything about $w$, about $\pi$'s middle 20 bytes, or about any hash relation between $r$ and $\pi$.
- $h_v$ may be unsatisfiable for particular $(c, \sigma, \pi, w)$ (for example when $\sigma$ is not push-only, or when the middle bytes of $\pi$ do not match the hash of the pushed redeem script, in which case step 2 fails); for such inputs the implication holds vacuously.
- The five flags $\mathrm{taproot}$, $\mathrm{dersig}$, $\mathrm{cltv}$, $\mathrm{csv}$, $\mathrm{nulldummy}$ are unconstrained.
