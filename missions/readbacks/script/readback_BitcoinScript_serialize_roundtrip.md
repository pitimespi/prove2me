# Read-back: `BitcoinScript.serialize_roundtrip`

**Binders and hypothesis.** One universally quantified integer $n$ (any sign, any magnitude, $0$ included). No hypotheses.

**Conclusion.** The integer equation
$$\mathrm{setVch}\big(\mathrm{serialize}(n)\big) = n .$$
Decoding the byte list produced by `serialize` from $n$, using `setVch`, returns exactly $n$.

**Unfolding `serialize`.** $\mathrm{serialize}(0) = []$. For $n \ne 0$, with $\mathit{mag} := \mathrm{natBytes}(|n|)$ (little-endian bytes of $|n|$, no trailing zero bytes, hence non-empty with non-zero last byte): if the last byte of $\mathit{mag}$ has bit $\mathtt{0x80}$ set, the result is $\mathit{mag}$ followed by $\mathtt{0x80}$ (if $n < 0$) or $\mathtt{0x00}$ (if $n > 0$); otherwise the result is $\mathit{mag}$ with bit $\mathtt{0x80}$ set on its last byte (if $n < 0$) or $\mathit{mag}$ unchanged (if $n > 0$).

**Unfolding `setVch`.** For a byte list $v$: if the top bit ($\mathtt{0x80}$) of the last byte of $v$ is set, $\mathrm{setVch}(v) = -\mathrm{leNat}(\mathrm{clearTop}(v))$, where `clearTop` clears that one bit; otherwise $\mathrm{setVch}(v) = \mathrm{leNat}(v)$. Here $\mathrm{leNat}([]) = 0$ and $\mathrm{leNat}(b :: r) = b + 256\cdot \mathrm{leNat}(r)$, so the first byte is least significant. For $v = []$ the value is $0$.

**The claim in detail.** For each integer $n$:
- if $n = 0$: $\mathrm{setVch}([]) = \mathrm{leNat}([]) = 0$;
- if $n > 0$: the last byte of $\mathrm{serialize}(n)$ has its top bit clear (either the last magnitude byte with clear top bit, or an appended $\mathtt{0x00}$), and the little-endian value of the whole list is claimed to be $|n| = n$;
- if $n < 0$: the last byte has its top bit set (either by `setTop` or because an appended $\mathtt{0x80}$), and the negated little-endian value after clearing that bit is claimed to be $-|n| = n$.
The theorem states the equation uniformly for all $n$; the case split above is only the shape the definitions impose.

**Edge cases included by the quantifier.** $n = 0$; $n = -1$ ($[\mathtt{0x81}]$ decodes to $-1$); $n = \pm 128$ (two-byte outputs $[\mathtt{0x80},\mathtt{0x00}]$ and $[\mathtt{0x80},\mathtt{0x80}]$); $n = \pm 2^{31}$, $\pm 2^{63}$ and beyond — there is no size restriction, so the equation is claimed for integers whose encodings exceed 4 or 5 bytes, outside anything `toNum` would accept.

**What is not said.** The theorem asserts only the composite $\mathrm{setVch} \circ \mathrm{serialize}$ is the identity on integers. It does not assert the other composite: nothing is claimed about $\mathrm{serialize}(\mathrm{setVch}(v))$ for a byte list $v$, and indeed the statement is silent on whether `serialize` is surjective onto byte lists (it is not claimed that every byte list decodes and re-encodes to itself). It does not say `serialize` is injective (though injectivity is a logical consequence of having a left inverse, the theorem does not state it). It does not mention minimality, `nonMinimal`, `toNum`, size limits, or the length of $\mathrm{serialize}(n)$. It does not relate to `castToBool`. It makes no statement about the interpreter, `pushNum`, flags, or the oracle.
