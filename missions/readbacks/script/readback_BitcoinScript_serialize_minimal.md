# Read-back: `BitcoinScript.serialize_minimal`

**Binders and hypothesis.** One universally quantified variable $n$, an integer (of either sign, any magnitude, including $0$). No hypotheses.

**Conclusion.** The Boolean
$$\mathrm{nonMinimal}\big(\mathrm{serialize}(n)\big)$$
is equal to **false**. Since `nonMinimal` returns true to signal a non-minimal encoding, the claim is: the byte list produced by `serialize` from any integer is never flagged as non-minimal by `nonMinimal`.

**Unfolding `serialize`.** For $n = 0$, $\mathrm{serialize}(0) = []$. For $n \neq 0$: let $\mathit{mag} := \mathrm{natBytes}(|n|)$, the little-endian bytes of the absolute value with no trailing zero bytes (so $\mathit{mag}$ is non-empty and its last byte is non-zero). If the last byte of $\mathit{mag}$ has bit $\mathtt{0x80}$ set, the output is $\mathit{mag}$ followed by one extra byte, $\mathtt{0x80}$ when $n < 0$ and $\mathtt{0x00}$ when $n > 0$. Otherwise, the output is $\mathit{mag}$ with bit $\mathtt{0x80}$ set on its last byte when $n < 0$, and $\mathit{mag}$ itself when $n > 0$.

**Unfolding `nonMinimal`.** Given a byte list $v$: if $v = []$, the result is false. Otherwise let $\mathit{last}$ be the final byte and consider the byte $\mathit{prev}$ before it, if any. The result is
$$\big((\mathit{last} \,\&\, \mathtt{0x7f}) = 0\big)\ \wedge\ \big(\text{no } \mathit{prev} \text{ exists}\ \ \vee\ \ (\mathit{prev} \,\&\, \mathtt{0x80}) = 0\big).$$
That is, $v$ is "non-minimal" when the last byte is $\mathtt{0x00}$ or $\mathtt{0x80}$ and either $v$ has length one or the preceding byte has its top bit clear.

**The claim, case by case (as the code determines it).** The theorem asserts that for every integer $n$, the output of `serialize` falls outside the "non-minimal" pattern:
- $n = 0$: the output is $[]$, on which `nonMinimal` is false by its first clause.
- $n \neq 0$ with no extra byte appended: the last byte is the last byte of $\mathit{mag}$ (non-zero, top bit clear), possibly with its top bit set by `setTop`; in either case its low seven bits are non-zero, so the first conjunct fails.
- $n \neq 0$ with an extra byte $\mathtt{0x00}$ or $\mathtt{0x80}$ appended: the last byte has zero low bits, so the first conjunct holds, and the claim is that the second conjunct fails: the preceding byte (the last byte of $\mathit{mag}$) has its top bit set.
The theorem states the conclusion for all $n$ at once; the above is merely the shape the definitions give it.

**Edge cases included.** $n = 0$; $n = \pm 1$ (one byte, $[\mathtt{0x01}]$ and $[\mathtt{0x81}]$); $n = \pm 127$; $n = \pm 128$ (two bytes with an appended sign/padding byte); $n = \pm 255$, $\pm 256$; arbitrarily large magnitudes (there is no bound on $|n|$ and the output may be arbitrarily long — longer than the 4- and 5-byte limits that `toNum` enforces elsewhere).

**What is not said.** The theorem does not say that `serialize` produces the *shortest* encoding in any sense other than the specific predicate `nonMinimal`; it does not say that `serialize` is injective, nor that $\mathrm{setVch}(\mathrm{serialize}(n)) = n$ (that is a separate theorem in this bundle). It does not say anything about `nonMinimal` on lists that are not in the image of `serialize`, nor that every list on which `nonMinimal` is false is in the image of `serialize` (e.g. nothing is claimed about $[\mathtt{0x80},\mathtt{0x00}]$ versus $[\mathtt{0x80},\mathtt{0x80}]$ beyond what `serialize` produces). It does not bound the length of $\mathrm{serialize}(n)$, and so says nothing about whether `toNum` with its size limit would accept the result. It does not involve `toNum`'s `requireMinimal` flag directly, the interpreter, flags, or the oracle.
