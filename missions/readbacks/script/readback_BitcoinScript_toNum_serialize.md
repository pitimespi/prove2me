# Read-back: `BitcoinScript.toNum_serialize`

**Binders and hypothesis.** One universally quantified integer $n$. One hypothesis, named $h$:
$$\big|\mathrm{serialize}(n)\big| \le 4,$$
i.e. the byte list produced by `serialize` from $n$ has length at most $4$ (lengths $0,1,2,3,4$ are all allowed).

**Conclusion.** An equation between optional integers:
$$\mathrm{toNum}(\text{true},\ 4,\ \mathrm{serialize}(n)) = \mathrm{some}(n).$$
That is, parsing the encoding of $n$ with the minimal-encoding requirement switched **on** and a size limit of $4$ bytes succeeds (does not return "no value") and yields exactly $n$.

**Unfolding `toNum`.** $\mathrm{toNum}(\mathit{requireMinimal}, \mathit{maxSize}, v)$ returns:
- "no value" if $\mathit{maxSize} < |v|$;
- otherwise "no value" if $\mathit{requireMinimal}$ is true, $v$ is non-empty, and $\mathrm{nonMinimal}(v)$ is true;
- otherwise $\mathrm{some}(\mathrm{setVch}(v))$.

With $\mathit{requireMinimal} = \text{true}$, $\mathit{maxSize} = 4$ and $v = \mathrm{serialize}(n)$, the conclusion therefore unfolds to the conjunction of three facts: (i) $\neg(4 < |\mathrm{serialize}(n)|)$, which is exactly the hypothesis $h$; (ii) it is **not** the case that $\mathrm{serialize}(n)$ is non-empty and $\mathrm{nonMinimal}(\mathrm{serialize}(n))$ is true; and (iii) $\mathrm{setVch}(\mathrm{serialize}(n)) = n$. Facts (ii) and (iii) are, respectively, the content of the separate theorems `serialize_minimal` and `serialize_roundtrip` in this bundle, but the present statement does not refer to them; it asserts the combined equation directly.

**Unfolding `serialize`, `nonMinimal`, `setVch`.** $\mathrm{serialize}(0) = []$; for $n \ne 0$ it is the little-endian magnitude bytes of $|n|$ without trailing zeros, with the sign carried in bit $\mathtt{0x80}$ of the last byte, adding an extra byte ($\mathtt{0x80}$ for negative, $\mathtt{0x00}$ for positive) when the last magnitude byte already has that bit set. $\mathrm{nonMinimal}(v)$ is true when $v$ is non-empty, its last byte is $\mathtt{0x00}$ or $\mathtt{0x80}$, and either $|v| = 1$ or the second-to-last byte has its top bit clear. $\mathrm{setVch}(v)$ is $-\mathrm{leNat}(\mathrm{clearTop}(v))$ if the last byte's top bit is set and $\mathrm{leNat}(v)$ otherwise, with $\mathrm{leNat}$ the little-endian unsigned value.

**What the hypothesis amounts to.** By the definition of `serialize`, the output length is at most $4$ exactly when $|n| \le 2^{31} - 1$: the magnitude $2^{31}-1$ encodes as $[\mathtt{0xff},\mathtt{0xff},\mathtt{0xff},\mathtt{0x7f}]$ (4 bytes), while $2^{31}$ needs $[\mathtt{0x00},\mathtt{0x00},\mathtt{0x00},\mathtt{0x80}]$ plus a fifth padding byte. So the theorem is about the integers $n$ with $-(2^{31}-1) \le n \le 2^{31}-1$, including $0$ (whose encoding is empty and is accepted by `toNum` because the minimality test is skipped for the empty list, and whose value is $\mathrm{setVch}([]) = 0$).

**Edge cases.** $n = 0$ (empty encoding, length $0 \le 4$). $n = \pm(2^{31}-1)$, the largest magnitudes allowed. $n = \pm 128$, $\pm 32768$, $\pm 8388608$ — values whose magnitude bytes end in a byte with the top bit set and so receive a padding byte; for these the length constraint bites one power of 256 earlier than one might expect from the magnitude alone.

**What is not said.** Nothing is claimed for integers whose encoding exceeds 4 bytes (e.g. $n = 2^{31}$ or $n = -2^{31}$): the theorem is silent, not negative, about them. Nothing is claimed about `toNum` with other size limits (such as the 5-byte limit used by CHECKLOCKTIMEVERIFY/CHECKSEQUENCEVERIFY in `execOp`) or with `requireMinimal = false` (the setting every arithmetic opcode in `execOp` actually uses). Nothing is claimed about `toNum` applied to byte lists not produced by `serialize`, in particular about whether non-minimal lists such as $[\mathtt{0x01},\mathtt{0x00}]$ or $[\mathtt{0x80}]$ are rejected. The theorem does not say that $\mathrm{serialize}(n)$ is the *only* 4-byte-or-shorter list that `toNum` maps to $n$. It does not mention the interpreter, flags, or the oracle.
