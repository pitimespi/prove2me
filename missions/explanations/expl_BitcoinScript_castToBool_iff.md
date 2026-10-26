We prove $\mathrm{castToBool}(v) = \mathtt{true} \iff \mathrm{setVch}(v) \ne 0$.

Define the magnitude $\mathrm{mag}(v) = \mathrm{leNat}(\mathrm{clearTop}\,v)$ when the top bit is set and $\mathrm{leNat}(v)$ otherwise; `setVch_eq` shows $\mathrm{setVch}(v) = \pm \mathrm{mag}(v)$ and hence (`setVch_ne_zero_iff`) $\mathrm{setVch}(v) \ne 0 \iff \mathrm{mag}(v) \ne 0$.

`castToBool` is defined by recursion: `[]` is false; `[b]` is true iff $b \ne 0 \wedge b \ne \mathtt{80}$; `b :: rest` (with `rest` non-empty) is true iff $b \ne 0$ or `castToBool rest`. We prove the iff by induction on $v$ with a strengthened statement for the cons case.

* `[]`: both sides false.
* `[b]`: `mag_single` gives $\mathrm{mag}[b] = b \bmod 128$ if $128 \le b$ and $b$ otherwise; this is zero iff $b = 0$ or $b = 128$, which is exactly the single-byte test (`topbit_iff`, `and7f_toNat`, and `BitVec.toNat` injectivity).
* `b :: c :: rest`: `mag_cons_cons` gives $\mathrm{mag}(b :: c :: rest) = b + 256\,\mathrm{mag}(c :: rest)$ — the first byte is never the last, so neither the top-bit test nor `clearTop` touches it (`topBit`/`clearTop` act on the last byte only). This is zero iff $b = 0$ and $\mathrm{mag}(c :: rest) = 0$, and the induction hypothesis turns the second conjunct into `castToBool (c :: rest) = false`.

Both encodings of zero (all-zero bytes, and zero bytes followed by `0x80`) land in the "false" case, every other list in the "true" case.
