# Read-back: `BitcoinSig.normalizeS_low`

**Binders and hypothesis.** Universally quantified over a natural number $s$, with one hypothesis $hs$: $s < n$, where $n$ is the constant
$$n = \texttt{0xFFFFFFFF FFFFFFFF FFFFFFFF FFFFFFFE BAAEDCE6 AF48A03B BFD25E8C D0364141}.$$
No other property of $n$ (primality, being a group order) is used or asserted.

**Conclusion.**
$$\text{isHighS}\ (\text{normalizeS}\ s) = \text{false}.$$

**Unfolding.** `isHighS` $t$ is the Boolean decision of $\lfloor n/2 \rfloor < t$, where $\lfloor n/2 \rfloor$ is natural-number (floor) division; since $n$ is odd, $\lfloor n/2 \rfloor = (n-1)/2$. `normalizeS` $s$ is: $n - s$ (natural-number subtraction, truncated at $0$) if `isHighS` $s$, and $s$ otherwise. So the conclusion reads: let
$$s' = \begin{cases} n - s & \text{if } s > \lfloor n/2 \rfloor,\\ s & \text{otherwise;}\end{cases}$$
then $s' \leq \lfloor n/2 \rfloor$. Under $hs$: in the first case $\lfloor n/2 \rfloor + 1 \leq s \leq n - 1$, so $1 \leq n - s \leq n - \lfloor n/2 \rfloor - 1 = \lfloor n/2 \rfloor$; in the second case $s' = s \leq \lfloor n/2\rfloor$ by definition of the branch. The statement is purely arithmetic on natural numbers.

**Edge cases.** $s = 0$ is allowed (not high, normalizes to $0$). $s = \lfloor n/2 \rfloor$ is not high and is left unchanged. $s = \lfloor n/2 \rfloor + 1$ is high and maps to $\lfloor n/2 \rfloor$. The hypothesis excludes $s \geq n$; for such $s$ the definition would give $n - s = 0$, also not high, but the theorem does not cover it.

**What is not said.** The statement does not say anything for $s \geq n$. It does not say that `normalizeS` $s$ is congruent to $\pm s$ modulo $n$, nor that it is non-zero, nor that it is below $n$. It does not say that normalization preserves or changes the outcome of any signature verification (`ecdsaVerifyRaw`, `pubkeyVerify`). It does not say that `normalizeS` is idempotent, nor that it is the identity on low values (though both follow from the definition, they are not asserted). It does not mention `checkLowS` or byte-string signatures at all: it is about a bare natural number.
