# Read-back: theorem `BitcoinDifficulty.no_wrap`

## Statement

**Binders (universally quantified).**

- $t$, a natural number;
- $s$, a natural number (named `ts`).

**Hypotheses.**

- (ht) $t \le L = 2^{224} - 1$;
- (hts) $s \le 4{,}838{,}400$ (a literal numeral in the statement; it equals $4T = 4 \cdot 1{,}209{,}600$, the upper clamp value, but the statement writes the number, not the named constant).

**Conclusion.**

$$
t \cdot s \;<\; 2^{256},
$$

a strict inequality between natural numbers, where $2^{256}$ is the constant called `width`.

## Definitions used

**Constants (from the imported proof-of-work definitions).**

- $W = 2^{256}$ (the modulus called `width`).
- $L = 2^{224} - 1$ (the value called `powLimit`).
- $T = 14 \cdot 24 \cdot 60 \cdot 60 = 1{,}209{,}600$ (the value called `targetTimespan`); hence $\lfloor T/4 \rfloor = 302{,}400$ and $4T = 4{,}838{,}400$.


## Edge cases and what the quantifiers include

- $t = 0$ and $s = 0$ are included (then $t \cdot s = 0 < 2^{256}$).
- The statement is pure arithmetic on natural numbers: it does not mention the decoding $D$, the clamp $\kappa$, `rawNextTarget`, `calculateNextWork`, or any compact word, even though the file imports those definitions. The connection "$s$ is a clamped timespan" or "$t$ is a decoded target" is not part of the statement.
- The largest admitted product is $(2^{224} - 1) \cdot 4{,}838{,}400$; since $4{,}838{,}400 < 2^{23}$, this is below $2^{247}$.
