# Read-back: theorem `BitcoinDifficulty.raw_target_bounds`

## Statement

**Binders (universally quantified).**

- $t$, a natural number;
- $\ell$ and $f$, integers (named `lastTime`, `firstTime`), unrelated to each other.

**Hypothesis.**

- (ht) $t \le L = 2^{224} - 1$.

**Conclusion.** A conjunction of two parts, writing $R = R(t, \ell, f)$ for the raw next target:

$$
R \le 4t
\quad\text{and}\quad
\Big( R = L \;\;\text{or}\;\; \lfloor t / 4 \rfloor \le R \Big).
$$

Here $4t$ is the natural-number product, $\lfloor t/4 \rfloor$ is natural-number floor division, "or" is inclusive disjunction, and both inequalities are non-strict.

## Definitions used

**Constants (from the imported proof-of-work definitions).**

- $W = 2^{256}$ (the modulus called `width`).
- $L = 2^{224} - 1$ (the value called `powLimit`).
- $T = 14 \cdot 24 \cdot 60 \cdot 60 = 1{,}209{,}600$ (the value called `targetTimespan`); hence $\lfloor T/4 \rfloor = 302{,}400$ and $4T = 4{,}838{,}400$.

**Clamping a timespan, $\kappa(a)$ (the function called `clampTimespan`).** For an integer $a$ (positive, zero or negative),

$$
\kappa(a) =
\begin{cases}
302{,}400 & \text{if } a < 302{,}400,\\
4{,}838{,}400 & \text{if } a > 4{,}838{,}400,\\
a & \text{otherwise.}
\end{cases}
$$

$\kappa(a)$ always lies in $[302{,}400,\; 4{,}838{,}400]$, so it is positive and its conversion to a natural number (written $\kappa(a)$ below as well) is lossless.

**The raw next target, $R(t, \ell, f)$ (the function called `rawNextTarget`, defined in this bundle).** For a natural number $t$ and integers $\ell, f$, with $\tau = \kappa(\ell - f)$,

$$
R(t, \ell, f) = \min\!\left( \left\lfloor \frac{(t \cdot \tau) \bmod 2^{256}}{T} \right\rfloor,\; L \right)
$$

(the minimum is written in the source as "if $L <$ the quotient then $L$ else the quotient"). Unfolding the definitions, $N(c, \ell, f) = E\big(R(D(c), \ell, f)\big)$.


(For reference, $R(t, \ell, f)$ unfolds to: let $\tau = \kappa(\ell - f)$; let $q = \lfloor ((t\cdot\tau) \bmod 2^{256}) / T \rfloor$; then $R = L$ if $L < q$, else $R = q$. No encoding to a compact word is involved.)

## Edge cases and what the quantifiers include

- $t = 0$: then $R = 0$, the first part reads $0 \le 0$, and the second part's right disjunct reads $0 \le 0$.
- $t < 4$: $\lfloor t/4 \rfloor = 0$, so the right disjunct of the second part holds trivially whatever $R$ is.
- $\ell$ and $f$ are arbitrary integers; $\ell - f \le 302{,}400$ (including $\ell \le f$) gives $\tau = 302{,}400$, and $\ell - f \ge 4{,}838{,}400$ gives $\tau = 4{,}838{,}400$.
- For the admitted $t \le L$, $t \cdot \tau < 2^{247}$, so the reduction modulo $2^{256}$ inside $R$ does not change the product; it is still literally present.
- The second part is a disjunction: in the case $R = L$ the statement makes no claim that $\lfloor t/4 \rfloor \le R$ (though with $t \le L$ that would follow), and in the other case it makes no claim that $R \ne L$.
- The first part bounds $R$ by $4t$ without any cap: when $t > L/4$ the bound $4t$ exceeds $L$, and the first part is then weaker than the cap built into $R$.
