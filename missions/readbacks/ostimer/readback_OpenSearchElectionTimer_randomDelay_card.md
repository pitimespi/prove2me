# Read-back: `OpenSearchElectionTimer.randomDelay_card`

## Notions used

**Draws.** A draw is an element $x$ of $\mathrm{Fin}(2^{64}) = \{0, \dots, 2^{64}-1\}$, read as the Java `long` $\mathrm{toLong}(x) = x - 2^{63}$.

**`nonNegative`.** $\mathrm{nonNegative}(n) = 0$ if $n = -2^{63}$, and $|n|$ otherwise.

**`randomDelay`.** $\mathrm{randomDelay}(M, x) = (\mathrm{nonNegative}(x - 2^{63}) \bmod M) + 1$, with the natural-number remainder (and $a \bmod 0 = a$).

**Notation.** $\#S$ is the number of elements of a finite set $S$. $\lfloor a / b \rfloor$ is natural-number floor division, and $a \mathbin{\dot-} b$ is truncated subtraction.

## 1. Declaration

```lean
theorem OpenSearchElectionTimer.randomDelay_card (M d : Nat) (hM : 1 ≤ M) (hM' : M ≤ 2 ^ 63)
    (hd : 1 ≤ d) (hdM : d ≤ M) :
    (Finset.univ.filter (fun x : Fin (2 ^ 64) => randomDelay M x = d)).card = 2 * ((2 ^ 63 - d) / M + 1)
```

**Binders:** $M, d \in \mathbb{N}$.

**Hypotheses, in order:**
- $hM : 1 \le M$;
- $hM' : M \le 2^{63}$;
- $hd : 1 \le d$;
- $hdM : d \le M$.

**Conclusion** (an equation in $\mathbb{N}$):
$$\#\{x \in \mathrm{Fin}(2^{64}) : \mathrm{randomDelay}(M, x) = d\} \;=\; 2\left(\left\lfloor \frac{2^{63} \mathbin{\dot-} d}{M} \right\rfloor + 1\right).$$
Because $d \le M \le 2^{63}$, the subtraction is never truncated.

**Unfolded.** The left side counts the draws $x$ with $\mathrm{nonNegative}(x - 2^{63}) \equiv d - 1 \pmod M$. Dividing by $2^{64}$ gives the probability of delay $d$ under a uniform 64-bit draw:
$$\Pr[\mathrm{randomDelay}(M, x) = d] = \frac{\lfloor (2^{63}-d)/M\rfloor + 1}{2^{63}} .$$

**Equivalent form** (my rewriting). Let $q = \lfloor 2^{63}/M \rfloor$ and $\rho = 2^{63} \bmod M$. The right side equals $2(q+1)$ when $d \le \rho$, and $2q$ when $d > \rho$. Summing the right side over $d \in [1, M]$ gives $2^{64}$, as it must.

**Examples:**
- $M = 1$, $d = 1$: $2^{64}$, i.e. every draw.
- $M = 2^{63}$: exactly $2$ draws for every $d$.
- $M = 10000$: here $\rho = 5808$ and $q = 922337203685477$. Each $d \le 5808$ has $2 \cdot 922337203685478$ draws, and each $d \ge 5809$ has $2 \cdot 922337203685477$.

## 2. What is not constrained

- **$hd$ is needed.** For $d = 0$ the true count is $0$, but the right side would be $2(\lfloor 2^{63}/M\rfloor + 1) > 0$.
- **$hdM$ is needed.** For example, with $M = 1$ and $d = 2$ the count is $0$, but the right side is positive.
- **$hM'$ is needed.** If $M > 2^{63}$ and $2^{63} < d \le M$, the count is $0$ (delays never exceed $2^{63}$), but the right side is $2((2^{63} \mathbin{\dot-} d) \operatorname{div} M + 1) = 2$.
- **$hM$ is redundant.** It follows from $hd$ and $hdM$, since $1 \le d \le M$.
- **$M = 2^{63}$ is allowed.** This is not a Java `long` value (the maximum is $2^{63}-1$). The extension is harmless.
- **Idealization.** The count is over all $2^{64}$ elements of $\mathrm{Fin}(2^{64})$, i.e. a uniform 64-bit draw. The definitions file's docstring acknowledges that Java's `nextLong()` takes only $2^{48}$ distinct values. The theorem says nothing about the real generator.
- **Satisfiable, not vacuous.** The hypotheses hold for example with $M = d = 1$.

## 3. Plain-language summary

Take a bound $M$ with $1 \le M \le 2^{63}$ and a value $d$ with $1 \le d \le M$. Exactly $2(\lfloor (2^{63}-d)/M\rfloor + 1)$ of the $2^{64}$ possible draws give random delay $d$. So the delay is exactly uniform on $[1, M]$ when $M$ divides $2^{63}$. Otherwise, the first $2^{63} \bmod M$ values each have two more draws than the rest.
