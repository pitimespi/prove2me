# Read-back: `BitcoinToLocal.checkSequence_iff`

**Statement.** For every transaction $\mathrm{tx}$, every natural number $n_{\mathrm{in}}$, and every integer $\delta$ (named `delay`) satisfying the two hypotheses

$$
0 \le \delta \qquad\text{and}\qquad \delta < 2^{16},
$$

the following equivalence holds. Write $\sigma := \mathrm{inputSequence}(\mathrm{tx}, n_{\mathrm{in}})$ and $M := 2^{22} \mid \mathtt{0xffff}$ (bitwise OR on naturals; since the two constants have disjoint bits, $M = 2^{22} + 65535 = 4259839 = \mathtt{0x40ffff}$). Then

$$
\mathrm{checkSequence}(\mathrm{tx}, n_{\mathrm{in}}, \delta) = \mathrm{true}
\iff
\Big( 2 \le \mathrm{tx}.\mathrm{version} \Big)
\land \Big( \sigma \mathbin{\&} 2^{31} = 0 \Big)
\land \Big( \sigma \mathbin{\&} M < 2^{22} \Big)
\land \Big( \operatorname{toNat}(\delta) \le \sigma \mathbin{\&} M \Big).
$$

Here $\mathbin{\&}$ is bitwise AND on natural numbers; $\operatorname{toNat}(\delta)$ is $\delta$ itself since $\delta \ge 0$ by hypothesis (it would be $0$ for a negative integer). The constants are the preamble's $\mathrm{SEQUENCE\_LOCKTIME\_DISABLE\_FLAG} = 2^{31}$, $\mathrm{SEQUENCE\_LOCKTIME\_TYPE\_FLAG} = 2^{22}$ and $\mathrm{SEQUENCE\_LOCKTIME\_MASK} = \mathtt{0xffff} = 65535$ (the signature-layer copies).

**The objects involved.**

- A *transaction* is a record $(\mathrm{version} \in \mathbb{N},\ \mathrm{vin},\ \mathrm{vout},\ \mathrm{nLockTime} \in \mathbb{N})$ where $\mathrm{vin}$ is a list of *inputs*, each a record $(\mathrm{prevout}, \mathrm{scriptSig}, \mathrm{nSequence} \in \mathbb{N}, \mathrm{witness})$. The types impose no upper bound on $\mathrm{version}$ or on any $\mathrm{nSequence}$.
- $\mathrm{inputSequence}(\mathrm{tx}, n_{\mathrm{in}})$ is the $\mathrm{nSequence}$ field of the $n_{\mathrm{in}}$-th input of $\mathrm{tx}$ (zero-indexed); when $n_{\mathrm{in}} \ge |\mathrm{tx}.\mathrm{vin}|$ a default input with $\mathrm{nSequence} = 0$ is substituted, so $\sigma = 0$ in that case. (Then the right-hand side reduces to $2 \le \mathrm{tx}.\mathrm{version} \land \delta \le 0$, i.e. $\delta = 0$ under the hypotheses.)
- $\mathrm{checkSequence}(\mathrm{tx}, n_{\mathrm{in}}, s)$, for an integer $s$, is the boolean computed as follows. Let $\sigma$ be as above (the same out-of-range default applies). If $\mathrm{tx}.\mathrm{version} < 2$, the result is $\mathrm{false}$. Else, if $\sigma \mathbin{\&} 2^{31} \ne 0$, the result is $\mathrm{false}$. Else let $\tau := \sigma \mathbin{\&} M$ and $\varsigma := \operatorname{toNat}(s) \mathbin{\&} M$ (so a negative $s$ is treated as $0$ here). If it is **not** the case that either ($\tau < 2^{22}$ and $\varsigma < 2^{22}$) or ($2^{22} \le \tau$ and $2^{22} \le \varsigma$), the result is $\mathrm{false}$. Else, if $\tau < \varsigma$, the result is $\mathrm{false}$. Otherwise the result is $\mathrm{true}$.

**What is and is not quantified.** The theorem is stated for arbitrary $\mathrm{tx}$ (including transactions with no inputs, or with fewer than $n_{\mathrm{in}}+1$ inputs) and arbitrary $n_{\mathrm{in}}$; the only constraints are on $\delta$: non-negative and strictly below $2^{16} = 65536$. No hypothesis bounds $\sigma$ or $\mathrm{tx}.\mathrm{version}$. The right-hand side's third conjunct requires the masked sequence value $\sigma \mathbin{\&} M$ to have bit $22$ clear, and the fourth requires $\delta$ to be at most that masked value (which, with bit $22$ clear, lies in $[0, 65535]$).
