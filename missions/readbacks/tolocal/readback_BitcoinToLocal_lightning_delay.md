# Read-back: `BitcoinToLocal.lightning_delay`

**Statement.** For every transaction $\mathrm{tx}$, every natural number $n_{\mathrm{in}}$, and every integer $\delta$ (named `delay`), under the three hypotheses

$$
0 \le \delta, \qquad \delta < 2^{16}, \qquad \mathrm{inputSequence}(\mathrm{tx}, n_{\mathrm{in}}) < 2^{16},
$$

the following equivalence holds:

$$
\mathrm{checkSequence}(\mathrm{tx}, n_{\mathrm{in}}, \delta) = \mathrm{true}
\iff
2 \le \mathrm{tx}.\mathrm{version}\ \ \land\ \ \operatorname{toNat}(\delta) \le \mathrm{inputSequence}(\mathrm{tx}, n_{\mathrm{in}}).
$$

Since $\delta \ge 0$, $\operatorname{toNat}(\delta)$ (which sends negative integers to $0$) is just $\delta$ viewed as a natural number.

**The objects involved.**

- A *transaction* is a record $(\mathrm{version} \in \mathbb{N},\ \mathrm{vin},\ \mathrm{vout},\ \mathrm{nLockTime} \in \mathbb{N})$; each element of the list $\mathrm{vin}$ is an input record carrying, among other fields, a natural number $\mathrm{nSequence}$. No upper bound on $\mathrm{version}$ or $\mathrm{nSequence}$ comes from the types.
- $\mathrm{inputSequence}(\mathrm{tx}, n_{\mathrm{in}})$ is the $\mathrm{nSequence}$ of the $n_{\mathrm{in}}$-th input of $\mathrm{tx}$ (zero-indexed), or $0$ when $n_{\mathrm{in}} \ge |\mathrm{tx}.\mathrm{vin}|$ (a default input is substituted). Write $\sigma$ for this value; the third hypothesis says $\sigma < 65536$, which is automatically true in the out-of-range case.
- $\mathrm{checkSequence}(\mathrm{tx}, n_{\mathrm{in}}, s)$, for an integer $s$, is the boolean: if $\mathrm{tx}.\mathrm{version} < 2$ then $\mathrm{false}$; else if $\sigma \mathbin{\&} 2^{31} \ne 0$ then $\mathrm{false}$; else, with $M := 2^{22} \mid \mathtt{0xffff} = \mathtt{0x40ffff}$, $\tau := \sigma \mathbin{\&} M$ and $\varsigma := \operatorname{toNat}(s) \mathbin{\&} M$: if neither ($\tau < 2^{22}$ and $\varsigma < 2^{22}$) nor ($2^{22} \le \tau$ and $2^{22} \le \varsigma$) then $\mathrm{false}$; else if $\tau < \varsigma$ then $\mathrm{false}$; else $\mathrm{true}$. (Here $\mathbin{\&}$ and $\mid$ are bitwise AND and OR on natural numbers; the constants are the preamble's $\mathrm{SEQUENCE\_LOCKTIME\_DISABLE\_FLAG} = 2^{31}$, $\mathrm{SEQUENCE\_LOCKTIME\_TYPE\_FLAG} = 2^{22}$, $\mathrm{SEQUENCE\_LOCKTIME\_MASK} = \mathtt{0xffff}$.)

**Edge cases made explicit.** When $n_{\mathrm{in}}$ is out of range, $\sigma = 0$ and the right-hand side becomes $2 \le \mathrm{tx}.\mathrm{version} \land \delta \le 0$, i.e. $\delta = 0$. The hypotheses bound both $\delta$ and $\sigma$ strictly below $2^{16}$, so each lies entirely within the low $16$ bits; neither bit $22$ nor bit $31$ can be set in either. Nothing constrains $\mathrm{tx}.\mathrm{version}$ beyond what appears in the conclusion.
