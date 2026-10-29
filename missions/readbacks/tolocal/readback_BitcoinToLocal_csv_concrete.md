# Read-back: `BitcoinToLocal.csv_concrete`

**Statement.** Let

- $f$ be a script flag record, a triple of booleans $(f.\mathrm{cltv}, f.\mathrm{csv}, f.\mathrm{nulldummy})$;
- $\mathrm{sf}$ be a signature-layer flag record, a quadruple of booleans $(\mathrm{dersig}, \mathrm{lowS}, \mathrm{strictenc}, \mathrm{witnessPubkeyType})$;
- $\mathrm{tx}$ be a transaction (a record with $\mathrm{version} \in \mathbb{N}$, a list $\mathrm{vin}$ of inputs each carrying an $\mathrm{nSequence} \in \mathbb{N}$, a list $\mathrm{vout}$, and $\mathrm{nLockTime} \in \mathbb{N}$);
- $n_{\mathrm{in}} \in \mathbb{N}$, $\mathrm{amount} \in \mathbb{Z}$;
- $v$ be a signature version, one of the two values $\mathrm{base}$ or $\mathrm{witnessV0}$;
- $\mathrm{sc}$ be a byte string (a script code);
- $\delta \in \mathbb{Z}$ (named `delay`).

Assume the three hypotheses

$$
f.\mathrm{csv} = \mathrm{true}, \qquad 0 \le \delta, \qquad \delta < 2^{16}.
$$

Then

$$
\mathrm{CsvPasses}\big(f,\ \mathrm{legacyOracle}(\mathrm{sf}, \mathrm{tx}, n_{\mathrm{in}}, \mathrm{amount}, v, \mathrm{sc}),\ \delta\big)
\iff
\mathrm{checkSequence}(\mathrm{tx}, n_{\mathrm{in}}, \delta) = \mathrm{true}.
$$

**Unfolding the left-hand side.** $\mathrm{legacyOracle}(\mathrm{sf}, \mathrm{tx}, n_{\mathrm{in}}, \mathrm{amount}, v, \mathrm{sc})$ is the concrete oracle record whose five hash components are the preamble's SHA-256, SHA-1, RIPEMD-160, HASH160 and HASH256 implementations, whose signature-check component is the pre-tapscript checker built from $\mathrm{sf}, \mathrm{tx}, n_{\mathrm{in}}, \mathrm{amount}, v, \mathrm{sc}$, whose lock-time component is the transaction lock-time check for $(\mathrm{tx}, n_{\mathrm{in}})$, and whose **sequence component is exactly** $s \mapsto \mathrm{checkSequence}(\mathrm{tx}, n_{\mathrm{in}}, s)$. The proposition $\mathrm{CsvPasses}(f, o, \delta)$ is

$$
f.\mathrm{csv} = \mathrm{false}\ \lor\ \Big(0 \le \delta \land \big((\operatorname{toNat}(\delta) \mathbin{\&} 2^{31}) \ne 0 \lor o.\mathrm{checkSequence}(\delta) = \mathrm{true}\big)\Big),
$$

and it consults only the sequence component of $o$. Under the hypothesis $f.\mathrm{csv} = \mathrm{true}$ the first disjunct is false, so the left-hand side says:

$$
0 \le \delta\ \land\ \Big( (\delta \mathbin{\&} 2^{31}) \ne 0\ \lor\ \mathrm{checkSequence}(\mathrm{tx}, n_{\mathrm{in}}, \delta) = \mathrm{true} \Big),
$$

where $\operatorname{toNat}(\delta) = \delta$ because $\delta \ge 0$. The parameters $\mathrm{sf}$, $\mathrm{amount}$, $v$ and $\mathrm{sc}$ enter the statement only through oracle components that $\mathrm{CsvPasses}$ never reads.

**Unfolding the right-hand side.** $\mathrm{checkSequence}(\mathrm{tx}, n_{\mathrm{in}}, s)$ for an integer $s$: let $\sigma$ be the $\mathrm{nSequence}$ of the $n_{\mathrm{in}}$-th input of $\mathrm{tx}$ (zero-indexed), or $0$ if $n_{\mathrm{in}} \ge |\mathrm{tx}.\mathrm{vin}|$. If $\mathrm{tx}.\mathrm{version} < 2$, return $\mathrm{false}$. Else if $\sigma \mathbin{\&} 2^{31} \ne 0$, return $\mathrm{false}$. Else let $M := 2^{22} \mid \mathtt{0xffff} = \mathtt{0x40ffff}$, $\tau := \sigma \mathbin{\&} M$, $\varsigma := \operatorname{toNat}(s) \mathbin{\&} M$. If neither ($\tau < 2^{22}$ and $\varsigma < 2^{22}$) nor ($2^{22} \le \tau$ and $2^{22} \le \varsigma$) holds, return $\mathrm{false}$. Else if $\tau < \varsigma$, return $\mathrm{false}$. Else return $\mathrm{true}$.

**Remarks on the hypotheses.** The constant $2^{31}$ in $\mathrm{CsvPasses}$ is the script-layer constant $2147483648$, numerically equal to the signature-layer $2^{31}$ used inside $\mathrm{checkSequence}$. The hypothesis $\delta < 2^{16}$ places $\delta$ strictly below $65536$; in particular bit $31$ of $\delta$ is clear, so the disjunct $(\delta \mathbin{\&} 2^{31}) \ne 0$ is false for every $\delta$ admitted by the hypotheses. No hypothesis constrains $\mathrm{tx}$, $n_{\mathrm{in}}$ (which may be out of range), $\mathrm{amount}$, $v$, $\mathrm{sc}$ or $\mathrm{sf}$.
