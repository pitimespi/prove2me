# Read-back: `BitcoinUniqueness.scan_runs_late`

**Statement.** For every chain state $S$ (a record of a list of headers $S.\mathrm{headers}$ and a ledger $S.\mathrm{utxo}$) and every block $b$, if
- $1{,}983{,}702 \le |S.\mathrm{headers}|$ (the constant $\mathrm{BIP34\_IMPLIES\_BIP30\_LIMIT} = 1983702$ is at most the next height of $S$),

then $\mathrm{ScanRuns}(S, b)$ holds.

Formally:
$$\forall S,\ \forall b,\quad 1983702 \le |S.\mathrm{headers}| \ \Longrightarrow\ \mathrm{ScanRuns}(S,b).$$

### What ScanRuns says

$\mathrm{ScanRuns}(S,b)$ is, by definition, $\mathrm{bip30Checked}(S, H, \eta) = \mathtt{true}$ with $H := |S.\mathrm{headers}|$ and $\eta := \mathrm{headerHash}(b.\mathrm{header})$ (double-SHA-256 of the serialized header), which unfolds to
$$\Big(\neg\,\mathrm{Rep}(H,\eta)\ \wedge\ \neg\,\mathrm{Anc}(S)\Big)\ \vee\ 1{,}983{,}702 \le H,$$
where $\mathrm{Rep}(H,\eta)$ holds iff $(H = 91842 \wedge \eta = C_{91842})$ or $(H = 91880 \wedge \eta = C_{91880})$ for two fixed 32-byte constants, and $\mathrm{Anc}(S)$ holds iff $S.\mathrm{headers}$ has an element at zero-based position $227{,}931$ (i.e. $H \ge 227{,}932$) whose header hash equals a fixed 32-byte constant $C_{34}$. The block $b$ enters only through $\eta$.

### Edge cases and scope

- The block $b$ is completely unconstrained: any header, any transaction list (including empty), any hash.
- The chain state $S$ is unconstrained apart from the length of its header list; there is no reachability, validity, or well-formedness hypothesis, and the ledger $S.\mathrm{utxo}$ is arbitrary.
- The hypothesis coincides with the second disjunct of the unfolded conclusion, so the statement is of the form "$P \Rightarrow (Q \vee P)$" after unfolding.
- "Height" here is literally the length of the header list, not a field read from any header or from $b$.
