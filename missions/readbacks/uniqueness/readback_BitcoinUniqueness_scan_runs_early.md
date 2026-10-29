# Read-back: `BitcoinUniqueness.scan_runs_early`

**Statement.** For every chain state $S$ (a list of headers $S.\mathrm{headers}$ and a ledger $S.\mathrm{utxo}$) and every block $b$, if
- $|S.\mathrm{headers}| \le 227{,}931$ (the length of the header list is at most the constant $\mathrm{BIP34Height} = 227931$), and
- $\mathrm{isBIP30Repeat}\big(|S.\mathrm{headers}|,\ \mathrm{headerHash}(b.\mathrm{header})\big) = \mathtt{false}$, i.e. it is **not** the case that $\big(|S.\mathrm{headers}| = 91842$ and the header hash of $b$ equals the fixed constant $C_{91842}\big)$, and **not** the case that $\big(|S.\mathrm{headers}| = 91880$ and the header hash of $b$ equals the fixed constant $C_{91880}\big)$,

then $\mathrm{ScanRuns}(S, b)$ holds.

Formally, with $H := |S.\mathrm{headers}|$ and $\eta := \mathrm{headerHash}(b.\mathrm{header})$:
$$\forall S,\ \forall b,\quad H \le 227931 \ \wedge\ \neg\mathrm{Rep}(H,\eta) \ \Longrightarrow\ \mathrm{ScanRuns}(S,b).$$

### What ScanRuns says

$\mathrm{ScanRuns}(S,b)$ is, by definition, $\mathrm{bip30Checked}(S, H, \eta) = \mathtt{true}$ with $H := |S.\mathrm{headers}|$ and $\eta := \mathrm{headerHash}(b.\mathrm{header})$ (double-SHA-256 of the serialized header), which unfolds to
$$\Big(\neg\,\mathrm{Rep}(H,\eta)\ \wedge\ \neg\,\mathrm{Anc}(S)\Big)\ \vee\ 1{,}983{,}702 \le H,$$
where $\mathrm{Rep}(H,\eta)$ holds iff $(H = 91842 \wedge \eta = C_{91842})$ or $(H = 91880 \wedge \eta = C_{91880})$ for two fixed 32-byte constants, and $\mathrm{Anc}(S)$ holds iff $S.\mathrm{headers}$ has an element at zero-based position $227{,}931$ (i.e. $H \ge 227{,}932$) whose header hash equals a fixed 32-byte constant $C_{34}$. The block $b$ enters only through $\eta$.

### Edge cases and scope

- The first hypothesis is stated on $|S.\mathrm{headers}|$ directly; by definition this is the same number as $S.\mathrm{nextHeight}$ used inside $\mathrm{ScanRuns}$.
- Under $H \le 227{,}931$ the header list has no element at position $227{,}931$, so the $\mathrm{Anc}(S)$ test in the unfolded conclusion is false by the definition's "no such element" branch; the second hypothesis is exactly $\neg\mathrm{Rep}(H,\eta)$. The statement therefore asserts the first disjunct of the unfolded conclusion from hypotheses that are its two conjuncts (one of them in a syntactically different but definitionally equal form).
- $H = 0$ (empty header list) is included; $H = 227{,}931$ is included (the inequality is non-strict).
- No reachability or validity of $S$ or $b$ is assumed; the ledger and all header contents are arbitrary; the block enters only through its header hash.
- The statement says nothing about states with $227{,}931 < H < 1{,}983{,}702$.
