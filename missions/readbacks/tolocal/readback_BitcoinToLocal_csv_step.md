# Read-back: `BitcoinToLocal.csv_step`

**Statement.** Let

- $f$ be a script flag record, a triple of booleans $(f.\mathrm{cltv}, f.\mathrm{csv}, f.\mathrm{nulldummy})$;
- $o$ be an oracle: a record of five arbitrary hash functions on byte strings, an arbitrary function $o.\mathrm{checkSig}$ from two byte strings to an optional boolean, and two arbitrary functions $o.\mathrm{checkLockTime}, o.\mathrm{checkSequence} : \mathbb{Z} \to \mathrm{Bool}$ (no properties are assumed of any of them);
- $s$ be an interpreter state: a record $(s.\mathrm{stack}, s.\mathrm{altstack}, s.\mathrm{vfExec}, s.\mathrm{opCount})$ where the first two are lists of byte strings written top-first, $s.\mathrm{vfExec}$ is a list of booleans and $s.\mathrm{opCount} \in \mathbb{N}$;
- $\delta \in \mathbb{Z}$ (named `delay`) and $\mathrm{rest}$ a list of byte strings.

Assume the two hypotheses

$$
s.\mathrm{stack} = \mathrm{serialize}(\delta) :: \mathrm{rest} \qquad\text{and}\qquad |\delta| < 2^{32},
$$

where $|\delta|$ is the absolute value as a natural number. Then

$$
\mathrm{execOp}\big(f, o, \mathrm{true}, \mathtt{0xb2}, s\big) \;=\; \begin{cases} \mathrm{some}\ s & \text{if } \mathrm{CsvPasses}(f, o, \delta), \\ \mathrm{none} & \text{otherwise.}\end{cases}
$$

Here $\mathtt{0xb2}$ is the byte the preamble names `OP_CHECKSEQUENCEVERIFY`, and the right-hand side is a case split on the (decidable) proposition $\mathrm{CsvPasses}$. The equality is between optional states: "$\mathrm{some}\ s$" means the step succeeds and returns the **same** state $s$ (nothing popped, no counter changed); "$\mathrm{none}$" means script failure.

**Unfolding `execOp` at `0xb2`.** $\mathrm{execOp}(f, o, e, c, s)$ executes one non-push opcode $c$ on state $s$, where $e$ is an "executing" flag. It is a chain of tests on $c$; for $c = \mathtt{0xb2}$ the earlier tests ($c = \mathtt{0x4f}$ or $\mathtt{0x51} \le c \le \mathtt{0x60}$; $c = \mathtt{0x61}$; $c = \mathtt{0xb1}$) all fail and the `CHECKSEQUENCEVERIFY` branch is taken. That branch **does not consult** the flag $e$ (here $\mathrm{true}$). It computes:

1. If $f.\mathrm{csv} = \mathrm{false}$: return $\mathrm{some}\ s$.
2. Otherwise, if $s.\mathrm{stack}$ is empty: return $\mathrm{none}$. (Excluded here by the first hypothesis.)
3. Otherwise let $x$ be the top element (not removed). Convert $x$ to a number with maximum size $5$ and without the minimal-encoding requirement: if $5 < |x|$ return $\mathrm{none}$; otherwise let $n := \mathrm{setVch}(x)$, where $\mathrm{setVch}(x)$ is: if the last byte of $x$ has its $\mathtt{0x80}$ bit set (for empty $x$, "no"), then $-(\text{little-endian value of } x \text{ with that bit cleared})$, else the little-endian value of $x$ (so $\mathrm{setVch}([\,]) = 0$).
4. If $n < 0$: return $\mathrm{none}$.
5. Else if $(\operatorname{toNat}(n) \mathbin{\&} 2^{31}) \ne 0$: return $\mathrm{some}\ s$.
6. Else if $o.\mathrm{checkSequence}(n) = \mathrm{false}$: return $\mathrm{none}$.
7. Else return $\mathrm{some}\ s$.

Here $2^{31} = 2147483648$ is the script-layer constant `SEQUENCE_LOCKTIME_DISABLE_FLAG`, $\mathbin{\&}$ is bitwise AND on naturals and $\operatorname{toNat}$ truncates negatives to $0$ (irrelevant after step 4).

**Unfolding `serialize` and `CsvPasses`.** $\mathrm{serialize}(0) = [\,]$; for $\delta \ne 0$, let $m$ be the little-endian base-$256$ digits of $|\delta|$ without trailing zeros; if the last byte of $m$ has bit $\mathtt{0x80}$ set, append $\mathtt{0x80}$ (if $\delta < 0$) or $\mathtt{0x00}$ (if $\delta > 0$); otherwise set bit $\mathtt{0x80}$ on the last byte if $\delta < 0$, else leave $m$. The proposition $\mathrm{CsvPasses}(f, o, \delta)$ is

$$
f.\mathrm{csv} = \mathrm{false}\ \lor\ \Big(0 \le \delta \land \big((\operatorname{toNat}(\delta) \mathbin{\&} 2^{31}) \ne 0 \lor o.\mathrm{checkSequence}(\delta) = \mathrm{true}\big)\Big).
$$

**What the hypotheses do.** The first hypothesis fixes the top of the stack to be the encoding of $\delta$ (so the number read back in step 3 is $\mathrm{setVch}(\mathrm{serialize}(\delta))$), with arbitrary $\mathrm{rest}$ below it; the alt-stack, condition stack and op-count of $s$ are unconstrained. The second hypothesis bounds $|\delta|$ below $2^{32}$; step 3 rejects stack tops longer than $5$ bytes. The theorem asserts the step's outcome is exactly: unchanged state when $\mathrm{CsvPasses}(f,o,\delta)$ holds, failure otherwise.
