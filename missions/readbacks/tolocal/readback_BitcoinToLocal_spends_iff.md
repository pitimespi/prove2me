# Read-back: `BitcoinToLocal.spends_iff`

**Statement.** Let $f$ be a script flag record (booleans $f.\mathrm{cltv}, f.\mathrm{csv}, f.\mathrm{nulldummy}$), $o$ an oracle (a record of five arbitrary hash functions on byte strings, an arbitrary $o.\mathrm{checkSig} : \text{bytes} \times \text{bytes} \to \mathrm{Option}\,\mathrm{Bool}$ taking the signature first and the key second, and arbitrary $o.\mathrm{checkLockTime}, o.\mathrm{checkSequence} : \mathbb{Z} \to \mathrm{Bool}$; no properties assumed), $R$ (`rev`) and $D$ (`dpk`) byte strings, $\delta \in \mathbb{Z}$ (`delay`), and $\mathrm{st}$ an arbitrary list of byte strings (an initial stack, top-first). Assume

$$
|R| \le 520, \qquad |D| \le 520, \qquad |\delta| < 2^{32}
$$

($520$ is `MAX_SCRIPT_ELEMENT_SIZE`; $|\delta|$ the absolute value as a natural). Then

$$
\Big( \exists\, \mathrm{res}.\ \ \mathrm{evalScript}\big(f, o, \mathrm{st}, \mathrm{toLocalScript}(R, \delta, D)\big) = \mathrm{some}\ \mathrm{res}\ \land\ |\mathrm{res}| = 1\ \land\ \mathrm{topTrue}(\mathrm{res}) = \mathrm{true} \Big)
\iff
\Big( \exists\, b\ \mathrm{sig}.\ \ \mathrm{st} = [b, \mathrm{sig}]\ \land\ \mathrm{SpendCondition}(f, o, R, \delta, D, b, \mathrm{sig}) \Big).
$$

On the left, $\mathrm{res}$ ranges over lists of byte strings; $\mathrm{topTrue}(\mathrm{res})$ is $\mathrm{false}$ for the empty list and $\mathrm{castToBool}$ of the first (top) element otherwise, so with $|\mathrm{res}| = 1$ the left side says: evaluation succeeds with a one-element stack $[x]$ and $\mathrm{castToBool}(x) = \mathrm{true}$. On the right, $b$ and $\mathrm{sig}$ range over byte strings; $\mathrm{st} = [b, \mathrm{sig}]$ means the initial stack has **exactly two** elements, $b$ on top and $\mathrm{sig}$ beneath. No hypothesis constrains $\mathrm{st}$ (its length or element sizes) — the two-element shape is part of the conclusion, not an assumption.

**Unfolded notions.**

- $\mathrm{castToBool}(x)$: $\mathrm{false}$ for $x = [\,]$; for $[y]$, true iff $y \ne 0$ and $y \ne \mathtt{0x80}$; for $y :: \mathrm{rest}$ with $\mathrm{rest} \ne [\,]$, true iff $y \ne 0$ or $\mathrm{castToBool}(\mathrm{rest})$.
- $\mathrm{CsvPasses}(f, o, \delta)$ is $f.\mathrm{csv} = \mathrm{false} \lor \big(0 \le \delta \land ((\operatorname{toNat}(\delta) \mathbin{\&} 2^{31}) \ne 0 \lor o.\mathrm{checkSequence}(\delta) = \mathrm{true})\big)$, where $\operatorname{toNat}$ truncates negatives to $0$ and $\mathbin{\&}$ is bitwise AND on naturals.
- $\mathrm{SpendCondition}(f, o, R, \delta, D, b, \mathrm{sig})$ is
  $$
  \big(\mathrm{castToBool}(b) = \mathrm{true} \land o.\mathrm{checkSig}(\mathrm{sig}, R) = \mathrm{some}\,\mathrm{true}\big)\ \lor\ \big(\mathrm{castToBool}(b) = \mathrm{false} \land \mathrm{CsvPasses}(f, o, \delta) \land o.\mathrm{checkSig}(\mathrm{sig}, D) = \mathrm{some}\,\mathrm{true}\big);
  $$
  in each disjunct the oracle's verdict must be exactly $\mathrm{some}\,\mathrm{true}$ ($\mathrm{none}$ and $\mathrm{some}\,\mathrm{false}$ both fail).
- $\mathrm{toLocalScript}(R, \delta, D)$ is the nine-instruction list $[\mathrm{op}\,\mathtt{0x63},\ \mathrm{push}\,R,\ \mathrm{op}\,\mathtt{0x67},\ \mathrm{numInstr}(\delta),\ \mathrm{op}\,\mathtt{0xb2},\ \mathrm{op}\,\mathtt{0x75},\ \mathrm{push}\,D,\ \mathrm{op}\,\mathtt{0x68},\ \mathrm{op}\,\mathtt{0xac}]$, where $\mathrm{numInstr}(\delta)$ is the opcode with byte $\delta + 80$ when $\delta = -1$ or $1 \le \delta \le 16$ (bytes $\mathtt{0x4f}$, $\mathtt{0x51}$–$\mathtt{0x60}$) and otherwise the data push of $\mathrm{serialize}(\delta)$ ($\mathrm{serialize}(0) = [\,]$; for $\delta \ne 0$ the little-endian magnitude bytes of $|\delta|$ without trailing zeros, plus an appended $\mathtt{0x80}$/$\mathtt{0x00}$ byte when the top bit of the last byte is set, else the top bit set on the last byte when $\delta < 0$).

**The interpreter `evalScript`.** $\mathrm{evalScript}(f, o, S, P)$ starts from the state (main stack $S$, alt-stack $[\,]$, condition stack $\mathrm{vfExec} = [\,]$, $\mathrm{opCount} = 0$), applies one step per instruction of $P$ in order, and returns $\mathrm{some}$ of the final main stack if every step succeeds and $\mathrm{vfExec}$ is empty at the end; otherwise $\mathrm{none}$. A step is:

- **Push of data $x$.** Fail if $|x| > 520$. Otherwise, if every entry of $\mathrm{vfExec}$ is true, put $x$ on top of the main stack (else leave the state unchanged). Then fail if $|\text{stack}| + |\text{alt-stack}| > 1000$.
- **Opcode $c$.** Let $e$ be "every entry of $\mathrm{vfExec}$ is true". If $c > \mathtt{0x60}$: fail if $\mathrm{opCount} + 1 > 201$, else increment $\mathrm{opCount}$. Fail if $c$ is one of the fifteen disabled opcodes (none occur here). If $e$ holds or $\mathtt{0x63} \le c \le \mathtt{0x68}$, apply $\mathrm{execOp}$ with flag $e$ and then fail if $|\text{stack}| + |\text{alt-stack}| > 1000$; otherwise leave the state unchanged apart from that size check.

$\mathrm{execOp}$ for the opcodes of this script:

- $\mathtt{0x4f}$, $\mathtt{0x51}$–$\mathtt{0x60}$ (opcode form of $\mathrm{numInstr}(\delta)$): push $\mathrm{serialize}(c - 80)$.
- $\mathtt{0x63}$ (`OP_IF`): if $e$, fail on an empty main stack, else pop the top $x$ and push $\mathrm{castToBool}(x)$ onto $\mathrm{vfExec}$; if not $e$, push $\mathrm{false}$ onto $\mathrm{vfExec}$ without popping.
- $\mathtt{0x67}$ (`OP_ELSE`): fail if $\mathrm{vfExec}$ is empty, else negate its head.
- $\mathtt{0x68}$ (`OP_ENDIF`): fail if $\mathrm{vfExec}$ is empty, else remove its head.
- $\mathtt{0xb2}$ (`OP_CHECKSEQUENCEVERIFY`): if $f.\mathrm{csv} = \mathrm{false}$, unchanged. Else fail on an empty main stack; let $x$ be the top (not removed); fail if $|x| > 5$; let $n$ be the signed little-endian value of $x$ (top bit of last byte is the sign; empty is $0$); fail if $n < 0$; if $(\operatorname{toNat}(n) \mathbin{\&} 2^{31}) \ne 0$, unchanged; else fail if $o.\mathrm{checkSequence}(n) = \mathrm{false}$; else unchanged.
- $\mathtt{0x75}$ (`OP_DROP`): fail on an empty main stack, else remove the top.
- $\mathtt{0xac}$ (`OP_CHECKSIG`): the main stack must be $\mathrm{pk} :: \mathrm{sg} :: \mathrm{rest}$ ($\mathrm{pk}$ on top), else fail; then $o.\mathrm{checkSig}(\mathrm{sg}, \mathrm{pk})$: $\mathrm{none}$ fails, $\mathrm{some}\,\mathrm{ok}$ yields the stack $\mathrm{boolBytes}(\mathrm{ok}) :: \mathrm{rest}$ with $\mathrm{boolBytes}(\mathrm{true}) = [\mathtt{0x01}]$, $\mathrm{boolBytes}(\mathrm{false}) = [\,]$.

The theorem is a two-sided equivalence: a successful run of this script from $\mathrm{st}$ ending with exactly one element that casts to true happens precisely when $\mathrm{st}$ is a two-element stack $[b, \mathrm{sig}]$ satisfying $\mathrm{SpendCondition}$.
