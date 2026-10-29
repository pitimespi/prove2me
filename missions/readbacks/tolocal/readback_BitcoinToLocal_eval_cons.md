# Read-back: `BitcoinToLocal.eval_cons`

**Statement.** Let $f$ be a script flag record (booleans $f.\mathrm{cltv}, f.\mathrm{csv}, f.\mathrm{nulldummy}$), $o$ an oracle (a record of five arbitrary hash functions on byte strings, an arbitrary $o.\mathrm{checkSig} : \text{bytes} \times \text{bytes} \to \mathrm{Option}\,\mathrm{Bool}$ taking the signature first and the key second, and arbitrary $o.\mathrm{checkLockTime}, o.\mathrm{checkSequence} : \mathbb{Z} \to \mathrm{Bool}$; nothing is assumed about them), $R$ (`rev`), $D$ (`dpk`) and $b$ byte strings, $\delta \in \mathbb{Z}$ (`delay`), and $\mathrm{tl}$ a list of byte strings. Assume

$$
|R| \le 520, \qquad |D| \le 520, \qquad |\delta| < 2^{32}, \qquad |\mathrm{tl}| + 1 \le 1000 .
$$

($520$ and $1000$ are the preamble's `MAX_SCRIPT_ELEMENT_SIZE` and `MAX_STACK_SIZE`; $|\delta|$ is the absolute value as a natural.) Then the result of evaluating the `to_local` script on the initial stack $b :: \mathrm{tl}$ (top-first, so $b$ is on top) is

$$
\mathrm{evalScript}\big(f, o,\ b :: \mathrm{tl},\ \mathrm{toLocalScript}(R, \delta, D)\big) =
\begin{cases}
\mathrm{none} & \text{if } \mathrm{tl} = [\,],\\[4pt]
\mathrm{map}\big(\mathrm{ok} \mapsto \mathrm{boolBytes}(\mathrm{ok}) :: \mathrm{rest}\big)\big(o.\mathrm{checkSig}(\mathrm{sig}, R)\big) & \text{if } \mathrm{tl} = \mathrm{sig} :: \mathrm{rest} \text{ and } \mathrm{castToBool}(b) = \mathrm{true},\\[4pt]
\mathrm{map}\big(\mathrm{ok} \mapsto \mathrm{boolBytes}(\mathrm{ok}) :: \mathrm{rest}\big)\big(o.\mathrm{checkSig}(\mathrm{sig}, D)\big) & \text{if } \mathrm{tl} = \mathrm{sig} :: \mathrm{rest},\ \mathrm{castToBool}(b) = \mathrm{false},\ \text{and } \mathrm{CsvPasses}(f, o, \delta),\\[4pt]
\mathrm{none} & \text{if } \mathrm{tl} = \mathrm{sig} :: \mathrm{rest},\ \mathrm{castToBool}(b) = \mathrm{false},\ \text{and not } \mathrm{CsvPasses}(f, o, \delta).
\end{cases}
$$

Here "$\mathrm{map}(g)$" applied to an optional value sends $\mathrm{none}$ to $\mathrm{none}$ and $\mathrm{some}\,\mathrm{ok}$ to $\mathrm{some}\,(g(\mathrm{ok}))$; so in the second and third cases the result is $\mathrm{none}$ when the oracle's signature check returns $\mathrm{none}$, and otherwise the stack $\mathrm{boolBytes}(\mathrm{ok}) :: \mathrm{rest}$, where $\mathrm{boolBytes}(\mathrm{true}) = [\mathtt{0x01}]$ and $\mathrm{boolBytes}(\mathrm{false}) = [\,]$. Note that $\mathrm{rest}$ (everything below the second element) is preserved untouched, and the result is $\mathrm{some}$ of a stack of length $|\mathrm{rest}| + 1 = |\mathrm{tl}|$ in the successful cases. Note also that no hypothesis bounds $|b|$ or the lengths of the elements of $\mathrm{tl}$; only the count $|\mathrm{tl}| + 1 \le 1000$ of initial stack elements is assumed.

**Unfolded notions.**

- $\mathrm{castToBool}(x)$: $\mathrm{false}$ for $x = [\,]$; for $x = [y]$, true iff $y \ne 0$ and $y \ne \mathtt{0x80}$; for $x = y :: \mathrm{rest}$ with $\mathrm{rest} \ne [\,]$, true iff $y \ne 0$ or $\mathrm{castToBool}(\mathrm{rest})$.
- $\mathrm{CsvPasses}(f, o, \delta)$ is $f.\mathrm{csv} = \mathrm{false} \lor \big(0 \le \delta \land ((\operatorname{toNat}(\delta) \mathbin{\&} 2^{31}) \ne 0 \lor o.\mathrm{checkSequence}(\delta) = \mathrm{true})\big)$, with $\operatorname{toNat}$ truncating negatives to $0$ and $\mathbin{\&}$ bitwise AND on naturals.
- $\mathrm{toLocalScript}(R, \delta, D)$ is the nine-instruction list $[\mathrm{op}\,\mathtt{0x63},\ \mathrm{push}\,R,\ \mathrm{op}\,\mathtt{0x67},\ \mathrm{numInstr}(\delta),\ \mathrm{op}\,\mathtt{0xb2},\ \mathrm{op}\,\mathtt{0x75},\ \mathrm{push}\,D,\ \mathrm{op}\,\mathtt{0x68},\ \mathrm{op}\,\mathtt{0xac}]$, where $\mathrm{numInstr}(\delta)$ is the opcode with byte $\delta + 80$ if $\delta = -1$ or $1 \le \delta \le 16$ (bytes $\mathtt{0x4f}$, $\mathtt{0x51}$–$\mathtt{0x60}$), and otherwise the data push of $\mathrm{serialize}(\delta)$ ($\mathrm{serialize}(0) = [\,]$; for $\delta \ne 0$, the little-endian magnitude bytes of $|\delta|$ without trailing zeros, with an appended $\mathtt{0x80}$ or $\mathtt{0x00}$ byte when the top bit of the last byte is set, otherwise the top bit set on the last byte when $\delta < 0$).

**The interpreter `evalScript`.** $\mathrm{evalScript}(f, o, S, P)$ starts from the state (main stack $= S$, alt-stack $= [\,]$, condition stack $\mathrm{vfExec} = [\,]$, $\mathrm{opCount} = 0$), applies one *step* per instruction of $P$ in order, and, if every step succeeds and the condition stack is empty at the end, returns $\mathrm{some}$ of the final main stack; any step failure, or a non-empty condition stack at the end, gives $\mathrm{none}$. A step is:

- **Push of data $x$.** Fail if $|x| > 520$. Otherwise, if every entry of $\mathrm{vfExec}$ is true, place $x$ on top of the main stack; if some entry is false, leave the state unchanged. Then fail if $|\text{stack}| + |\text{alt-stack}| > 1000$.
- **Opcode $c$.** Let $e$ be "every entry of $\mathrm{vfExec}$ is true". If $c > \mathtt{0x60}$, the opcode is counted: fail if $\mathrm{opCount} + 1 > 201$, else increment $\mathrm{opCount}$. Fail if $c$ is one of the fifteen disabled opcodes ($\mathtt{0x7e}$–$\mathtt{0x81}$, $\mathtt{0x83}$–$\mathtt{0x86}$, $\mathtt{0x8d}$, $\mathtt{0x8e}$, $\mathtt{0x95}$–$\mathtt{0x99}$; none occur here). If $e$ holds or $\mathtt{0x63} \le c \le \mathtt{0x68}$, apply $\mathrm{execOp}$ below with flag $e$, then fail if $|\text{stack}| + |\text{alt-stack}| > 1000$. Otherwise leave the state unchanged apart from that same size check.

$\mathrm{execOp}$ for the opcodes that can occur in this script:

- $\mathtt{0x4f}$, $\mathtt{0x51}$–$\mathtt{0x60}$ (the opcode form of $\mathrm{numInstr}(\delta)$): push $\mathrm{serialize}(c - 80)$ onto the main stack.
- $\mathtt{0x63}$ (`OP_IF`): if $e$ is true, fail on an empty main stack, else pop the top $x$ and push $\mathrm{castToBool}(x)$ onto $\mathrm{vfExec}$; if $e$ is false, push $\mathrm{false}$ onto $\mathrm{vfExec}$ without touching the main stack.
- $\mathtt{0x67}$ (`OP_ELSE`): fail if $\mathrm{vfExec}$ is empty, else negate its head.
- $\mathtt{0x68}$ (`OP_ENDIF`): fail if $\mathrm{vfExec}$ is empty, else remove its head.
- $\mathtt{0xb2}$ (`OP_CHECKSEQUENCEVERIFY`): if $f.\mathrm{csv} = \mathrm{false}$, unchanged. Else fail on an empty main stack; let $x$ be the top (not removed); fail if $|x| > 5$; let $n$ be the signed little-endian value of $x$ (top bit of the last byte is the sign; the empty string is $0$); fail if $n < 0$; if $(\operatorname{toNat}(n) \mathbin{\&} 2^{31}) \ne 0$, unchanged; else fail if $o.\mathrm{checkSequence}(n) = \mathrm{false}$; else unchanged.
- $\mathtt{0x75}$ (`OP_DROP`): fail on an empty main stack, else remove the top.
- $\mathtt{0xac}$ (`OP_CHECKSIG`): the main stack must have the form $\mathrm{pk} :: \mathrm{sg} :: \mathrm{rest}$ ($\mathrm{pk}$ on top), else fail; then $o.\mathrm{checkSig}(\mathrm{sg}, \mathrm{pk})$: $\mathrm{none}$ gives failure, $\mathrm{some}\,\mathrm{ok}$ replaces the two elements by $\mathrm{boolBytes}(\mathrm{ok})$, giving $\mathrm{boolBytes}(\mathrm{ok}) :: \mathrm{rest}$.

The theorem thus equates the outcome of this nine-step run on $b :: \mathrm{tl}$ with the four-case expression displayed above.
