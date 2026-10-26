# Read-back: `BitcoinTaproot.minimalif_rejects`

**Binders.** $c$ : a `TapCtx` record (flags `cltv`, `csv`, `nulldummy`; transaction; spent outputs; input index); $\mathrm{ed}$ : an `ExecData` record; $\mathrm{ts}$ : a `TapState` record ($\mathrm{st}$ : interpreter state with main stack, alt stack, condition stack `vfExec`, op count; $\mathrm{weightLeft} \in \mathbb{Z}$; $\mathrm{codeseparatorPos}, \mathrm{opcodePos} \in \mathbb{N}$); $\mathrm{top}$ : a byte string; $\mathrm{rest}$ : a list of byte strings.

**Hypotheses.**
1. $\mathrm{ts}.\mathrm{st}.\mathrm{stack} = \mathrm{top} :: \mathrm{rest}$ (main stack, top first);
2. $1 < |\mathrm{top}| \;\lor\; \big(|\mathrm{top}| = 1 \land \mathrm{top}_0 \neq 1\big)$, where $\mathrm{top}_0$ is the first byte of $\mathrm{top}$ read as a natural number (with default $0$ if there were no such byte — irrelevant under $|\mathrm{top}| = 1$).

**Conclusion.**

$$\mathrm{tapExecOp}(c, \mathrm{ed}, \mathrm{true}, \texttt{0x63}, \mathrm{ts}) = \mathrm{none},$$

where $\texttt{0x63}$ is `OP_IF` and $\mathrm{none}$ is script failure.

Unfolded. $\mathrm{tapExecOp}$ with opcode `OP_IF` (or `OP_NOTIF`) and execute flag $\mathrm{true}$ inspects the main stack: if it is empty the result is $\mathrm{none}$; if its top element $\mathrm{top}$ satisfies $1 < |\mathrm{top}|$ or ($|\mathrm{top}| = 1$ and $\mathrm{top}_0 \neq 1$) the result is $\mathrm{none}$; otherwise it delegates to the legacy interpreter's conditional (which pops $\mathrm{top}$, converts it to a Boolean by the "any non-zero byte, except negative zero" rule, negates for `OP_NOTIF`, and pushes the Boolean onto the condition stack). Hypothesis 2 is exactly the rejecting guard, so the result is $\mathrm{none}$ regardless of $c$, $\mathrm{ed}$, the other fields of $\mathrm{ts}$, and $\mathrm{rest}$.

**Edge cases the quantifiers include.** $\mathrm{top} = [0]$, $[2]$, $[\texttt{0x80}]$, $[\texttt{0x81}]$ (single byte other than $1$ — all rejected); $\mathrm{top} = [1, 0]$ or any longer string (rejected); the statement says nothing about $\mathrm{top} = [\,]$ or $\mathrm{top} = [1]$, nor about `OP_NOTIF`; $\mathrm{rest}$ empty; arbitrary weight and condition stack.
