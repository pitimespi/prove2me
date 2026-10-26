# Read-back: `BitcoinTaproot.checkmultisig_rejected`

**Binders.** $c$ : a `TapCtx` record (interpreter flags `cltv`, `csv`, `nulldummy` : Booleans; a transaction $\mathrm{tx}$; a list $\mathrm{spent}$ of outputs; an input index $\mathrm{nIn} \in \mathbb{N}$); $\mathrm{ed}$ : an `ExecData` record (`annexPresent` : Boolean, `annexHash`, `tapleafHash` : byte strings, `codeseparatorPos` : natural); $\mathrm{fExec}$ : a Boolean; $\mathrm{ts}$ : a `TapState` record (an interpreter state $\mathrm{st}$ with main stack, alt stack, condition stack `vfExec` and op count; an integer `weightLeft`; naturals `codeseparatorPos` and `opcodePos`).

**Hypotheses.** None.

**Conclusion.** Both of the following hold:

$$\mathrm{tapExecOp}(c, \mathrm{ed}, \mathrm{fExec}, \texttt{0xae}, \mathrm{ts}) = \mathrm{none}
\quad\text{and}\quad
\mathrm{tapExecOp}(c, \mathrm{ed}, \mathrm{fExec}, \texttt{0xaf}, \mathrm{ts}) = \mathrm{none},$$

where $\texttt{0xae}$ is `OP_CHECKMULTISIG` and $\texttt{0xaf}$ is `OP_CHECKMULTISIGVERIFY` as 8-bit values, and $\mathrm{none}$ is the "script failure" result of the optional return type.

Unfolded: $\mathrm{tapExecOp}$ dispatches on the opcode byte in this order: (i) if it is `OP_IF` ($\texttt{0x63}$) or `OP_NOTIF` ($\texttt{0x64}$), the minimal-if-guarded conditional; (ii) if it is `OP_CHECKSIG` ($\texttt{0xac}$) or `OP_CHECKSIGVERIFY` ($\texttt{0xad}$), the Tapscript signature check; (iii) if it is `OP_CHECKSIGADD` ($\texttt{0xba}$), the add-variant; (iv) if it is $\texttt{0xae}$ or $\texttt{0xaf}$, the result is $\mathrm{none}$ unconditionally; (v) if it is `OP_CODESEPARATOR` ($\texttt{0xab}$), record the opcode position; (vi) otherwise, delegate to the legacy per-opcode interpreter. The two opcodes named fall into case (iv), and the result does not depend on $\mathrm{fExec}$, on the stack contents, on the weight, or on any other field.

**Edge cases the quantifiers include.** $\mathrm{fExec} = \mathrm{false}$ (an unexecuted branch; the function itself still returns $\mathrm{none}$, though the surrounding step function would only call it for opcodes in the range $\texttt{0x63}$–$\texttt{0x68}$ when not executing); empty stacks; negative `weightLeft`; arbitrary $\mathrm{ed}$.
