# Read-back: `BitcoinTaproot.checksig_empty`

**Binders.** $c$ : a `TapCtx` record (flags `cltv`, `csv`, `nulldummy`; transaction $\mathrm{tx}$; list $\mathrm{spent}$ of outputs; index $\mathrm{nIn} \in \mathbb{N}$); $\mathrm{ed}$ : an `ExecData` record; $\mathrm{ts}$ : a `TapState` record with fields $\mathrm{st}$ (interpreter state: main stack, alt stack, condition stack, op count), $\mathrm{weightLeft} \in \mathbb{Z}$, $\mathrm{codeseparatorPos}, \mathrm{opcodePos} \in \mathbb{N}$; $\mathrm{pubkey}$ : a byte string; $\mathrm{rest}$ : a list of byte strings.

**Hypotheses.**
1. $\mathrm{ts}.\mathrm{st}.\mathrm{stack} = \mathrm{pubkey} :: [\,] :: \mathrm{rest}$ — the main stack, top first, has $\mathrm{pubkey}$ on top, then the empty byte string, then $\mathrm{rest}$;
2. $|\mathrm{pubkey}| = 32$.

**Conclusion.**

$$\mathrm{tapExecOp}(c, \mathrm{ed}, \mathrm{true}, \texttt{0xac}, \mathrm{ts}) = \mathrm{some}\big(\mathrm{ts}\text{ with } \mathrm{st} := (\mathrm{ts}.\mathrm{st} \text{ with stack} := [\,] :: \mathrm{rest})\big),$$

where $\texttt{0xac}$ is `OP_CHECKSIG` and $[\,] = \mathrm{boolBytes}(\mathrm{false})$ is the empty byte string (`vchFalse`). All other fields — the alt stack, condition stack and op count of $\mathrm{st}$, and $\mathrm{weightLeft}$, $\mathrm{codeseparatorPos}$, $\mathrm{opcodePos}$ of $\mathrm{ts}$ — are those of $\mathrm{ts}$.

Unfolded. In $\mathrm{tapExecOp}$ the opcode $\texttt{0xac}$ is neither `OP_IF` nor `OP_NOTIF`, so the second branch applies: the stack must match $\mathrm{pubkey} :: \mathrm{sig} :: \mathrm{rest}$ (here $\mathrm{sig} = [\,]$), else the result would be $\mathrm{none}$. Then $\mathrm{evalChecksigTapscript}(c, \mathrm{ed}', \mathrm{sig}, \mathrm{pubkey}, \mathrm{ts}.\mathrm{weightLeft})$ is computed, with $\mathrm{ed}'$ equal to $\mathrm{ed}$ except `codeseparatorPos` $:= \mathrm{ts}.\mathrm{codeseparatorPos}$. That function sets $\mathrm{success} := (\mathrm{sig} \neq [\,])$, here $\mathrm{false}$; $\mathrm{weight} := \mathrm{weightLeft} - 50$ if $\mathrm{success}$ else $\mathrm{weightLeft}$, here unchanged; it returns $\mathrm{none}$ if $\mathrm{success} \land \mathrm{weight} < 0$ (not the case), $\mathrm{none}$ if $|\mathrm{pubkey}| = 0$ (not the case), and for $|\mathrm{pubkey}| = 32$ it returns $\mathrm{none}$ only if $\mathrm{success} \land \neg\mathrm{checkSchnorrSignature}(\dots)$, which is false since $\mathrm{success}$ is false — so no signature verification is performed and the result is $\mathrm{some}(\mathrm{false}, \mathrm{weightLeft})$. Back in $\mathrm{tapExecOp}$, since the opcode is not `OP_CHECKSIGVERIFY`, the new state has stack $\mathrm{boolBytes}(\mathrm{false}) :: \mathrm{rest} = [\,] :: \mathrm{rest}$ and $\mathrm{weightLeft} := \mathrm{weight} = \mathrm{ts}.\mathrm{weightLeft}$.

**Edge cases the quantifiers include.** $\mathrm{ts}.\mathrm{weightLeft}$ negative (no failure, since the budget test requires $\mathrm{success}$); $\mathrm{rest}$ empty; a 32-byte $\mathrm{pubkey}$ that is not a valid x-only key (never inspected); arbitrary transaction, $\mathrm{spent}$, $\mathrm{nIn}$ and $\mathrm{ed}$; the condition stack of $\mathrm{st}$ may be non-empty or contain `false` (the function is called with the execute flag `true` regardless).
