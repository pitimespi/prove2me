We compute the two evaluations of `verifyScriptPlain` step by step.

**scriptSig.** $[\langle sig\rangle, \langle pk\rangle]$ from the empty stack gives, by `BitcoinScript.eval_pushes` (both elements $\le 520$ bytes, two $\le 1000$), the stack $[pk, sig]$ (top first).

**scriptPubKey** $\mathtt{DUP\ HASH160}\ \langle h\rangle\ \mathtt{EQUALVERIFY\ CHECKSIG}$ on $[pk, sig]$. Each opcode step is reduced with `step_op_small`, which packages the per-opcode checks of `step` (operation count $k+1 \le 201$ for $k \le 3$, not disabled, `vfExec = []` so the opcode executes) and leaves the `execOp` call followed by the stack-size test; the opcode effects `execOp_dup`, `execOp_hash160`, `execOp_equalverify`, `execOp_checksig` are each proved by `rfl`.

* `DUP`: $[pk, pk, sig]$; stack size $3 \le 1000$.
* `HASH160`: $[\mathrm{hash160}(pk), pk, sig]$.
* push $\langle h\rangle$: $[h, \mathrm{hash160}(pk), pk, sig]$, using $|h| \le 520$ and $4 \le 1000$.
* `EQUALVERIFY`: pops two and compares; if $\mathrm{hash160}(pk) \ne h$ the step returns `none`, the run fails, and the right-hand side is false too. If equal, the stack is $[pk, sig]$.
* `CHECKSIG`: pops `pubkey :: sig`, consults `o.checkSig sig pubkey`; `none` fails the script (and the right side, which needs `some true`), `some ok` pushes `boolBytes ok`.

The empty remainder returns the state (`vfExec = []`), and the final test `castToBool (boolBytes ok) = ok` (`castToBool_boolBytes`). Hence success iff $\mathrm{hash160}(pk) = h$ and $ok = \mathtt{true}$, which is the right-hand side; the `by_cases` on the hash equality and `cases` on the oracle's answer give both directions at once.
