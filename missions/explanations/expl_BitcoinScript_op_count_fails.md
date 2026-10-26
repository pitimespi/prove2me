We prove that a script with more than 201 non-push instructions never evaluates successfully.

Two step facts. `step_push_opCount`: a successful push step leaves `opCount` unchanged (the pushed state is `{ s with stack := … }` or `s`). `step_op_opCount`: a successful opcode step satisfies $s.\mathrm{opCount} + 1 \le s'.\mathrm{opCount} \le 201$ — the step fails unless $s.\mathrm{opCount} + 1 \le 201$, sets the count to $s.\mathrm{opCount} + 1$, and then either returns that state (skipped opcode) or executes `execOp`, whose result by `BitcoinScript.execOp_opCount` has a count that is unchanged or still $\le 201$.

The loop invariant `run_opCount`: if `run f o s script = some s'` then $s.\mathrm{opCount} + \mathrm{opsIn}(script) \le s'.\mathrm{opCount}$, and if the script has at least one opcode, $s'.\mathrm{opCount} \le 201$. By induction on the script: pushes contribute nothing and keep the count, opcodes contribute one; for the bound, if the tail still has an opcode the induction hypothesis applies, and if the tail is push-only an inner induction shows the count is frozen at the value the opcode step left, which is $\le 201$.

Applied to `State.initial stack` (count $0$) with $\mathrm{opsIn}(script) > 201$: a successful run would give $201 < \mathrm{opsIn} \le s'.\mathrm{opCount} \le 201$, a contradiction, so `run` returns `none` and so does `evalScript`.
