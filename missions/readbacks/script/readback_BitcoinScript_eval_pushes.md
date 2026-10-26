# Read-back: `BitcoinScript.eval_pushes`

**Binders and hypothesis.** Universally quantified: $f$, a flags record (three arbitrary Booleans); $o$, an arbitrary oracle; and $\mathit{ps}$, a finite list of byte lists $[p_1, p_2, \dots, p_k]$ with $k \ge 0$. Two hypotheses:

- $\mathit{hsz}$: for every $p$ occurring in $\mathit{ps}$, $|p| \le 520$ ($= \mathrm{MAX\_SCRIPT\_ELEMENT\_SIZE}$). Elements of length exactly $520$ are allowed; the empty byte list is allowed.
- $\mathit{hlen}$: $k = |\mathit{ps}| \le 1000$ ($= \mathrm{MAX\_STACK\_SIZE}$). Exactly $1000$ pushes are allowed.

**Conclusion.** An equation between optional lists of byte lists:
$$\mathrm{evalScript}\big(f,\ o,\ [],\ [\mathrm{push}(p_1), \mathrm{push}(p_2), \dots, \mathrm{push}(p_k)]\big) = \mathrm{some}\big([p_k, p_{k-1}, \dots, p_1]\big).$$
Evaluating, from the **empty** initial stack, the script consisting solely of one data-push instruction per element of $\mathit{ps}$ (in the same order) succeeds, and the resulting main stack is $\mathit{ps}$ reversed — i.e. with the last-pushed element on top, since stacks are written top-first.

**Unfolding `evalScript`.** $\mathrm{evalScript}(f,o,\mathit{stack},\mathit{script})$ runs `run` from $\mathrm{State.initial}(\mathit{stack}) = \langle \mathit{stack}, [], [], 0\rangle$ (empty alt stack, empty condition stack, zero operation count) and returns the main-stack component of the final state, if the run succeeds. Here the initial main stack is $[]$. `run` processes instructions one by one via `step`, failing at the first failing step, and at the end returns the state only if the condition stack is empty.

**Unfolding `step` on a push.** For $\mathrm{push}(d)$: if $520 < |d|$ the step fails (none). Otherwise, since the condition stack is $[]$ throughout (no conditional opcode ever appears), $\mathrm{allTrue}([]) = \text{true}$ and $d$ is pushed on the main stack. Then the stack-size check: the step fails if $1000 < |\mathrm{stack}| + |\mathrm{altstack}|$; here the alt stack stays empty and after the $j$-th push the main stack has $j \le k \le 1000$ elements, so the check passes under $\mathit{hlen}$. No `opCount` change occurs for pushes.

**So the claim is:** under the two hypotheses, every push step succeeds, the final condition stack is empty (it was never touched), and the final main stack is exactly $[p_k, \dots, p_1]$. For $k = 0$ the claim reads $\mathrm{evalScript}(f,o,[],[]) = \mathrm{some}([])$.

**Role of the parameters.** $f$ and $o$ are not consulted by any push step, so the conclusion is claimed uniformly for all flag settings and all oracles. The hypotheses are exactly the two checks a push step performs; the theorem does not claim what happens if either is violated.

**What is not said.** The theorem is only about scripts made entirely of pushes starting from the empty stack; it says nothing about pushes mixed with opcodes, pushes from a non-empty initial stack (where the $1000$ limit would include the pre-existing elements), or pushes of elements longer than $520$ bytes (no claim that these fail is made here). It does not state that the hypotheses are necessary, only that they suffice. It does not mention `verifyScriptPlain`, the alt stack, `opCount`, or the condition stack in the result (all are discarded by `evalScript`). It does not say the result stack's elements satisfy any numeric or minimality property; a push of a non-minimal encoding, an empty element, or the same element twice is included unchanged. It makes no claim about the uniqueness of the final stack or about pushes being the only way to obtain it.
