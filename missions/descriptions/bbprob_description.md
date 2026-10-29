## The claim

The backbone mission proved chain growth, common prefix and chain quality for every *typical* execution: one in which, on every window of at least $\lambda$ rounds, the adversary finds fewer blocks than there are uniquely successful honest rounds. Garay, Kiayias and Leonardos show that under honest majority executions are typical except with probability exponentially small in $\lambda$. This mission proves that half: the random mining process, its expectations, Hoeffding concentration per window, the union bound, and the end-to-end statement that every consequence of typicality holds with probability at least $1 - (L+1)^2 e^{-\text{rate}(\lambda+1)}$, against any adversary strategy.

## What is proved

- **The process** (`iIndepFun_rounds`, `map_eval_P`): independent rounds, each a product of independent Bernoulli($p$) queries, $n$ honest and $t$ adversarial.
- **Expectations and honest majority** (`integral_round*`, `expect_X`, `expect_Y`, `expect_Z`, `expect_Y_sub_expect_Z`, `margin_ge_of_honest_majority`, `expect_Z_add_le_expect_Y`, `expect_Z_lt_expect_Y`): $E[Y] = np(1-p)^{n-1}$, $E[Z] = tp$, $E[X] = 1-(1-p)^n$, and with $t \le (1-\delta)n$ and $np \le \delta/2$ the margin $E[Y] - E[Z]$ is at least $\delta p n/2$.
- **Concentration** (`sets_hoeffding`, `window_bound`, `window_bound_rate`): a window of $k$ rounds fails the typicality inequality with probability at most $e^{-\text{rate}(k+1)}$.
- **Typicality** (`typicalOn_failure_le_of_window`, `typicalOn_failure_le`, `typicalOn_prob_ge`, `typical_toExecution_iff`, `typicalTrunc_failure_le`): on a horizon of $L$ rounds, typicality fails with probability at most $(L+1)^2 e^{-\text{rate}(\lambda+1)}$, independently of the network and of the adversary's chain choices.
- **End to end** (`backbone_failure_le`, `backbone_prob_ge`, the goal): any property implied by legality and typicality, in particular the backbone mission's common prefix, chain growth and chain quality, holds for every adversary strategy with that probability.

## What this rests on and what it does not say

The bound is Hoeffding's, with each round's difference ranging over $t+1$ values, not the paper's multiplicative Chernoff bounds (absent from Mathlib), so the rate is weak when $t$ is large and $p$ small; the window conditions $4tp \le (\lambda-3)\,\text{margin}$, $\lambda \ge 2$ are sufficient conditions chosen for clean statements. The execution is frozen after the horizon (party 0 mines alone, the adversary finds nothing) so that the deterministic theorems apply to infinite executions. The paper's separate bounds on $X$ are not proved; the deterministic layer does not need them. The common-prefix instance is a one-line composition left out of the public theorems because a split file cannot import another mission's solution. ([ePrint 2014/765](https://eprint.iacr.org/2014/765))
