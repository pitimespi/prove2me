We prove that for heights $h_1 \le h_2$ every flag of an ordinary block at $h_1$ is a flag at $h_2$.

The three base flags `P2SH`, `WITNESS`, `TAPROOT` are `true` at every height, so their inclusions are trivial. Each of the four height-gated flags is `false || activeAt`$(h, dep)$, i.e. the activation test alone; by `BitcoinActivation.activeAt_mono` activation at $h_1$ implies activation at $h_2$. Pointwise, every flag enforced at $h_1$ is enforced at $h_2$.
