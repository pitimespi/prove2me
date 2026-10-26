# Read-back: `BitcoinVerify.isWitnessProgram_iff`

**Binders and hypothesis.** Three universally quantified variables: $s$, a byte string; $v$, a natural number; $\mathrm{prog}$, a byte string. There are no hypotheses.

**Conclusion.** A biconditional:

$$\mathrm{isWitnessProgram}(s) = \mathrm{some}(v, \mathrm{prog}) \iff v \le 16 \ \wedge\ 2 \le |\mathrm{prog}| \ \wedge\ |\mathrm{prog}| \le 40 \ \wedge\ s = \mathrm{witnessBytes}(v, \mathrm{prog}).$$

**Unfolding the left-hand side.** `isWitnessProgram s` returns nothing unless $4 \le |s| \le 42$ (it returns nothing when $|s| < 4$ or $42 < |s|$). Writing $b_0$ for the first byte of $s$ (as a natural number), it returns nothing unless $b_0 = 0$ or $\mathtt{0x51} \le b_0 \le \mathtt{0x60}$. It then requires that the second byte $s_1$, as a natural number, satisfy $s_1 + 2 = |s|$; if so it returns the pair $(\mathrm{decodeOpN}(b_0),\ s \text{ with the first two bytes dropped})$, otherwise nothing. Here $\mathrm{decodeOpN}(b) = 0$ if $b = 0$ and $b - \mathtt{0x50}$ (truncated subtraction) otherwise. Consequently the left side holds exactly when: $4 \le |s| \le 42$; $s_0 = 0$ and $v = 0$, or $s_0 = \mathtt{0x50} + v$ with $1 \le v \le 16$; $s_1 = |s| - 2$; and $\mathrm{prog}$ is the suffix of $s$ after its first two bytes (so $|\mathrm{prog}| = s_1 \in [2, 40]$).

**Unfolding the right-hand side.** `witnessBytes v prog` is the byte string whose first byte is $0$ if $v = 0$ and $(\mathtt{0x50} + v) \bmod 256$ otherwise, followed by `pushBytes prog`. For $|\mathrm{prog}| \le 40 < 76$, `pushBytes prog` is the single length byte $|\mathrm{prog}|$ followed by $\mathrm{prog}$. So, under the three bounds on the right, $s$ must be the $(|\mathrm{prog}| + 2)$-byte string: the version byte ($0$, or $\mathtt{0x51}$ through $\mathtt{0x60}$), the length byte $|\mathrm{prog}| \in [2, 40]$, then $\mathrm{prog}$.

**Logical content.** For every $s$, $v$, $\mathrm{prog}$: the parser recognizes $s$ as a witness program with exactly this version and this program if and only if $v$ is at most $16$, the program has between $2$ and $40$ bytes inclusive, and $s$ is literally the encoding `witnessBytes v prog`. Note that the right side uses $v \le 16$ with no lower bound (so $v = 0$ is included) and that the bounds $2 \le |\mathrm{prog}|$ and $|\mathrm{prog}| \le 40$ are both non-strict.

**What is not said.** Nothing is claimed about $v > 16$ except implicitly through the biconditional (for such $v$ the left side must be false, since the right side is); nothing is claimed about what `isWitnessProgram` returns on strings that are not witness programs beyond "not `some (v, prog)`"; nothing about evaluation, about `verifyWitnessProgram`, about any flag, or about which versions are "known". The theorem does not say that the version byte of `witnessBytes v prog` is in range for $v > 16$ (it is not, and that is consistent with the statement).
