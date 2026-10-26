We prove that the root component of the loop does not depend on the incoming flag: $\mathrm{rootLoop}_{c,z}(\ell, m).1 = \mathrm{rootLoop}_{c,z}(\ell, m').1$ for all flags $m, m'$.

**Idea.** The flag enters the recursion only as the accumulator $m \lor \mathrm{hasEqualPair}(\ell)$ passed to the next level and is never consulted when choosing hashes. The argument is an induction along the loop, i.e. well-founded induction on $|\ell|$, using $|\mathrm{pairUp}(\ell)| = \lceil |\ell|/2 \rceil < |\ell|$ when $|\ell| > 1$.

**Step 1 ($|\ell| > 1$).** Both runs step to the same list $\mathrm{pairUp}(\ell)$ with (possibly different) flags; by the induction hypothesis their roots agree.

**Step 2 ($|\ell| \le 1$).** Both runs return the head of $\ell$ (or $z$), independent of the flag.
