We prove the leaf-level form of CVE-2012-2459: for a non-empty prefix $\ell$ of even length and a hash $a$,
$$\mathrm{root}(\ell \mathbin{+\!\!+} [a]) = \mathrm{root}(\ell \mathbin{+\!\!+} [a, a]) \qquad\text{and}\qquad \mathrm{mutated}(\ell \mathbin{+\!\!+} [a, a]) = \mathtt{true}.$$

**Idea.** Both lists have length greater than one, so each runs at least one level. By `BitcoinMerkle.pairUp_append_even`, the first level of $\ell \mathbin{+\!\!+} [a]$ is $\mathrm{pairUp}(\ell) \mathbin{+\!\!+} [c(a, a)]$ — the odd trailing $a$ is paired with itself — and the first level of $\ell \mathbin{+\!\!+} [a, a]$ is $\mathrm{pairUp}(\ell) \mathbin{+\!\!+} [c(a, a)]$ as well. From there the two computations coincide.

**Step 1 (roots).** After one level both runs continue on the same list, with flags that may differ; by `BitcoinMerkle.rootLoop_fst` the roots agree.

**Step 2 (detection).** By `BitcoinMerkle.hasEqualPair_append_even`, the test on $\ell \mathbin{+\!\!+} [a, a]$ includes the aligned pair $(a, a)$, so the flag after the first level is $\mathtt{true}$, and by `BitcoinMerkle.rootLoop_sticky` it is returned $\mathtt{true}$.

Non-emptiness of $\ell$ is used to guarantee $|\ell \mathbin{+\!\!+} [a]| > 1$; for $\ell = [\,]$ the list $[a]$ is returned unprocessed while $[a, a]$ hashes to $c(a, a)$.
