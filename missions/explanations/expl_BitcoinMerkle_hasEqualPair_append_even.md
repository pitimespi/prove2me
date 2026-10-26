We prove that the per-level mutation test distributes over a concatenation with an even-length prefix: for $|\ell|$ even, $\mathrm{hasEqualPair}(\ell \mathbin{+\!\!+} r) = \mathrm{hasEqualPair}(\ell) \lor \mathrm{hasEqualPair}(r)$.

By induction on $\ell$ two elements at a time, exactly as for pairing: the first aligned pair of the concatenation is the first pair of $\ell$, its test is disjoined with the test on the remainder, and associativity of disjunction regroups the terms. With aligned boundaries, every aligned pair of the concatenation lies within one of the two parts.
