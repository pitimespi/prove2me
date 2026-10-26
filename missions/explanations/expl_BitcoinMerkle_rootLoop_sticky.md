We prove that a set flag is returned set: $\mathrm{rootLoop}_{c,z}(\ell, \mathtt{true}).2 = \mathtt{true}$ for every list $\ell$.

By well-founded induction on $|\ell|$. If $|\ell| > 1$, the loop continues with flag $\mathtt{true} \lor \mathrm{hasEqualPair}(\ell) = \mathtt{true}$ on the shorter list $\mathrm{pairUp}(\ell)$, where the induction hypothesis applies. Otherwise the loop exits returning the flag $\mathtt{true}$ unchanged. The per-level tests are only ever disjoined into the flag, so a mutation detected at any level is reported at the end.
