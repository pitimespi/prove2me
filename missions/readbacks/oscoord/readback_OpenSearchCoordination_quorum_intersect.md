# Read-back: `OpenSearchCoordination.quorum_intersect`

## Notions used

**Voting configurations.** A voting configuration $c$ is a list $c.\mathrm{nodeIds}$ of natural numbers (node ids) together with a proof that the list is strictly increasing. So it has no duplicates and stands for a finite set $N_c$ of naturals.

**Quorum test.** For a list $L$ of naturals:
$$\mathrm{hasQuorum}(c, L) = \mathrm{true} \iff 2\cdot\big|[\,x \in c.\mathrm{nodeIds} \mid x \in L\,]\big| > |c.\mathrm{nodeIds}|,$$
that is, $2\,|N_c \cap L| > |N_c|$: strictly more than half of the configuration's ids occur in $L$. Duplicates in $L$ and entries of $L$ outside $N_c$ do not matter. For the empty configuration the test is always false.

## 1. Declaration

**Binders.**
- $c$: a voting configuration;
- $a, b$: lists of natural numbers (`List NodeId`).

**Hypotheses, in order.**
1. $\mathit{ha}$: $\mathrm{hasQuorum}(c, a) = \mathrm{true}$;
2. $\mathit{hb}$: $\mathrm{hasQuorum}(c, b) = \mathrm{true}$.

**Conclusion.**
$$\exists x,\quad x \in c.\mathrm{nodeIds} \;\wedge\; x \in a \;\wedge\; x \in b.$$
If $a$ and $b$ each contain a strict majority of $c$'s ids, then some id of $c$ lies in both.

## 2. What is not constrained

- $a$ and $b$ are arbitrary lists. They may contain ids outside $c$, repeat ids, and need not be related to each other.
- The conclusion asserts one common member. It says nothing about how many there are, nor that the common member is cluster-manager-eligible: no node objects are involved, only ids.
- If $c$ is empty, the hypotheses cannot both hold, since no list is a quorum of the empty configuration. The statement is then vacuous, which is the only consistent outcome, because the conclusion would be false.
- For non-empty $c$ the hypotheses are satisfiable, for example $c = [1]$ and $a = b = [1]$. The statement is not vacuous.
- The statement concerns a single configuration. It says nothing about two quorums of *different* configurations.

## 3. Plain-language summary

Two vote lists that are each a strict-majority quorum of the same voting configuration share at least one voter that belongs to the configuration. This is the usual quorum-intersection property, stated for one configuration and plain lists of ids.
