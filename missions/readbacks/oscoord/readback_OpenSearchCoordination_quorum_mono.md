# Read-back: `OpenSearchCoordination.quorum_mono`

## Notions used

**Voting configurations.** A voting configuration $c$ is a strictly increasing, hence duplicate-free, list $c.\mathrm{nodeIds}$ of natural numbers (node ids). It stands for a finite set $N_c$.

**Quorum test.** For a list $L$ of naturals:
$$\mathrm{hasQuorum}(c, L) = \mathrm{true} \iff 2\cdot\big|[\,x \in c.\mathrm{nodeIds} \mid x \in L\,]\big| > |c.\mathrm{nodeIds}|,$$
that is, $2\,|N_c \cap L| > |N_c|$, a strict majority of $c$. Membership is tested with `List.contains` on ℕ, which agrees with $\in$.

## 1. Declaration

**Binders.**
- $c$: a voting configuration;
- $a, b$: lists of natural numbers.

**Hypotheses, in order.**
1. $\mathit{hab}$: $\forall x,\ x \in a \to x \in b$. Every id occurring in $a$ occurs in $b$. This is inclusion of the underlying sets, not a sublist or multiset relation.
2. $\mathit{ha}$: $\mathrm{hasQuorum}(c, a) = \mathrm{true}$.

**Conclusion.** $\mathrm{hasQuorum}(c, b) = \mathrm{true}$.

## 2. What is not constrained

- $b$ may contain any extra ids, inside or outside $c$, in any order and with repetitions.
- No hypothesis is unsatisfiable. For example, $c = [1]$, $a = [1]$, $b = [1, 2]$ satisfies them.
- The statement is about a fixed configuration $c$. It says nothing about changing the configuration.

## 3. Plain-language summary

Enlarging a vote list never destroys a quorum: if every id of $a$ is also in $b$ and $a$ is a strict-majority quorum of $c$, then so is $b$.
