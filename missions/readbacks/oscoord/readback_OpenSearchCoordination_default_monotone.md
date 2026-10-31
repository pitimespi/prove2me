# Read-back: `OpenSearchCoordination.default_monotone`

## Notions used

**Election strategies.** An election strategy $es$ is a structure holding an arbitrary Boolean function
$$f_{es} : \mathrm{DiscoveryNode} \to \mathbb{N} \to \mathbb{N} \to \mathbb{Z} \to \mathrm{VotingConfiguration} \to \mathrm{VotingConfiguration} \to \mathrm{VoteCollection} \to \mathrm{Bool}$$
(field `satisfiesAdditionalQuorumConstraints`). Its arguments are, in order: the local node, the current term, the accepted term, the accepted version, the committed configuration, the accepted configuration and the votes. A vote collection $v$ is a list $v.\mathrm{nodes}$ of natural numbers.

**The default strategy.** $\mathrm{DEFAULT\_INSTANCE}$ is the strategy whose function is constantly $\mathrm{true}$.

**Monotonicity.** $\mathrm{Monotone}(es)$ is the proposition
$$\forall n\ t\ t'\ a\ c\ c'\ v\ w,\quad (\forall x,\ x \in v.\mathrm{nodes} \to x \in w.\mathrm{nodes}) \to f_{es}(n,t,t',a,c,c',v) = \mathrm{true} \to f_{es}(n,t,t',a,c,c',w) = \mathrm{true}.$$
In words: with all other arguments fixed, enlarging the set of voters never turns a satisfied constraint into an unsatisfied one.

## 1. Declaration

**Binders and hypotheses.** None.

**Conclusion.** $\mathrm{Monotone}(\mathrm{DEFAULT\_INSTANCE})$. Unfolded, this reads: for all $n, t, t', a, c, c', v, w$, if every id of $v$ is in $w$ and $\mathrm{true} = \mathrm{true}$, then $\mathrm{true} = \mathrm{true}$.

## 2. What is not constrained

- The statement is **trivial**. The default function ignores all its arguments and returns $\mathrm{true}$, so the inner conclusion holds whatever the premises are. The statement is not vacuous, since its premises can hold, but it has no content beyond the definition of $\mathrm{DEFAULT\_INSTANCE}$.
- It says nothing about any other strategy.

## 3. Plain-language summary

The default election strategy, which imposes no additional constraint, is monotone in the votes. This holds trivially, because its extra constraint is always satisfied. As a result, the default strategy satisfies the `Monotone` hypothesis of `handleJoin_stays_won` and `javaInvariant_preserved`.
