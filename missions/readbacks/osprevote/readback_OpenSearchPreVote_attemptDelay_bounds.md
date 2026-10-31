# Read-back: `OpenSearchPreVote.attemptDelay_bounds`

## Notions used

**Scheduler settings.** A settings value $s$ is four natural numbers: $s.\mathrm{initialTimeout}$, $s.\mathrm{backoffTime}$, $s.\mathrm{maxTimeout}$ and $s.\mathrm{duration}$. The docstring says these are milliseconds. $\mathrm{Valid}(s)$ is the conjunction:
- $1 \le \mathrm{initialTimeout} \le 10000$;
- $1 \le \mathrm{backoffTime} \le 60000$;
- $200 \le \mathrm{maxTimeout} \le 300000$;
- $\mathrm{initialTimeout} \le \mathrm{maxTimeout}$;
- $1 \le \mathrm{duration} \le 300000$.

**Delay bound and delay.**
- $\mathrm{maxDelay}(s, k) = \min(s.\mathrm{maxTimeout},\ s.\mathrm{initialTimeout} + k\cdot s.\mathrm{backoffTime})$, in natural-number arithmetic.
- $\mathrm{nonNegative}(x)$ is $0$ if $x = -2^{63}$ and $|x|$ otherwise, for any integer $x$.
- $\mathrm{toPositiveLongAtMost}(x, u) = (\mathrm{nonNegative}(x) \bmod u) + 1$, with natural-number $\bmod$; when $u = 0$ the $\bmod$ returns its dividend.
- $\mathrm{attemptDelay}(s, k, x, g) = \mathrm{toPositiveLongAtMost}(x, \mathrm{maxDelay}(s, k)) + g$.

## 1. Declaration

**Binders and hypothesis.**
- $s$: scheduler settings;
- $hs$: $\mathrm{Valid}(s)$;
- $k \in \mathbb{N}$: the attempt index;
- $r \in \mathbb{Z}$: the random number;
- $g \in \mathbb{N}$: the grace period.

**Conclusion.**
$$1 \le \mathrm{maxDelay}(s, k) \;\wedge\; g + 1 \le \mathrm{attemptDelay}(s, k, r, g) \;\wedge\; \mathrm{attemptDelay}(s, k, r, g) \le g + \mathrm{maxDelay}(s, k).$$

Unfolded, with $M = \min(s.\mathrm{maxTimeout}, s.\mathrm{initialTimeout} + k\cdot s.\mathrm{backoffTime})$:
- $M \ge 1$;
- $g + 1 \le (\mathrm{nonNegative}(r) \bmod M) + 1 + g \le g + M$.

## 2. What is not constrained

- **The random number.** $r$ is any integer, including integers outside Java's long range. There, $\mathrm{nonNegative}$ is just the absolute value.
- **The grace period.** $g$ is any natural number. It is not tied to $0$ or to $s.\mathrm{duration}$, although the definition's docstring says those are the values Java uses.
- **The attempt index.** $k$ is any natural number.
- **Which parts of $\mathrm{Valid}$ matter.** As far as I can see, only $1 \le \mathrm{initialTimeout}$ and $1 \le \mathrm{maxTimeout}$ (from $200 \le \mathrm{maxTimeout}$) are needed. Together they give $M \ge 1$, and the delay bounds follow from $M \ge 1$. The other bounds of $\mathrm{Valid}$, and $s.\mathrm{duration}$, play no role.
- **Why the hypothesis matters.** Without $\mathrm{Valid}$, $M$ can be $0$, for example with initialTimeout $0$ and backoffTime $0$. Then the first conjunct fails, and $\mathrm{toPositiveLongAtMost}$ degenerates to $\mathrm{nonNegative}(r) + 1$.
- **What is not stated.** Nothing is said about the distribution of the delay, about which values in $[g+1, g+M]$ are attained, or about the relation between successive attempts.
- **Vacuity.** None. $\mathrm{Valid}$ is satisfiable, for example by the defaults $\langle 100, 100, 10000, 500\rangle$.

## 3. Plain-language summary

For valid scheduler settings, the delay bound of every attempt is at least $1$. The delay of every attempt lies between $g+1$ and $g$ plus that bound, whatever the random number and whatever the grace period $g$.
