# Read-back: `BitcoinTapSoundness.branch_eq`

**Statement.** For all byte strings $a, b, c, d$ (finite sequences of 8-bit values), under the four hypotheses

$$
|a| = 32,\qquad |b| = 32,\qquad |c| = 32,\qquad |d| = 32,
$$

if

$$
\mathrm{BranchHash}(a, b) \;=\; \mathrm{BranchHash}(c, d),
$$

then at least one of the following holds:

1. $a = c$ and $b = d$; or
2. $a = d$ and $b = c$; or
3. $\mathsf{Sha256Collision}$: there exist two byte strings $x \neq y$ (of any lengths, unrelated to $a, b, c, d$) with $\mathrm{SHA256}(x) = \mathrm{SHA256}(y)$.

(The parenthesization in the code is $\bigl((1) \vee (2)\bigr) \vee (3)$, which is logically the same three-way disjunction.)

**Unfolded notions.**

- $\mathrm{SHA256}$ is the bundle's own executable implementation of SHA-256 (a total function from all finite byte strings to 32-byte strings).
- $\mathrm{utf8}(\cdot)$ is UTF-8 encoding of a string; the tagged hash with tag $\tau$ is
$$
\mathrm{Tagged}_{\tau}(m) := \mathrm{SHA256}\bigl(\mathrm{SHA256}(\mathrm{utf8}(\tau)) \| \mathrm{SHA256}(\mathrm{utf8}(\tau)) \| m\bigr).
$$
- Lexicographic order $\prec$ on byte strings: compare position by position by numeric byte value; at the first differing position the smaller byte wins; if one string is a proper prefix of the other, the shorter one is smaller; a string is never $\prec$ itself.
- The branch hash is
$$
\mathrm{BranchHash}(u, v) := \begin{cases}
\mathrm{Tagged}_{\text{``TapBranch''}}(u \| v) & \text{if } u \prec v,\\
\mathrm{Tagged}_{\text{``TapBranch''}}(v \| u) & \text{otherwise (including } u = v\text{)}.
\end{cases}
$$
  As a consequence of this definition, $\mathrm{BranchHash}(u,v) = \mathrm{BranchHash}(v,u)$ for all $u, v$.
- $\mathsf{Sha256Collision}$ is the closed proposition $\exists\, x, y \in \mathsf{Bytes}.\; x \neq y \wedge \mathrm{SHA256}(x) = \mathrm{SHA256}(y)$. It has no parameters, so it is the same proposition in every instance of the theorem; since it concerns a fixed total function from infinitely many inputs to finitely many 32-byte outputs, its truth value is a fixed mathematical fact (such a pair exists by counting), not an assumption.

**Edge cases made explicit.** All four inputs are required to be exactly 32 bytes long, so the two 64-byte strings fed to the tagged hash are $\min_\prec(a,b)\|\max_\prec(a,b)$ and $\min_\prec(c,d)\|\max_\prec(c,d)$. The case $a = b$ (and/or $c = d$) is included; then disjuncts (1) and (2) coincide. Nothing is asserted when any of the length hypotheses fails.
