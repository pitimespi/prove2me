# Read-back: `BitcoinTapSoundness.tagged_collision`

**Statement.** For every pair of strings $t, t'$ (arbitrary Unicode strings, possibly empty, possibly equal) and every pair of byte strings $m, m'$ (finite sequences of 8-bit values, of any lengths, possibly empty), if

$$
\mathrm{Tagged}_{t}(m) \;=\; \mathrm{Tagged}_{t'}(m')
$$

then at least one of the following holds:

1. $\mathrm{SHA256}(\mathrm{utf8}(t)) = \mathrm{SHA256}(\mathrm{utf8}(t'))$ **and** $m = m'$ (equality of byte strings, so in particular $|m| = |m'|$); or
2. $\mathsf{Sha256Collision}$ holds, i.e. there exist two byte strings $x \neq y$ (of any lengths, not necessarily the same length, and unrelated to $t, t', m, m'$) with $\mathrm{SHA256}(x) = \mathrm{SHA256}(y)$.

The first disjunct does **not** require $t = t'$; it only requires that the digests of their UTF-8 encodings agree.

**Unfolded notions.**

- $\mathrm{utf8}(t)$ is the list of bytes of the UTF-8 encoding of the string $t$.
- $\mathrm{SHA256}$ is the bundle's own executable implementation of SHA-256 (Merkle–Damgård padding with $0x80$, zero bytes, and the 64-bit big-endian bit length; 64 compression rounds with the standard constants; a 32-byte big-endian digest). It is a total function defined on every finite byte string, not an abstract or axiomatized hash.
- The tagged hash is
$$
\mathrm{Tagged}_{t}(m) \;:=\; \mathrm{SHA256}\bigl(\mathrm{SHA256}(\mathrm{utf8}(t)) \,\|\, \mathrm{SHA256}(\mathrm{utf8}(t)) \,\|\, m\bigr),
$$
  where $\|$ is concatenation of byte strings. Because every digest is 32 bytes long, the input to the outer $\mathrm{SHA256}$ always begins with a 64-byte prefix followed by $m$.
- $\mathsf{Sha256Collision}$ is a closed proposition (it has no parameters and does not depend on $t, t', m, m'$):
$$
\exists\, x, y \in \mathsf{Bytes}.\; x \neq y \;\wedge\; \mathrm{SHA256}(x) = \mathrm{SHA256}(y).
$$
  Since $\mathrm{SHA256}$ here is a fixed total function from the infinite set of byte strings to the finite set of 32-byte strings, the truth value of this proposition is a fixed mathematical fact (by counting, such a pair $x \neq y$ exists); it is not a hypothesis, assumption, or axiom of the theorem.

**Edge cases made explicit.** No hypothesis constrains the lengths of $m, m'$ or the contents of $t, t'$. If $t = t'$ and $m = m'$ the hypothesis holds trivially and the first disjunct holds. The theorem does not assert anything about $t$ versus $t'$ as strings, only about the SHA-256 digests of their UTF-8 encodings.
