# Read-back: `BitcoinTapSoundness.script_path_soundness`

**Statement.** Let $T$ be a tap tree (a finite binary tree in which every internal node has exactly two ordered children and every leaf carries a byte $v$ and a byte string $s$). Let $c$ ("control") be a byte string and $k$ a natural number (possibly $0$) with

$$
|c| = 33 + 32\,k .
$$

Let $v$ be a byte and $s$ a byte string (of any length). Assume

$$
\mathrm{Root}\bigl(c, \mathrm{LeafHash}(v, s)\bigr) \;=\; \mathrm{hash}(T).
$$

Then at least one of the following holds:

1. $\mathrm{LeafHash}(v, s)$ is an element of the list $\mathrm{leaves}(T)$; or
2. $\mathsf{Sha256Collision}$: there exist two byte strings $x \neq y$ (of any lengths, unrelated to the theorem's variables) with $\mathrm{SHA256}(x) = \mathrm{SHA256}(y)$.

**Unfolded notions.**

- $\mathrm{SHA256}$ is the bundle's own executable implementation of SHA-256 (a total function from all finite byte strings to 32-byte strings). $\mathrm{utf8}(\cdot)$ is UTF-8 encoding, and for a tag string $\tau$,
$$
\mathrm{Tagged}_{\tau}(m) := \mathrm{SHA256}\bigl(\mathrm{SHA256}(\mathrm{utf8}(\tau)) \| \mathrm{SHA256}(\mathrm{utf8}(\tau)) \| m\bigr).
$$
- $\mathrm{CS}(\ell)$ is the compact-size encoding of $\ell$ (one byte if $\ell < 253$; $0xfd$ + 2 little-endian bytes if $\ell \le 65535$; $0xfe$ + 4 bytes if $\ell \le 2^{32}-1$; $0xff$ + 8 bytes of $\ell \bmod 2^{64}$ otherwise).
- $\mathrm{LeafHash}(v, s) := \mathrm{Tagged}_{\text{``TapLeaf''}}([v] \| \mathrm{CS}(|s|) \| s)$, with $v$ used as given (no masking).
- $\prec$ is lexicographic order on byte strings (first differing byte decides; a proper prefix is smaller; no string is $\prec$ itself) and
$$
\mathrm{BranchHash}(a, b) := \mathrm{Tagged}_{\text{``TapBranch''}}\bigl(\text{if } a \prec b \text{ then } a\|b \text{ else } b\|a\bigr).
$$
- The path nodes of a control string $c$: let $m := \lfloor (|c| \mathbin{\dot-} 33) / 32 \rfloor$, where $\dot-$ is truncated natural-number subtraction (so $m = 0$ whenever $|c| \le 33$). Discard the first $33$ bytes of $c$ and cut what remains into $m$ consecutive blocks of $32$ bytes, $[n_1, \dots, n_m]$; any leftover bytes (fewer than 32) are ignored. Under the hypothesis $|c| = 33 + 32k$ there are exactly $m = k$ nodes, each exactly 32 bytes long, and nothing is left over. The first 33 bytes of $c$ play no role in this theorem.
- The Merkle root computed from $c$ and a starting hash $h$ is the left fold
$$
\mathrm{Root}(c, h) := \mathrm{BranchHash}\bigl(\cdots\mathrm{BranchHash}(\mathrm{BranchHash}(h, n_1), n_2)\cdots, n_m\bigr),
$$
  which equals $h$ itself when $m = 0$.
- $\mathrm{hash}(\mathrm{leaf}(v, s)) := \mathrm{LeafHash}(v, s)$ and $\mathrm{hash}(\mathrm{branch}(L, R)) := \mathrm{BranchHash}(\mathrm{hash}(L), \mathrm{hash}(R))$.
- $\mathrm{leaves}(\mathrm{leaf}(v, s)) := [\mathrm{LeafHash}(v, s)]$ and $\mathrm{leaves}(\mathrm{branch}(L, R)) := \mathrm{leaves}(L) \| \mathrm{leaves}(R)$: the list of leaf *hashes* of $T$, left to right, with repetitions. Membership in disjunct (1) is membership of a 32-byte string in this list; it does not say that the pair $(v, s)$ itself appears in $T$, only that its leaf hash equals the leaf hash of some leaf of $T$.
- $\mathsf{Sha256Collision}$ is the closed proposition $\exists\, x, y \in \mathsf{Bytes}.\; x \neq y \wedge \mathrm{SHA256}(x) = \mathrm{SHA256}(y)$, independent of all the theorem's variables; since it concerns a fixed total function from infinitely many inputs to finitely many 32-byte outputs, its truth value is a fixed mathematical fact (such a pair exists by counting), not an assumption.

**Edge cases made explicit.** $k = 0$ is allowed: then $c$ has exactly 33 bytes, there are no path nodes, and the hypothesis reads $\mathrm{LeafHash}(v, s) = \mathrm{hash}(T)$. No upper bound on $k$ (such as 128) is imposed. $s$ may be empty. The tree $T$ may be a single leaf. No relation between $c$'s first 33 bytes and anything else is assumed or concluded.
