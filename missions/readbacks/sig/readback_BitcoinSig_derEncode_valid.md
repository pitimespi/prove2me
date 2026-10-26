# Read-back: `BitcoinSig.derEncode_valid`

**Binders and hypothesis.** Universally quantified over byte strings $r$ and $s$ and a byte $ht$, with three hypotheses:
- $hr$: `minimalInt` $r$, i.e. $r \neq [\,]$, the first byte of $r$ is $<$ `0x80`, and if $|r| > 1$ and the first byte of $r$ is $0$ then the second byte of $r$ is $\geq$ `0x80`;
- $hs$: `minimalInt` $s$, the same three conditions for $s$;
- $hlen$: $|r| + |s| \leq 66$.
Since both strings are non-empty, each has length between $1$ and $65$.

**Conclusion.**
$$\text{isValidSignatureEncoding}\ (\text{derEncode}\ r\ s\ ht) = \text{true}.$$

**Unfolding the encoding.** `derEncode` $r\,s\,ht$ is the byte string $[\texttt{0x30},\ (|r|+|s|+4) \bmod 256,\ \texttt{0x02},\ |r| \bmod 256] \,\|\, r \,\|\, [\texttt{0x02},\ |s| \bmod 256] \,\|\, s \,\|\, [ht]$, of total length $\ell = |r| + |s| + 7$, which under $hlen$ lies in $[9, 73]$. Under $hlen$ all the "mod 256" reductions are identities.

**Unfolding the check.** `isValidSignatureEncoding` on this string examines, in order (with byte $i$ meaning the $i$-th byte, $0$ if out of range): $\ell \geq 9$ (true); $\ell \leq 73$ (true by $hlen$); byte 0 is `0x30` (true); byte 1 equals $\ell - 3 = |r| + |s| + 4$ (true); $lenR$ := byte 3 $= |r|$, and $5 + lenR < \ell$ (true since $|s| \geq 1$); $lenS$ := byte $5 + |r|$, which is the byte right after $r$'s tag, i.e. $|s|$, and $lenR + lenS + 7 = \ell$ (true); byte 2 is `0x02` (true); $lenR \neq 0$ (true by $hr$); byte 4 — the first byte of $r$ — is $<$ `0x80` (true by $hr$); it is not the case that $|r| > 1$ and $r$'s first byte is $0$ and $r$'s second byte (byte 5) is $<$ `0x80` (true by $hr$); byte $|r| + 4$ — the tag after $r$ — is `0x02` (true); $lenS \neq 0$ (true by $hs$); byte $|r| + 6$ — the first byte of $s$ — is $<$ `0x80` (true by $hs$); not ($|s| > 1$ and $s$'s first byte is $0$ and $s$'s second byte is $<$ `0x80`) (true by $hs$). The final byte $ht$ is never inspected. Hence the check returns true.

**What is not said.** The statement does not say anything when $|r| + |s| > 66$ (then the encoded length exceeds 73 and the check would fail, but the theorem is silent). It does not say anything about non-minimal or empty $r$ or $s$. It does not say that the hash-type byte $ht$ is a "defined" hash type, nor that it is examined — the encoding check ignores it. It does not say that $r$ or $s$ read as integers are non-zero, below $n$, or low (the byte string $[0]$ is a valid `minimalInt`, and the string `0x7f` followed by 64 `0xff` bytes is too). It does not say that `parseDerLax` accepts the encoding, that `checkLowS` holds, or anything about `checkSignatureEncoding` with any flags (which additionally depends on `lowS` and `strictenc`). It does not state the converse decomposition; that is the separate completeness statement.
