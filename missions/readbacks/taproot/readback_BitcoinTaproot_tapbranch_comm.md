# Read-back: `BitcoinTaproot.tapbranch_comm`

**Binders.** $a, b$ : byte strings (finite lists of 8-bit values).

**Hypotheses.** None.

**Conclusion.**

$$\mathrm{tapbranchHash}(a, b) = \mathrm{tapbranchHash}(b, a)$$

as an equality of byte strings, where, unfolded,

$$\mathrm{tapbranchHash}(x, y) = \mathrm{tagged}(\texttt{"TapBranch"},\; \text{if } x <_{\mathrm{lex}} y \text{ then } x \,\Vert\, y \text{ else } y \,\Vert\, x),$$

$\mathrm{tagged}(T, m) = \mathrm{SHA256}\big(\mathrm{SHA256}(T)\,\Vert\,\mathrm{SHA256}(T)\,\Vert\, m\big)$ with $T$ the UTF-8 bytes of the tag string, and $x <_{\mathrm{lex}} y$ is the file's byte-wise lexicographic "strictly less" test: two empty strings are not less; an empty string is less than a non-empty one; a non-empty string is not less than an empty one; otherwise compare the first bytes as naturals, and on a tie recurse on the tails. SHA256 here is the bundle's own definition of SHA-256 on byte lists.

**Edge cases the quantifiers include.** $a = b$ (both sides hash $a \,\Vert\, a$); $a$ or $b$ empty; $a$ a proper prefix of $b$ (then $a <_{\mathrm{lex}} b$); strings of arbitrary, unequal, non-32-byte lengths.
