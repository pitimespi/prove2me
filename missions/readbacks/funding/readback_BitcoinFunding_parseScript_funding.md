# Read-back: `BitcoinFunding.parseScript_funding`

A **byte** is an 8-bit word; a **byte string** is a finite list of bytes.

## Statement

For all byte strings $k_1, k_2$ (named `pubkey1`, `pubkey2`; otherwise unconstrained in content), under the two hypotheses

$$
|k_1| \le 520 \qquad\text{and}\qquad |k_2| \le 520
$$

($520$ is the constant `MAX_SCRIPT_ELEMENT_SIZE`; $|\cdot|$ is the length in bytes), the theorem asserts the equality

$$
\mathrm{parseScript}\big(\mathrm{fundingBytes}(k_1,k_2)\big) \;=\; \mathrm{some}\big(\mathrm{fundingScript}(k_1,k_2)\big),
$$

an equality of values in $\mathrm{Option}(\mathsf{Script})$, where a script is a list of parsed instructions. In words: the byte-level parser, applied to the serialized funding script, does not fail and returns exactly the five-instruction parsed funding script. Both sides are unfolded below.

## The right-hand side: `fundingScript`

An *instruction* is either $\mathrm{push}(d)$, a data push carrying a byte string $d$, or $\mathrm{op}(c)$, a non-push opcode with byte $c$. By definition

$$
\mathrm{fundingScript}(k_1,k_2) = \big[\ \mathrm{numInstr}(2),\ \mathrm{push}(k_1),\ \mathrm{push}(k_2),\ \mathrm{numInstr}(2),\ \mathrm{op}(\mathtt{0xae})\ \big],
$$

where $\mathrm{numInstr}(n)$ is $\mathrm{op}(n+\mathtt{0x50})$ when $n=-1$ or $1\le n\le 16$, and otherwise the push of the script-number encoding of $n$. For $n=2$ this gives $\mathrm{op}(\mathtt{0x52})$. So the right-hand side is

$$
\mathrm{some}\ \big[\ \mathrm{op}(\mathtt{0x52}),\ \mathrm{push}(k_1),\ \mathrm{push}(k_2),\ \mathrm{op}(\mathtt{0x52}),\ \mathrm{op}(\mathtt{0xae})\ \big].
$$

Equality of scripts is entrywise equality of instruction lists; $\mathrm{push}(d)=\mathrm{push}(d')$ iff $d=d'$.

## The argument of the left-hand side: `fundingBytes`

$$
\mathrm{fundingBytes}(k_1,k_2) = \mathrm{numBytes}(2)\ \|\ \mathrm{pushBytes}(k_1)\ \|\ \mathrm{pushBytes}(k_2)\ \|\ \mathrm{numBytes}(2)\ \|\ [\mathtt{0xae}],
$$

with $\mathrm{numBytes}(n) = [\,n+\mathtt{0x50}\,]$ when $n=-1$ or $1\le n\le16$ (so $\mathrm{numBytes}(2)=[\mathtt{0x52}]$), otherwise $\mathrm{pushBytes}$ of the script-number encoding of $n$; and $\mathrm{pushBytes}(d)$, for $\ell=|d|$:

- $\ell<76$: the single byte $\ell$, then $d$;
- $76\le\ell\le255$: bytes $\mathtt{0x4c},\ \ell$, then $d$;
- $256\le\ell\le65535$: byte $\mathtt{0x4d}$, then $\ell$ as 2 little-endian bytes, then $d$;
- otherwise: byte $\mathtt{0x4e}$, then $\ell$ as 4 little-endian bytes (modulo $2^{32}$), then $d$.

Under the hypotheses, each of $|k_1|,|k_2|$ is at most $520$, so only the first three cases can arise for the two pushes (in particular $\mathrm{pushBytes}([\,])=[\mathtt{0x00}]$ when a key is empty).

## The parser: `parseScript`

$\mathrm{parseScript}(s)$ runs an auxiliary parser with a *fuel* equal to $|s|$:

- on the empty byte string, it returns $\mathrm{some}\,[\,]$ (regardless of fuel);
- on a non-empty string with fuel $0$, it returns $\mathrm{none}$;
- otherwise it calls $\mathrm{getOp}(s)$; if that is $\mathrm{none}$ the result is $\mathrm{none}$; if it is $\mathrm{some}(i, r)$ (one instruction and the remaining bytes), the remainder $r$ is parsed recursively with one unit less fuel, and $\mathrm{none}$ propagates, otherwise $i$ is prepended to the recursively parsed list.

$\mathrm{getOp}(s)$ (one instruction) is:

- $s=[\,]$: $\mathrm{none}$.
- $s = c :: r$ with $o$ the numeric value of $c$:
  - if $o \le \mathtt{0x4e}$ ($=78$), a push: the size and remainder are
    - $o<\mathtt{0x4c}$: size $o$, remainder $r$ (so the byte $\mathtt{0x00}$ is a push of the empty string);
    - $o=\mathtt{0x4c}$: size = the next byte, remainder after it; $\mathrm{none}$ if $r$ is empty;
    - $o=\mathtt{0x4d}$: size = little-endian value of the next 2 bytes; $\mathrm{none}$ if fewer than 2 remain;
    - $o=\mathtt{0x4e}$: size = little-endian value of the next 4 bytes; $\mathrm{none}$ if fewer than 4 remain;

    then $\mathrm{none}$ if fewer than *size* bytes remain, else $\mathrm{some}\big(\mathrm{push}(\text{the next } \mathit{size}\text{ bytes}),\ \text{the rest}\big)$;
  - if $o > \mathtt{0x4e}$: $\mathrm{some}(\mathrm{op}(c), r)$ — every byte from $\mathtt{0x4f}$ to $\mathtt{0xff}$, including $\mathtt{0x52}$ and $\mathtt{0xae}$, is returned as a non-push opcode with no further check.

## What is and is not constrained

- The only hypotheses are the two length bounds on $k_1$ and $k_2$; the theorem makes no claim when either key exceeds $520$ bytes.
- $k_1$ and $k_2$ are arbitrary byte strings within that bound (they may be empty, equal to each other, or of any content; no public-key format is required).
- The conclusion is a statement about parsing only: it asserts that parsing succeeds (is not $\mathrm{none}$) and that the resulting instruction list is exactly the five-entry list above, with the pushed data equal to $k_1$ and $k_2$ respectively.
