# Read-back: `BitcoinBlock.acceptHeader_iff`

## Binders

- $S$ : a chain state, i.e. a pair $(\mathit{headers}, \mathit{utxo})$ where $\mathit{headers}$ is a list of serialized block headers (each with fields: version $\in \mathbb{Z}$, previous-block hash (a byte list), merkle root (a byte list), time $\in \mathbb{N}$, bits $\in \mathbb{N}$, nonce $\in \mathbb{N}$) and $\mathit{utxo}$ is a ledger (an association list from outpoints to coins). No hypothesis is placed on $S$: its header list may be empty, may not start with the genesis header, etc.
- $h$ : a serialized block header (same six fields as above; time and bits are unbounded natural numbers).
- $\mathit{now} \in \mathbb{Z}$ : the local clock.

There are no further hypotheses.

## Conclusion

The statement is an equivalence (iff):

$$\mathrm{acceptHeader}(S, h, \mathit{now}) = \mathrm{accept}(S, [\,]) \iff \mathrm{checkHeaderPow}(h) = \mathrm{true} \;\wedge\; h.\mathrm{prevBlock} = \mathrm{tipHash}(S) \;\wedge\; \mathrm{contextualCheck}\big(\langle h.\mathrm{version}, h.\mathrm{time}, \mathrm{bits}_{32}(h)\rangle,\ \mathrm{tipHeight}(S),\ \mathrm{timesTo}(S, \mathrm{tipHeight}(S)),\ \mathrm{requiredBits}(S),\ \mathit{now}\big) = \mathrm{true}.$$

### Left-hand side, unfolded

$\mathrm{acceptHeader}(S,h,\mathit{now})$ is a value of the four-constructor outcome type (accept with a state and undo list / invalid / futureTime / missingPrev), computed by the following ordered chain of tests:

1. if $\mathrm{checkHeaderPow}(h)$ is false, the result is **invalid**;
2. else if $h.\mathrm{prevBlock} \ne \mathrm{tipHash}(S)$, the result is **missingPrev**;
3. else if $\mathrm{bits}_{32}(h) \ne \mathrm{requiredBits}(S)$, the result is **invalid**;
4. else if $h.\mathrm{time} \le \mathrm{mtp}(S)$ (as integers), the result is **invalid**;
5. else if $\mathit{now} + 7200 < h.\mathrm{time}$, the result is **futureTime**;
6. else if $\mathrm{versionOutdated}(h.\mathrm{version}, \mathrm{tipHeight}(S))$, the result is **invalid**;
7. else the result is $\mathrm{accept}(S, [\,])$: the very same state $S$ and the empty undo list.

So the left side holds exactly when all six tests pass (constructor equality on the outcome type; the accepted state must be literally $S$ and the undo list literally empty, which is what step 7 produces).

Here:

- $\mathrm{bits}_{32}(h)$ is $h.\mathrm{bits}$ reduced modulo $2^{32}$ and viewed as a 32-bit word.
- $\mathrm{checkHeaderPow}(h)$: let $H$ be the little-endian numeric value of the 32-byte double-SHA256 of the serialized header; decode $\mathrm{bits}_{32}(h)$ as a compact target (mantissa $= $ low 23 bits, exponent $=$ top byte, shifted into 256 bits with truncation modulo $2^{256}$); the check is **false** if the compact word is "negative" (mantissa non-zero and bit $0x00800000$ set), the decoded target is $0$, the compact word "overflows", or the target exceeds $2^{224}-1$; otherwise it is $H \le \text{target}$.
- $\mathrm{tipHeight}(S) = |\mathit{headers}| - 1$ with natural-number subtraction (so $0$ when the header list is empty).
- $\mathrm{tip}(S)$ is the last header of $S$, or the genesis header if the list is empty; $\mathrm{tipHash}(S)$ is its double-SHA256 header hash.
- $\mathrm{timesTo}(S, k)$ is the list of the times (as integers) of the first $k+1$ headers of $S$, most recent first.
- $\mathrm{mtp}(S)$ is the median-time-past of the tip: take the first $11$ entries of $\mathrm{timesTo}(S, \mathrm{tipHeight}(S))$, sort them ascending, and take the element at index $\lfloor n/2 \rfloor$ ($n$ the window length), with default $0$ for an empty window.
- $\mathrm{requiredBits}(S)$: with $\mathit{first}$ the header at index $\mathrm{tipHeight}(S) - 2015$ (natural subtraction, so index $0$ when the tip height is below $2015$; the genesis header if that index is out of range), it is $\mathrm{nextWorkRequired}(\mathrm{tipHeight}(S), \mathrm{bits}_{32}(\mathrm{tip}), \mathrm{tip.time}, \mathit{first}.\mathrm{time})$: the tip's bits unchanged unless $\mathrm{tipHeight}+1$ is a multiple of $2016$, in which case the retargeted compact word computed from the clamped timespan $\mathrm{tip.time} - \mathit{first}.\mathrm{time}$.
- $\mathrm{versionOutdated}(v, p)$ holds when $v<2$ and $227931 \le p+1$, or $v<3$ and $363725 \le p+1$, or $v<4$ and $388381 \le p+1$.

### Right-hand side, unfolded

The right side is a conjunction of three Boolean equalities:

1. $\mathrm{checkHeaderPow}(h) = \mathrm{true}$ (as above);
2. $h.\mathrm{prevBlock} = \mathrm{tipHash}(S)$ (byte-list equality);
3. $\mathrm{contextualCheck}$ from the header-rules development, applied to the reduced header $\langle h.\mathrm{version},\ h.\mathrm{time} \text{ cast to } \mathbb{Z},\ \mathrm{bits}_{32}(h)\rangle$, the previous height $\mathrm{tipHeight}(S)$, the previous times $\mathrm{timesTo}(S,\mathrm{tipHeight}(S))$, the required word $\mathrm{requiredBits}(S)$ and the clock $\mathit{now}$. That function is the conjunction
   $$\mathrm{bits}_{32}(h) = \mathrm{requiredBits}(S) \;\wedge\; \mathrm{medianTimePast}(\mathrm{timesTo}(S,\mathrm{tipHeight}(S))) < h.\mathrm{time} \;\wedge\; h.\mathrm{time} \le \mathit{now} + 7200 \;\wedge\; \neg\,\mathrm{versionOutdated}(h.\mathrm{version}, \mathrm{tipHeight}(S)),$$
   where $\mathrm{medianTimePast}$ is the same window-of-11 sorted median described above and $7200$ is the header development's own constant $2\cdot 60\cdot 60$ (a separate definition from the block development's constant of the same value).

## Edge cases silently included

Empty header list ($\mathrm{tipHeight}=0$, tip defaults to the genesis header, median defaults over a window of length $0$ gives $0$); $h.\mathrm{bits}$ and $h.\mathrm{time}$ are unbounded naturals reduced/cast when used; $\mathrm{tipHeight}-2015$ clamps at $0$; the header at index $\mathrm{tipHeight}-2015$ defaults to the genesis header when out of range; no well-formedness of $S$ or $h$ is assumed; the "futureTime" and "missingPrev" outcomes are both just "not accept" on the left.
