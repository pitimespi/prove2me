# Read-back: `BitcoinBlock.futureTime_iff`

## Binders

- $S$ : a chain state $\langle\mathit{headers}, \mathit{utxo}\rangle$.
- $b$ : a serialized block (header, transaction list).
- $\mathit{now} \in \mathbb{Z}$.

There are no hypotheses.

## Conclusion

$$\mathrm{validate}(S,b,\mathit{now}) = \mathrm{futureTime} \iff \mathrm{checkHeaderPow}(b.\mathrm{header}) = \mathrm{true} \wedge b.\mathrm{header.prevBlock} = \mathrm{tipHash}(S) \wedge \mathrm{bits}_{32}(b.\mathrm{header}) = \mathrm{requiredBits}(S) \wedge \mathrm{mtp}(S) < b.\mathrm{header.time} \wedge \mathit{now} + 7200 < b.\mathrm{header.time},$$
with times compared as integers and $7200$ = `MAX_FUTURE_BLOCK_TIME` $= 2\cdot60\cdot60$.

### Left side, unfolded

$\mathrm{validate}(S,b,\mathit{now})$ first computes $\mathrm{acceptHeader}(S, b.\mathrm{header}, \mathit{now})$; if that outcome is accept it proceeds to $\mathrm{checkBlock}$, $\mathrm{contextualCheckBlock}$ and $\mathrm{connectBlock}$, whose only possible outcomes are invalid or accept; if it is anything else, $\mathrm{validate}$ returns it unchanged. Hence $\mathrm{validate} = \mathrm{futureTime}$ exactly when $\mathrm{acceptHeader}(S,b.\mathrm{header},\mathit{now}) = \mathrm{futureTime}$, which by the ordered chain of tests happens exactly when:

1. $\mathrm{checkHeaderPow}(b.\mathrm{header})$ (little-endian value of the double-SHA256 of the serialized header $\le$ the compact target decoded from $b.\mathrm{header.bits} \bmod 2^{32}$, that compact word being non-negative, non-zero, non-overflowing and decoding to at most $2^{224}-1$) — otherwise invalid;
2. $b.\mathrm{header.prevBlock} = \mathrm{tipHash}(S)$ (hash of the last header, or of the genesis header if $S$ has no headers) — otherwise missingPrev;
3. $\mathrm{bits}_{32}(b.\mathrm{header}) = \mathrm{requiredBits}(S)$, where $\mathrm{bits}_{32}$ is the bits field modulo $2^{32}$ and $\mathrm{requiredBits}(S)$ is the tip's bits unless $\mathrm{tipHeight}+1 \equiv 0 \pmod{2016}$, in which case the retarget from the time of the header at index $\mathrm{tipHeight} - 2015$ (natural subtraction; genesis header default) — otherwise invalid;
4. $\neg\,(b.\mathrm{header.time} \le \mathrm{mtp}(S))$, i.e. $\mathrm{mtp}(S) < b.\mathrm{header.time}$, where $\mathrm{mtp}(S)$ is the sorted median (index $\lfloor n/2\rfloor$) of the at most $11$ most recent header times, default $0$ — otherwise invalid;
5. $\mathit{now} + 7200 < b.\mathrm{header.time}$ — then futureTime.

The version-floor test comes after and is not reached.

### Right side

Precisely the conjunction of the five conditions above, in the same terms.

## Edge cases silently included

Empty header list (tip defaults to genesis, $\mathrm{tipHeight} = 0$, median $0$); unbounded $\mathrm{time}$ and $\mathrm{bits}$ (bits reduced modulo $2^{32}$, time cast to $\mathbb{Z}$ unreduced); the transaction list of $b$ is irrelevant on both sides; the version field is irrelevant on both sides.
