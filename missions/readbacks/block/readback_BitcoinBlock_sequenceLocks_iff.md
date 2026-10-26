# Read-back: `BitcoinBlock.sequenceLocks_iff`

## Binders

- $u$ : a ledger (association list from outpoints to coins $\langle\mathrm{out}, \mathrm{height}, \mathrm{isCoinbase}\rangle$).
- $\mathit{height} \in \mathbb{N}$.
- $\mathit{mtp} : \mathbb{N} \to \mathbb{N}$ : an arbitrary function (median time past by height).
- $\mathit{ltf} \in \mathbb{N}$ : the lock-time flags word.
- $tx$ : a serialized transaction (version $\in\mathbb{N}$, inputs with sequence $\in \mathbb{N}$ and prevout, outputs, lock time).

There are no hypotheses.

## Conclusion

$$\mathrm{sequenceLocksOk}(u, \mathit{height}, \mathit{mtp}, \mathit{ltf}, tx) = \mathrm{true} \iff \mathrm{satisfiesBIP68}\big(V, F, \langle\mathit{height}, \mathit{mtp}\rangle, I\big),$$
where $V = tx.\mathrm{version} \bmod 2^{32}$, $F = \mathit{ltf} \bmod 2^{32}$ (both as 32-bit words), and $I$ is the list, in input order, of pairs $\langle i.\mathrm{nSequence} \bmod 2^{32},\ \mathrm{accessCoin}(u, i.\mathrm{prevout}).\mathrm{height}\rangle$; $\mathrm{accessCoin}$ returns the coin of the first ledger entry with that key, or the dummy coin (height $0$, value $-1$) if there is none.

### Left side, unfolded

$\mathrm{sequenceLocksOk}$ is $\mathrm{sequenceLocks}(V, F, \langle\mathit{height},\mathit{mtp}\rangle, I)$ from the BIP68 core transcription: compute an accumulator $\langle \mathit{minHeight}, \mathit{minTime}, \mathit{heightsRev}\rangle$ starting at $\langle -1, -1, [\,]\rangle$ (integers):

- if $2 \le V$ and bit $0$ of $F$ is set ("enabled"), fold over $I$: for an input with sequence $s$ and coin height $c$: if bit $31$ of $s$ is set, nothing changes (height $0$ is recorded); else if bit $22$ of $s$ is set, $\mathit{minTime} := \max(\mathit{minTime},\ \mathit{mtp}(c - 1) + ((s \,\&\, 0xffff) \ll 9) - 1)$ (natural subtraction in $c-1$; the shift is inside 32 bits, so it equals $512\cdot(s \bmod 2^{16})$); else $\mathit{minHeight} := \max(\mathit{minHeight},\ c + (s \,\&\, 0xffff) - 1)$;
- if not enabled, the accumulator stays $\langle -1, -1, \cdot\rangle$.

Then the result is $\mathit{minHeight} < \mathit{height} \wedge \mathit{minTime} < \mathit{mtp}(\mathit{height} - 1)$ (integers; natural subtraction in $\mathit{height}-1$).

### Right side, unfolded

$\mathrm{satisfiesBIP68}(V,F,\mathit{ctx},I)$ is the proposition: $\neg\,\mathrm{specEnabled}(V,F)$, **or** every input $\langle s, c\rangle \in I$ is satisfied, where $\mathrm{specEnabled}(V,F)$ is $2 \le V \wedge F \bmod 2 = 1$, and an input is satisfied when $\lfloor s / 2^{31}\rfloor = 1$ (disabled), or — if $\lfloor s/2^{22}\rfloor$ is odd (time-based) — $\mathit{mtp}(c-1) + 512\cdot(s \bmod 2^{16}) \le \mathit{mtp}(\mathit{height}-1)$, otherwise $c + (s \bmod 2^{16}) \le \mathit{height}$ (all in $\mathbb{N}$ with natural subtraction in $c-1$ and $\mathit{height}-1$).

## Edge cases silently included

No admissibility or overflow hypotheses from the BIP68 model are assumed ($\mathit{height}$ may be $0$, coin heights may exceed $\mathit{height}$, $\mathit{mtp}$ may be anything); $\mathit{height} = 0$ makes $\mathit{height}-1 = 0$ and $\mathit{minHeight} < 0$ false when enabled with a non-disabled input; empty $tx.\mathrm{vin}$ (left: $-1 < \mathit{height}$ and $-1 < \mathit{mtp}(\cdot)$, true; right: vacuous); missing coins give height $0$ (so $c - 1 = 0$); $tx.\mathrm{version}$, $\mathit{ltf}$ and sequences are unbounded naturals truncated to 32 bits.
