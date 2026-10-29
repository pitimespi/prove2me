# Read-back: `BitcoinReorg.connectChain_equiv`

## Notions used

**Ledgers and coin lookup.** A *ledger* $u$ is a finite list of pairs $(p, c)$, where $p$ is an *outpoint* (a byte string $p.\mathrm{hash}$ and a natural number $p.n$) and $c$ is a *coin* (an output $c.\mathrm{out}$ consisting of an integer value $c.\mathrm{out}.\mathrm{nValue}$ and a byte-string script $c.\mathrm{out}.\mathrm{scriptPubKey}$; a natural-number creation height $c.\mathrm{height}$; and a Boolean coinbase flag $c.\mathrm{isCoinbase}$). The lookup $\mathrm{getCoin}(u, p)$ scans $u$ from the front and returns the coin of the *first* pair whose outpoint equals $p$ (as a value "some $c$"), or "none" if no pair has outpoint $p$; any later pair with the same outpoint is shadowed and never consulted. Two ledgers are *equivalent*, written $u \sim v$, when
$$\forall p,\quad \mathrm{getCoin}(u, p) = \mathrm{getCoin}(v, p),$$
the quantifier ranging over every outpoint (every byte string and every natural number). Equivalence says nothing about the order of the lists, about duplicate or shadowed entries, or about list length.

**Chain states.** A *chain state* $S$ is a pair of a list of headers $S.\mathrm{headers}$ and a ledger $S.\mathrm{utxo}$. A header has an integer version, byte strings $\mathrm{prevBlock}$ and $\mathrm{merkleRoot}$, and natural numbers $\mathrm{time}$, $\mathrm{bits}$, $\mathrm{nonce}$; $\mathrm{headerHash}(h)$ is the double SHA-256 of its 80-byte serialization. A block $b$ is a header $b.\mathrm{header}$ and a list of transactions $b.\mathrm{vtx}$. Derived quantities of a state $S$ with $n = |S.\mathrm{headers}|$:

- $\mathrm{tipHeight}(S) = n - 1$ with *truncated* natural-number subtraction, so it is $0$ both when $n = 1$ and when $n = 0$;
- $\mathrm{nextHeight}(S) = n$;
- $\mathrm{tip}(S)$ is the last header of the list, or the fixed genesis header if the list is empty; $\mathrm{tipHash}(S) = \mathrm{headerHash}(\mathrm{tip}(S))$;
- $\mathrm{mtp}(S)$ ("median time past"): take the times of the headers at indices $0, \dots, \mathrm{tipHeight}(S)$, list them most recent first, keep the first $11$, sort ascending, and take the element at index $\lfloor \ell / 2 \rfloor$ where $\ell$ is the length of that window ($0$ if the window is empty); $\mathrm{mtpNat}(S, h)$ is the same computation for the headers at indices $0..h$, converted to a natural number (negative values become $0$);
- $\mathrm{requiredBits}(S)$: let $f$ be the header at index $\mathrm{tipHeight}(S) - 2015$ (truncated subtraction; the genesis header if the index is out of range); if $(\mathrm{tipHeight}(S) + 1) \bmod 2016 \neq 0$ the result is the tip's $\mathrm{bits}$ field, otherwise it is the retargeted compact difficulty computed by the transcribed difficulty-adjustment routine from the tip's bits and time and $f$'s time.

The *initial state* is $\langle [\text{genesisHeader}],\ [\,]\rangle$: the single fixed genesis header and the empty ledger. $\mathrm{genesisHash}$ is a fixed 32-byte constant.

**State equivalence.** Two chain states are *equivalent*, written $S \approx T$ (the file's `StateEquiv`), when
$$S.\mathrm{headers} = T.\mathrm{headers} \quad\text{and}\quad S.\mathrm{utxo} \sim T.\mathrm{utxo},$$
i.e. the header lists are literally equal (same length, same headers in the same order) and the ledgers are equivalent in the sense above.

**Validation.** $\mathrm{validate}(S, b, t)$, for a chain state $S$, a block $b$ and an integer clock reading $t$, is the transcribed Bitcoin Core validation path: the header tests (proof-of-work, parent equal to $\mathrm{tipHash}(S)$, bits equal to $\mathrm{requiredBits}(S)$, time above $\mathrm{mtp}(S)$, time at most $t + 7200$, version floors), the context-free block checks, the contextual block checks, and the ledger connection $\mathrm{connectBlock}(S, b)$ (genesis-hash shortcut returning the ledger unchanged with empty undo data; the BIP30 scan where required; per-transaction input, fee, sequence-lock, sigop and script checks with the ledger updated by $\mathrm{updateCoins}$; the coinbase bound). Its outcome is $\mathrm{accept}(\langle S.\mathrm{headers} \mathbin{+\!\!+} [b.\mathrm{header}], u\rangle, \mathit{undo})$ when everything passes with connected ledger $u$ and recorded undo data $\mathit{undo}$, and otherwise $\mathrm{invalid}$, $\mathrm{futureTime}$ or $\mathrm{missingPrev}$. All header and block tests read only the header list and $b$; only $\mathrm{connectBlock}$ reads the ledger, and it does so through $\mathrm{getCoin}$ (first-match lookup) and the dummy-coin fallback.

**Connecting a chain** (the file's `connectChain`). For a chain state $S$ and a list $bs = [(b_1, t_1), \dots, (b_k, t_k)]$ of pairs of a block and an integer clock reading, $\mathrm{connectChain}(S, bs)$ returns "none" or "some $(T, [\mathit{undo}_1, \dots, \mathit{undo}_k])$", defined by: for $bs = [\,]$ it is "some $(S, [\,])$"; for $(b, t) :: \mathit{rest}$, if $\mathrm{validate}(S, b, t) = \mathrm{accept}(S', \mathit{undo})$ then it is "none" if $\mathrm{connectChain}(S', \mathit{rest})$ is "none" and "some $(T, \mathit{undo} :: \mathit{undos})$" if that is "some $(T, \mathit{undos})$"; if $\mathrm{validate}(S, b, t)$ is any other outcome ($\mathrm{invalid}$, $\mathrm{futureTime}$ or $\mathrm{missingPrev}$) it is "none". Thus a successful result has exactly one undo entry per block, in order, and $T$ is the state after all $k$ accepted blocks; for the empty list it is $S$ itself.


## Statement

**Binders and hypotheses.** A list $bs$ of block–clock pairs; then, universally, chain states $S$ and $T$ with the hypothesis $S \approx T$ (equal header lists, equivalent ledgers). No reachability or well-formedness is assumed.

**Conclusion.** A disjunction: either

1. $\mathrm{connectChain}(S, bs) = \text{none}$ and $\mathrm{connectChain}(T, bs) = \text{none}$; or
2. there exist chain states $U$, $V$ and a list $\mathit{undos}$ of undo data such that
$$\mathrm{connectChain}(S, bs) = \text{some } (U, \mathit{undos}),\qquad \mathrm{connectChain}(T, bs) = \text{some } (V, \mathit{undos}),\qquad U \approx V.$$

In alternative 2 the undo lists are literally the same list, and the final states have equal header lists and equivalent (not necessarily equal) ledgers.

**Edge cases the statement includes.** For $bs = [\,]$ alternative 2 holds with $U = S$, $V = T$, $\mathit{undos} = [\,]$ directly from the hypothesis. The statement does not say which alternative holds, only that one does; it also does not say at which block, if any, both runs fail.
