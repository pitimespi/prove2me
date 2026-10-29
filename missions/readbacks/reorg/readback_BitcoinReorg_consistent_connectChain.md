# Read-back: `BitcoinReorg.consistent_connectChain`

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

**Validation.** $\mathrm{validate}(S, b, t)$, for a chain state $S$, a block $b$ and an integer clock reading $t$, is the transcribed Bitcoin Core validation path: the header tests (proof-of-work, parent equal to $\mathrm{tipHash}(S)$, bits equal to $\mathrm{requiredBits}(S)$, time above $\mathrm{mtp}(S)$, time at most $t + 7200$, version floors), the context-free block checks, the contextual block checks, and the ledger connection $\mathrm{connectBlock}(S, b)$ (genesis-hash shortcut; the BIP30 scan where required; per-transaction input, fee, sequence-lock, sigop and script checks with the ledger updated transaction by transaction; the coinbase bound). Its outcome is $\mathrm{accept}(\langle S.\mathrm{headers} \mathbin{+\!\!+} [b.\mathrm{header}], u\rangle, \mathit{undo})$ when everything passes, and otherwise $\mathrm{invalid}$, $\mathrm{futureTime}$ or $\mathrm{missingPrev}$. The ledger is consulted only through first-match lookup $\mathrm{getCoin}$ (with a dummy coin where absent).

**Reachability.** $\mathrm{Reachable}(S)$ is the least predicate such that the initial state $\langle [\text{genesisHeader}], [\,]\rangle$ is reachable, and whenever $\mathrm{Reachable}(S)$ and there exist a block $b$, an integer $t$, a state $S'$ and undo data $\mathit{undo}$ with $\mathrm{validate}(S, b, t) = \mathrm{accept}(S', \mathit{undo})$, then $\mathrm{Reachable}(S')$. The clock reading $t$ is unconstrained in each step and may differ from step to step.

**Connecting a chain** (the file's `connectChain`). For a chain state $S$ and a list $bs = [(b_1, t_1), \dots, (b_k, t_k)]$ of pairs of a block and an integer clock reading, $\mathrm{connectChain}(S, bs)$ returns "none" or "some $(T, [\mathit{undo}_1, \dots, \mathit{undo}_k])$", defined by: for $bs = [\,]$ it is "some $(S, [\,])$"; for $(b, t) :: \mathit{rest}$, if $\mathrm{validate}(S, b, t) = \mathrm{accept}(S', \mathit{undo})$ then it is "none" if $\mathrm{connectChain}(S', \mathit{rest})$ is "none" and "some $(T, \mathit{undo} :: \mathit{undos})$" if that is "some $(T, \mathit{undos})$"; if $\mathrm{validate}(S, b, t)$ is any other outcome ($\mathrm{invalid}$, $\mathrm{futureTime}$ or $\mathrm{missingPrev}$) it is "none". Thus a successful result has exactly one undo entry per block, in order, and $T$ is the state after all $k$ accepted blocks; for the empty list it is $S$ itself.

**Consistency.** $\mathrm{Consistent}(S)$ holds when there exists a chain state $S_0$ with $\mathrm{Reachable}(S_0)$ and $S \approx S_0$ (equal header lists and equivalent ledgers).


## Statement

**Binders and hypotheses.** A chain state $S$ with $\mathit{hS} : \mathrm{Consistent}(S)$, i.e. there is a reachable $S_0$ with $S.\mathrm{headers} = S_0.\mathrm{headers}$ and $S.\mathrm{utxo} \sim S_0.\mathrm{utxo}$; a list $cs$ of block–clock pairs; a chain state $U$; a list $\mathit{undos}$ of undo data; and
$$h : \mathrm{connectChain}(S, cs) = \text{some } (U, \mathit{undos}).$$

**Conclusion.** $\mathrm{Consistent}(U)$: there exists a reachable chain state $U_0$ with $U.\mathrm{headers} = U_0.\mathrm{headers}$ and $U.\mathrm{utxo} \sim U_0.\mathrm{utxo}$.

**Edge cases the statement includes.** For $cs = [\,]$, $U = S$ and the conclusion is $\mathit{hS}$. The hypothesis $h$ requires every block of $cs$ to be accepted in turn on $S$ itself (not on $S_0$); the conclusion does not relate $U_0$ to $S_0$ or to $cs$, nor mention $\mathit{undos}$. Nothing is asserted when $\mathrm{connectChain}(S, cs)$ is "none".
