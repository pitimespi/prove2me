# Read-back: `BitcoinReorg.connectChain_reachable`

## Notions used

**Chain states.** A *chain state* $S$ is a pair of a list of headers $S.\mathrm{headers}$ and a ledger $S.\mathrm{utxo}$. A header has an integer version, byte strings $\mathrm{prevBlock}$ and $\mathrm{merkleRoot}$, and natural numbers $\mathrm{time}$, $\mathrm{bits}$, $\mathrm{nonce}$; $\mathrm{headerHash}(h)$ is the double SHA-256 of its 80-byte serialization. A block $b$ is a header $b.\mathrm{header}$ and a list of transactions $b.\mathrm{vtx}$. Derived quantities of a state $S$ with $n = |S.\mathrm{headers}|$:

- $\mathrm{tipHeight}(S) = n - 1$ with *truncated* natural-number subtraction, so it is $0$ both when $n = 1$ and when $n = 0$;
- $\mathrm{nextHeight}(S) = n$;
- $\mathrm{tip}(S)$ is the last header of the list, or the fixed genesis header if the list is empty; $\mathrm{tipHash}(S) = \mathrm{headerHash}(\mathrm{tip}(S))$;
- $\mathrm{mtp}(S)$ ("median time past"): take the times of the headers at indices $0, \dots, \mathrm{tipHeight}(S)$, list them most recent first, keep the first $11$, sort ascending, and take the element at index $\lfloor \ell / 2 \rfloor$ where $\ell$ is the length of that window ($0$ if the window is empty); $\mathrm{mtpNat}(S, h)$ is the same computation for the headers at indices $0..h$, converted to a natural number (negative values become $0$);
- $\mathrm{requiredBits}(S)$: let $f$ be the header at index $\mathrm{tipHeight}(S) - 2015$ (truncated subtraction; the genesis header if the index is out of range); if $(\mathrm{tipHeight}(S) + 1) \bmod 2016 \neq 0$ the result is the tip's $\mathrm{bits}$ field, otherwise it is the retargeted compact difficulty computed by the transcribed difficulty-adjustment routine from the tip's bits and time and $f$'s time.

The *initial state* is $\langle [\text{genesisHeader}],\ [\,]\rangle$: the single fixed genesis header and the empty ledger. $\mathrm{genesisHash}$ is a fixed 32-byte constant.

**Validation.** $\mathrm{validate}(S, b, t)$, for a chain state $S$, a block $b$ and an integer clock reading $t$, is the transcribed Bitcoin Core validation path (proof-of-work, parent-is-tip, required difficulty, median-time-past floor, clock ceiling $t + 7200$, version floors, the context-free block checks, the contextual block checks, and the ledger connection with BIP30, input checks, fee and sigop limits, sequence locks, script verification and the coinbase bound). Its outcome is one of $\mathrm{accept}(S', \mathit{undo})$ — with $S' = \langle S.\mathrm{headers} \mathbin{+\!\!+} [b.\mathrm{header}],\ u\rangle$ for the connected ledger $u$ and $\mathit{undo}$ the recorded undo data — or $\mathrm{invalid}$, $\mathrm{futureTime}$, $\mathrm{missingPrev}$. The present statement depends only on which outcomes are acceptances, not on the internals.

**Reachability.** $\mathrm{Reachable}(S)$ is the least predicate such that the initial state $\langle [\text{genesisHeader}], [\,]\rangle$ is reachable, and whenever $\mathrm{Reachable}(S)$ and there exist a block $b$, an integer $t$, a state $S'$ and undo data $\mathit{undo}$ with $\mathrm{validate}(S, b, t) = \mathrm{accept}(S', \mathit{undo})$, then $\mathrm{Reachable}(S')$. The clock reading $t$ is unconstrained in each step and may differ from step to step.

**Connecting a chain** (the file's `connectChain`). For a chain state $S$ and a list $bs = [(b_1, t_1), \dots, (b_k, t_k)]$ of pairs of a block and an integer clock reading, $\mathrm{connectChain}(S, bs)$ returns "none" or "some $(T, [\mathit{undo}_1, \dots, \mathit{undo}_k])$", defined by: for $bs = [\,]$ it is "some $(S, [\,])$"; for $(b, t) :: \mathit{rest}$, if $\mathrm{validate}(S, b, t) = \mathrm{accept}(S', \mathit{undo})$ then it is "none" if $\mathrm{connectChain}(S', \mathit{rest})$ is "none" and "some $(T, \mathit{undo} :: \mathit{undos})$" if that is "some $(T, \mathit{undos})$"; if $\mathrm{validate}(S, b, t)$ is any other outcome ($\mathrm{invalid}$, $\mathrm{futureTime}$ or $\mathrm{missingPrev}$) it is "none". Thus a successful result has exactly one undo entry per block, in order, and $T$ is the state after all $k$ accepted blocks; for the empty list it is $S$ itself.


## Statement

**Binders and hypotheses.** A chain state $S$ with $\mathit{hR} : \mathrm{Reachable}(S)$; then, universally, a list $bs$ of block–clock pairs, a chain state $T$, a list $\mathit{undos}$ of undo data, and the hypothesis
$$\mathrm{connectChain}(S, bs) = \text{some } (T, \mathit{undos}).$$

**Conclusion.** $\mathrm{Reachable}(T)$: the final state obtained by validating and connecting every block of $bs$ in order, each with its own clock reading, on top of a reachable state, is itself reachable from the initial state.

**Edge cases the statement includes.** For $bs = [\,]$, $\mathrm{connectChain}(S, [\,]) = \text{some } (S, [\,])$, so $T = S$ and the conclusion is the hypothesis $\mathit{hR}$. The list $\mathit{undos}$ appears in the hypothesis only; the conclusion does not mention it. Nothing is asserted when $\mathrm{connectChain}(S, bs)$ is "none".
