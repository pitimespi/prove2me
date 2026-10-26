# Read-back: `BitcoinBlock.apply_spec`

## Binders and hypotheses

- $S$ : a chain state $\langle \mathit{headers}, \mathit{utxo}\rangle$ (list of serialized headers; ledger as an association list outpoint $\mapsto$ coin).
- $b$ : a serialized block (header and transaction list $b.\mathrm{vtx}$).
- $\mathit{now} \in \mathbb{Z}$ : the clock.
- $S'$ : a chain state.
- $\mathit{undo}$ : a block undo list (a list of lists of coins).
- Hypothesis $h$ : $\mathrm{validate}(S, b, \mathit{now}) = \mathrm{accept}(S', \mathit{undo})$.

## Conclusion

$$S' = \mathrm{applySpec}(S, b).$$

### Unfolding the hypothesis

$\mathrm{validate}(S,b,\mathit{now})$ returns $\mathrm{accept}(S'',u)$ only along one path: the header outcome $\mathrm{acceptHeader}(S, b.\mathrm{header}, \mathit{now})$ is accept (PoW holds; $b.\mathrm{header.prevBlock}$ equals the tip hash; bits modulo $2^{32}$ equal the required bits; the time exceeds the tip's median-time-past; the time is at most $\mathit{now}+7200$; the version is not outdated for height $\mathrm{tipHeight}+1$), then $\mathrm{checkBlock}(b)$ is true, then $\mathrm{contextualCheckBlock}(S,b)$ is true, then $\mathrm{connectBlock}(S,b) = \mathrm{some}(u, \mathit{undo}')$, in which case the result is
$$\mathrm{accept}\big(\langle S.\mathrm{headers} \mathbin{+\!\!+} [b.\mathrm{header}],\ u\rangle,\ \mathit{undo}'\big).$$
So the hypothesis says exactly that all these checks pass and $S' = \langle S.\mathrm{headers} \mathbin{+\!\!+} [b.\mathrm{header}], u\rangle$, $\mathit{undo} = \mathit{undo}'$, where $u$ is the ledger returned by $\mathrm{connectBlock}$: $S.\mathrm{utxo}$ itself if the header hash equals the genesis hash; otherwise the ledger produced by the transaction loop (for each transaction in order: non-coinbase inputs spent from the running ledger, then its spendable outputs — those whose script does not start with $0x6a$ and is at most $10\,000$ bytes long — added at height $|S.\mathrm{headers}|$ with the coinbase flag, each added entry replacing any existing entry with the same outpoint), after the BIP30, input, fee, BIP68, sigop, script and coinbase-bound checks have all passed.

### Unfolding the conclusion

$\mathrm{applySpec}(S,b)$ is:

- if the double-SHA256 hash of $b.\mathrm{header}$ equals the genesis hash: $\langle S.\mathrm{headers} \mathbin{+\!\!+} [b.\mathrm{header}],\ S.\mathrm{utxo}\rangle$;
- otherwise $\langle S.\mathrm{headers} \mathbin{+\!\!+} [b.\mathrm{header}],\ \mathrm{applyTxs}(|S.\mathrm{headers}|, S.\mathrm{utxo}, b.\mathrm{vtx})\rangle$, where $\mathrm{applyTxs}(H, u, [\,]) = u$ and $\mathrm{applyTxs}(H, u, tx :: \mathit{rest}) = \mathrm{applyTxs}(H, \mathrm{updateCoins}(u, tx, H), \mathit{rest})$, with $\mathrm{updateCoins}(u,tx,H)$ = add the outputs of $tx$ (indices $0,1,\dots$, keyed by $\langle\mathrm{txid}(tx), i\rangle$, height $H$, coinbase flag $=\mathrm{isCoinBase}(tx)$, unspendable outputs skipped) to the ledger obtained from $u$ by removing every entry keyed by a prevout of $tx$ — except that for a coinbase (exactly one input with null prevout) nothing is removed.

Thus the claim is that the state produced by the executable path equals the state obtained by appending the header and applying $\mathrm{applyTxs}$ (or leaving the ledger untouched for a genesis-hashed block). The undo list $\mathit{undo}$ and the clock $\mathit{now}$ appear only in the hypothesis.

## Edge cases silently included

A block whose header hash is the genesis hash (both sides keep the ledger); $b.\mathrm{vtx}$ cannot be empty under $h$ (checkBlock requires it non-empty) but no explicit hypothesis says so; $\mathit{undo}$ is unconstrained beyond $h$; the hypothesis may be unsatisfiable for a given $S$ (e.g. an empty header list, where the tip defaults to the genesis header), making the statement vacuous there.
