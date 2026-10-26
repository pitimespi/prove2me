# Read-back: `BitcoinBlock.reachable_wellFormed`

## Binders and hypotheses

- $S$ : a chain state $\langle\mathit{headers}, \mathit{utxo}\rangle$.
- Hypothesis $h$ : $\mathrm{Reachable}(S)$, the least predicate closed under: (genesis) $\mathrm{Reachable}(\langle [\mathrm{genesisHeader}], [\,]\rangle)$; (step) for any $S_0$, block $b$, clock $t \in \mathbb{Z}$, state $S_1$ and undo list $u$, if $\mathrm{Reachable}(S_0)$ and $\mathrm{validate}(S_0, b, t) = \mathrm{accept}(S_1, u)$ then $\mathrm{Reachable}(S_1)$.

## Conclusion

$$\mathrm{WellFormed}(S),$$ i.e. the conjunction of:

1. the head of $S.\mathrm{headers}$ exists and equals $\mathrm{genesisHeader}$ (version $1$, prevBlock 32 zero bytes, merkleRoot the txid of the genesis coinbase, time $1231006505$, bits $0x1d00ffff$, nonce $2083236893$);
2. $\mathrm{keysNodup}(S.\mathrm{utxo})$: the list of outpoint keys of the ledger has no duplicates;
3. for every entry $e = (\mathit{op}, c)$ of $S.\mathrm{utxo}$: $1 \le c.\mathrm{height}$, $c.\mathrm{height} \le |S.\mathrm{headers}| - 1$ (natural subtraction), and $c.\mathrm{out.scriptPubKey}$ is not unspendable (it does not start with byte $0x6a$ and its length is at most $10\,000$).

### The step rule, unfolded

$\mathrm{validate}(S_0,b,t) = \mathrm{accept}(S_1,u)$ means: the header of $b$ passes proof of work, builds on the tip hash of $S_0$, has the required bits, a time above the tip's median-time-past and at most $t+7200$, and a non-outdated version; $\mathrm{checkBlock}(b)$ and $\mathrm{contextualCheckBlock}(S_0,b)$ hold; and $\mathrm{connectBlock}(S_0,b) = \mathrm{some}(u_1,u)$ with $S_1 = \langle S_0.\mathrm{headers} \mathbin{+\!\!+} [b.\mathrm{header}], u_1\rangle$. In $\mathrm{connectBlock}$, if the block's header hash is the genesis hash the ledger is returned unchanged; otherwise $u_1$ results from the transaction loop at height $|S_0.\mathrm{headers}|$, which spends inputs and adds spendable outputs (unspendable scripts are never stored; an added entry replaces any entry with the same key) at that height, after BIP30 (when checked), input, fee, BIP68, sigop, script and coinbase-bound checks.

## Edge cases silently included

The initial state has an empty ledger, so clauses 2 and 3 are vacuous there; the genesis-hashed shortcut adds a header without touching the ledger; clause 3 compares to $|S.\mathrm{headers}|-1$ which is $0$ for an empty list (unreachable under $h$ but the predicate itself is defined for it); the undo lists and clocks in the derivation are existentially hidden in the hypothesis.
