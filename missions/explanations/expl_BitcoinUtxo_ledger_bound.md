We prove the ledger supply bound: from the empty UTXO set, after any sequence of accepted blocks at consecutive heights from $h$,
$$\mathrm{totalValue}(U) \le \sum_{i<n} s(h + i).$$

This is `BitcoinUtxo.chain_bound` applied to the empty view, which trivially has distinct outpoints and total value $0$. The content of the argument lies in the chain and block bounds: within each block, fees leave the ledger through the ordinary transactions and return through the coinbase, which may add at most the subsidy beyond them; unspendable outputs only lower the total; the BIP30 check and distinct txids keep every added outpoint fresh so that no value is silently replaced.

With $s$ the mainnet subsidy and $h = 1$, the right-hand side is the cumulative subsidy, which the subsidy mission bounds below `MAX_MONEY`.
