We prove that an accepted block raises the ledger by at most the subsidy, and keeps outpoints distinct.

**Idea.** The loop of `connectBlock` processes the coinbase and the ordinary transactions in order; an invariant bounds the running view and fees together: $\mathrm{totalValue}(U_k) + \mathrm{fees}_k \le \mathrm{totalValue}(U) + \mathrm{valueOut}(\text{coinbase})$. The coinbase bound then converts the coinbase output into fees plus subsidy.

**Step 1 (preconditions).** `checkBlockTxs` gives that the first transaction is the coinbase, no other is, and all pass `checkTransaction`, hence (`BitcoinUtxo.checkTransaction_outputs`) have distinct inputs and non-negative outputs. `bip30Ok` gives that no output outpoint of any transaction is present in the initial view.

**Step 2 (freshness through the block).** When transaction $k$ is reached, its outpoints are still absent: `updateCoins` of an earlier transaction only removes entries or adds outpoints with that transaction's txid, and txids within the block are distinct.

**Step 3 (the loop invariant).** By induction over the transaction list: for the coinbase, `BitcoinUtxo.coinbase_bound` adds at most `valueOut`; for an ordinary transaction with fee $f$, `BitcoinUtxo.tx_conservation` removes at least $f$ from the view while the loop adds $f$ to the fees, so the sum does not increase. Distinctness of outpoints is preserved by each update.

**Step 4.** At the end, $\mathrm{totalValue}(U') + \mathrm{fees} \le \mathrm{totalValue}(U) + \mathrm{valueOut}(\text{cb})$, and the final check gives $\mathrm{valueOut}(\text{cb}) \le \mathrm{fees} + s(h)$; eliminating the fees yields the bound.
