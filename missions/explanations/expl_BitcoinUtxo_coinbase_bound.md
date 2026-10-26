We prove that a coinbase with fresh, non-negative outputs raises the ledger by at most `valueOut`.

For a coinbase, `updateCoins` spends nothing and adds the outputs in index order. By induction on the outputs, each is added at a fresh outpoint (distinct indices keep later outpoints fresh), so by `BitcoinUtxo.totalValue_add_fresh` it contributes its value or, if unspendable, nothing; with non-negative values the contribution is at most the value. The sum of the contributions is at most `valueOut`.
