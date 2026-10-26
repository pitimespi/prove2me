We prove that an accepted ordinary transaction with fresh outputs lowers the ledger by at least its fee:
$$\mathrm{totalValue}(\mathrm{updateCoins}(U, tx, h)) \le \mathrm{totalValue}(U) - f.$$

**Idea.** `updateCoins` spends the inputs and adds the outputs. Spending removes exactly `valueIn` (the inputs are distinct and present); adding at fresh outpoints contributes at most `valueOut` (an unspendable output contributes nothing); and the fee identity `BitcoinUtxo.checkTxInputs_some` gives $f = \mathrm{valueIn} - \mathrm{valueOut}$.

**Step 1.** By `checkTxInputs_some`, every input is present and $f = \mathrm{valueIn}(U, I) - \mathrm{valueOut}(tx)$.

**Step 2.** By `BitcoinUtxo.totalValue_spendInputs`, the view $U_1$ after spending has total $\mathrm{totalValue}(U) - \mathrm{valueIn}$.

**Step 3.** Freshness survives spending, since spending only removes entries. Adding the outputs $o_0, o_1, \dots$ at outpoints $(\mathrm{txid}, 0), (\mathrm{txid}, 1), \dots$ is an induction: each outpoint is fresh when reached (distinct indices), `BitcoinUtxo.totalValue_add_fresh` adds at most its value, and non-negativity of the values makes the unspendable case a loss. The total after adding is at most $\mathrm{totalValue}(U_1) + \mathrm{valueOut}$.

Combining, the final total is at most $\mathrm{totalValue}(U) - \mathrm{valueIn} + \mathrm{valueOut} = \mathrm{totalValue}(U) - f$.
