We prove that `addCoin` at an outpoint absent from the view raises the total by the coin's value, or by nothing when the output is unspendable.

`addCoin` returns the view unchanged for an unspendable output. Otherwise it removes any entry at the outpoint and prepends the new one; since the outpoint is absent, the removal is the identity, and prepending adds exactly the coin's value to the total.
