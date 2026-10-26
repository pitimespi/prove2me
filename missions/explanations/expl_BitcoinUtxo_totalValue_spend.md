We prove that removing a present coin $c$ at outpoint $p$ from a view with distinct outpoints lowers `totalValue` by exactly $c.\mathrm{value}$.

By induction on the list. At an entry with key $p$, distinctness of keys means no later entry has key $p$, so the lookup on the tail is `none` and spending the tail is the identity; the total drops by the value of the removed entry, which the lookup identified as $c$. At an entry with a different key, the entry is kept and the claim follows from the induction hypothesis on the tail, whose keys are still distinct.
