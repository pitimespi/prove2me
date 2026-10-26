`sigHashLegacy` begins with `if hashType &&& 0x1f = SIGHASH_SINGLE ∧ tx.vout.length ≤ nIn then uint256One else …`; both conjuncts are the hypotheses, so `rw [if_pos ⟨h1, h2⟩]` closes the goal.
