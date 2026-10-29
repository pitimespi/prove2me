Unfold `multisigLoop` on two signatures and two keys: a failing first check leaves one key for two signatures, which the loop rejects; so success forces `checkSig s₁ k₁` and then `checkSig s₂ k₂`.
