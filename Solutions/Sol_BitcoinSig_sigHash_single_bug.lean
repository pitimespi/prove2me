import Definitions.Def_BitcoinSig
import Theorems.Thm_BitcoinScript_p2pkh_correct

open BitcoinSig BitcoinSer

/-- With `SIGHASH_SINGLE` and no output at the input's index, the legacy sighash is `uint256::ONE`. -/
theorem solution (scriptCode : Bytes) (tx : Tx) (nIn hashType : Nat)
    (h1 : hashType &&& 0x1f = BitcoinSig.SIGHASH_SINGLE) (h2 : tx.vout.length ≤ nIn) :
    BitcoinSig.sigHashLegacy scriptCode tx nIn hashType = BitcoinSig.uint256One := by
  unfold sigHashLegacy
  rw [if_pos ⟨h1, h2⟩]
