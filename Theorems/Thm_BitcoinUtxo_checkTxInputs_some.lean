import Definitions.Def_BitcoinUtxo
open BitcoinUtxo

theorem BitcoinUtxo.checkTxInputs_some {T : Type} [DecidableEq T] (u : UtxoSet T) (tx : Tx T) (h : Nat) (fee : Int)
    (hfee : checkTxInputs u tx h = some fee) :
    fee = valueIn u tx.vin - valueOut tx ∧ 0 ≤ fee ∧ fee ≤ MAX_MONEY ∧
    ∀ op ∈ tx.vin, haveCoin u op = true := by sorry
