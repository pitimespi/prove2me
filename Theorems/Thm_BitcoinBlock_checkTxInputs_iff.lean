import Definitions.Def_BitcoinBlock
import Definitions.Def_BitcoinSer

theorem BitcoinBlock.checkTxInputs_iff (u : Ledger) (tx : BitcoinSer.Tx) (H : Nat) :
    ((∃ fee, BitcoinBlock.checkTxInputs u tx H = some fee) ↔
      (∀ i ∈ tx.vin, ∃ c, BitcoinBlock.getCoin u i.prevout = some c ∧
        (c.isCoinbase = true → c.height + COINBASE_MATURITY ≤ H) ∧ 0 ≤ c.out.nValue ∧ c.out.nValue ≤ MAX_MONEY) ∧
      BitcoinBlock.valueIn u tx.vin ≤ MAX_MONEY ∧ BitcoinBlock.valueOut tx ≤ BitcoinBlock.valueIn u tx.vin ∧
      BitcoinBlock.valueIn u tx.vin - BitcoinBlock.valueOut tx ≤ MAX_MONEY) ∧
    (∀ fee, BitcoinBlock.checkTxInputs u tx H = some fee → fee = BitcoinBlock.feeOf u tx) := by sorry
