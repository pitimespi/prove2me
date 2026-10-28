import Definitions.Def_BitcoinBlockV2
import Definitions.Def_BitcoinSer

theorem BitcoinBlockV2.checkTxInputs_iff (u : Ledger) (tx : BitcoinSer.Tx) (H : Nat) :
    ((∃ fee, BitcoinBlockV2.checkTxInputs u tx H = some fee) ↔
      (∀ i ∈ tx.vin, ∃ c, BitcoinBlockV2.getCoin u i.prevout = some c ∧
        (c.isCoinbase = true → c.height + COINBASE_MATURITY ≤ H) ∧ 0 ≤ c.out.nValue ∧ c.out.nValue ≤ MAX_MONEY) ∧
      BitcoinBlockV2.valueIn u tx.vin ≤ MAX_MONEY ∧ BitcoinBlockV2.valueOut tx ≤ BitcoinBlockV2.valueIn u tx.vin ∧
      BitcoinBlockV2.valueIn u tx.vin - BitcoinBlockV2.valueOut tx ≤ MAX_MONEY) ∧
    (∀ fee, BitcoinBlockV2.checkTxInputs u tx H = some fee → fee = BitcoinBlockV2.feeOf u tx) := by sorry
