import Definitions.Def_BitcoinSupply
import Definitions.Def_BitcoinSer
open BitcoinSupply BitcoinBlockV2

theorem BitcoinSupply.update_bound (u : Ledger) (tx : BitcoinSer.Tx) (H : Nat) (hnd : BitcoinBlockV2.keysNodup u)
    (hnn : ∀ e ∈ u, 0 ≤ e.2.out.nValue) (hos : ∀ o ∈ tx.vout, 0 ≤ o.nValue)
    (hdup : (tx.vin.map BitcoinSer.TxIn.prevout).Nodup)
    (hin : BitcoinBlockV2.isCoinBase tx = false → ∀ i ∈ tx.vin, BitcoinBlockV2.haveCoin u i.prevout = true) :
    BitcoinSupply.totalValue (BitcoinBlockV2.updateCoins u tx H) ≤
      BitcoinSupply.totalValue u + BitcoinBlockV2.valueOut tx -
        (if BitcoinBlockV2.isCoinBase tx then 0 else BitcoinBlockV2.valueIn u tx.vin) := by sorry
