import Definitions.Def_BitcoinReorg
import Definitions.Def_BitcoinSer
open BitcoinReorg BitcoinBlockV2

theorem BitcoinReorg.updateCoins_equiv (u v : Ledger) (h : BitcoinBlockV2.Equiv u v) (tx : BitcoinSer.Tx) (H : Nat) :
    BitcoinBlockV2.Equiv (BitcoinBlockV2.updateCoins u tx H) (BitcoinBlockV2.updateCoins v tx H) := by sorry
