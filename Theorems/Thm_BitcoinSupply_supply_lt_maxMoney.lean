import Definitions.Def_BitcoinSupply
open BitcoinSupply BitcoinBlockV2

theorem BitcoinSupply.supply_lt_maxMoney (S : ChainState) (hR : BitcoinBlockV2.Reachable S) :
    BitcoinSupply.totalValue S.utxo < MAX_MONEY := by sorry
