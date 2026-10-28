import Definitions.Def_BitcoinSupply
open BitcoinSupply BitcoinBlockV2

theorem BitcoinSupply.supply_bound (S : ChainState) (hR : BitcoinBlockV2.Reachable S) :
    BitcoinSupply.totalValue S.utxo + BitcoinSupply.genesisSubsidy ≤ BitcoinSupply.issued S.nextHeight := by sorry
