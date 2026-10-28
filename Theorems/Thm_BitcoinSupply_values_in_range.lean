import Definitions.Def_BitcoinSupply
open BitcoinSupply BitcoinBlockV2

theorem BitcoinSupply.values_in_range (S : ChainState) (hR : BitcoinBlockV2.Reachable S) :
    BitcoinSupply.ValuesInRange S.utxo := by sorry
