import Definitions.Def_BitcoinBlock
import Theorems.Thm_BitcoinPow_checkProofOfWork_iff
import Theorems.Thm_BitcoinHeader_versionOutdated_iff
import Theorems.Thm_BitcoinSubsidy_core_eq_spec
import Theorems.Thm_BitcoinBIP68_fold_acceptance
import Theorems.Thm_BitcoinBIP68_decode_sequence

open BitcoinBlock

/-- **Genesis initialization.** The mainnet genesis block passes `CheckBlock`: its proof of work,
merkle root, structure, coinbase and sigop count are all as the source requires. -/
theorem solution : BitcoinBlock.checkBlock BitcoinSer.genesisBlock = true := by
  decide +kernel
