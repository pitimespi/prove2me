import Definitions.Def_BitcoinUniqueness
import Definitions.Def_BitcoinSer
open BitcoinUniqueness BitcoinSer BitcoinBlockV2

theorem BitcoinUniqueness.scan_runs_late (S : ChainState) (b : BitcoinSer.Block)
    (h : BIP34_IMPLIES_BIP30_LIMIT ≤ S.nextHeight) : BitcoinUniqueness.ScanRuns S b := by sorry
