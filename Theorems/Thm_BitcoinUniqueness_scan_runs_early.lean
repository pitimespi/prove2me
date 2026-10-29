import Definitions.Def_BitcoinUniqueness
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinHeader
open BitcoinUniqueness BitcoinSer BitcoinBlockV2

theorem BitcoinUniqueness.scan_runs_early (S : ChainState) (b : BitcoinSer.Block)
    (h : S.headers.length ≤ BitcoinHeader.BIP34Height)
    (hrep : BitcoinBlockV2.isBIP30Repeat S.nextHeight (BitcoinSer.headerHash b.header) = false) :
    BitcoinUniqueness.ScanRuns S b := by sorry
