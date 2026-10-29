import Definitions.Def_BitcoinUniqueness
import Definitions.Def_BitcoinSer
open BitcoinUniqueness BitcoinSer BitcoinBlockV2

theorem BitcoinUniqueness.scan_freshness (S : ChainState) (b : BitcoinSer.Block) (now : Int) (S' : ChainState)
    (undo : BlockUndo) (hR : BitcoinBlockV2.Reachable S) (h : BitcoinBlockV2.validate S b now = .accept S' undo)
    (hscan : BitcoinUniqueness.ScanRuns S b) (hg : BitcoinSer.headerHash b.header ≠ BitcoinSer.genesisHash) :
    BitcoinUniqueness.FreshOutputs S.utxo b := by sorry
