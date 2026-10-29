import Definitions.Def_BitcoinUniqueness
import Definitions.Def_BitcoinHeader
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinReorg
open BitcoinUniqueness BitcoinSer BitcoinBlockV2

theorem BitcoinUniqueness.chain_coinbases_distinct (S : ChainState) (hR : BitcoinBlockV2.Reachable S)
    (h34 : BitcoinHeader.BIP34Height ≤ S.nextHeight) (bs : List (BitcoinSer.Block × Int)) (T : ChainState)
    (undos : List BlockUndo) (hc : BitcoinReorg.connectChain S bs = some (T, undos))
    (hlt : S.nextHeight + bs.length < 2 ^ 31) :
    (bs.map fun p => BitcoinUniqueness.coinbaseScriptSig p.1).Nodup := by sorry
