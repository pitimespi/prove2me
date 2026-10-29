import Definitions.Def_BitcoinUniqueness
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinSig
open BitcoinUniqueness BitcoinSer BitcoinBlockV2

theorem BitcoinUniqueness.pushBytes_prefix (d d' : BitcoinSer.Bytes) (hd : d.length < 2 ^ 32) (hd' : d'.length < 2 ^ 32)
    (h : (BitcoinSig.pushBytes d).isPrefixOf (BitcoinSig.pushBytes d') = true) : d = d' := by sorry
