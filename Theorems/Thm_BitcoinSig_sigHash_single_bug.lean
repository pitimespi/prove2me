import Definitions.Def_BitcoinSig
open BitcoinSig BitcoinSer

theorem BitcoinSig.sigHash_single_bug (scriptCode : Bytes) (tx : Tx) (nIn hashType : Nat)
    (h1 : hashType &&& 0x1f = BitcoinSig.SIGHASH_SINGLE) (h2 : tx.vout.length ≤ nIn) :
    BitcoinSig.sigHashLegacy scriptCode tx nIn hashType = BitcoinSig.uint256One := by sorry
