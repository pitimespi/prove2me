import Definitions.Def_BitcoinSig
open BitcoinSig BitcoinSer

theorem BitcoinSig.sigHashLegacy_skeleton (scriptCode : Bytes) (tx tx' : Tx) (nIn hashType : Nat)
    (h : BitcoinSig.sameSkeleton tx tx') :
    BitcoinSig.sigHashLegacy scriptCode tx' nIn hashType = BitcoinSig.sigHashLegacy scriptCode tx nIn hashType := by sorry
