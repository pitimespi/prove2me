import Definitions.Def_BitcoinSig
open BitcoinSig BitcoinSer

theorem BitcoinSig.sigHashLegacy_anyoneCanPay (scriptCode : Bytes) (tx tx' : Tx) (nIn hashType : Nat)
    (hacp : hashType &&& BitcoinSig.SIGHASH_ANYONECANPAY ≠ 0)
    (h1 : tx'.version = tx.version) (h2 : tx'.vout = tx.vout) (h3 : tx'.nLockTime = tx.nLockTime)
    (h4 : (tx'.vin.getD nIn ⟨⟨[], 0⟩, [], 0, []⟩).prevout = (tx.vin.getD nIn ⟨⟨[], 0⟩, [], 0, []⟩).prevout)
    (h5 : (tx'.vin.getD nIn ⟨⟨[], 0⟩, [], 0, []⟩).nSequence = (tx.vin.getD nIn ⟨⟨[], 0⟩, [], 0, []⟩).nSequence) :
    BitcoinSig.sigHashLegacy scriptCode tx' nIn hashType = BitcoinSig.sigHashLegacy scriptCode tx nIn hashType := by sorry
