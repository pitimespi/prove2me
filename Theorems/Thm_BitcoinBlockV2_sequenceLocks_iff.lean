import Definitions.Def_BitcoinBlockV2
import Definitions.Def_BitcoinSer

theorem BitcoinBlockV2.sequenceLocks_iff (u : Ledger) (height : Nat) (mtp : Nat → Nat) (ltf : Nat) (tx : BitcoinSer.Tx) :
    BitcoinBlockV2.sequenceLocksOk u height mtp ltf tx = true ↔
      BitcoinBIP68.satisfiesBIP68 (BitVec.ofNat 32 tx.version) (BitVec.ofNat 32 ltf) ⟨height, mtp⟩
        (tx.vin.map fun i => ⟨BitVec.ofNat 32 i.nSequence, (BitcoinBlockV2.accessCoin u i.prevout).height⟩) := by sorry
