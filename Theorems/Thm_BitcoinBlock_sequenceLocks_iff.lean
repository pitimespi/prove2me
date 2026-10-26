import Definitions.Def_BitcoinBlock
import Definitions.Def_BitcoinSer

theorem BitcoinBlock.sequenceLocks_iff (u : Ledger) (height : Nat) (mtp : Nat → Nat) (ltf : Nat) (tx : BitcoinSer.Tx) :
    BitcoinBlock.sequenceLocksOk u height mtp ltf tx = true ↔
      BitcoinBIP68.satisfiesBIP68 (BitVec.ofNat 32 tx.version) (BitVec.ofNat 32 ltf) ⟨height, mtp⟩
        (tx.vin.map fun i => ⟨BitVec.ofNat 32 i.nSequence, (BitcoinBlock.accessCoin u i.prevout).height⟩) := by sorry
