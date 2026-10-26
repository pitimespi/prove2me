import Definitions.Def_BitcoinBlock
import Definitions.Def_BitcoinActivation
import Definitions.Def_BitcoinSer

theorem BitcoinBlock.connectLoop_iff (f : BitcoinActivation.ScriptFlags) (H : Nat) (mtp : Nat → Nat) (ltf : Nat)
    (txs : List BitcoinSer.Tx) (u : Ledger) (fees : Int) (sigOps : Nat) (undo : BlockUndo)
    (hpos : ∀ tx ∈ txs, 0 ≤ BitcoinBlock.valueOut tx) (hfees : 0 ≤ fees) :
    (∃ st, BitcoinBlock.connectLoop f H mtp ltf ⟨u, fees, sigOps, undo⟩ txs = some st) ↔
      BitcoinBlock.TxsSpec f H mtp ltf u fees sigOps txs := by sorry
