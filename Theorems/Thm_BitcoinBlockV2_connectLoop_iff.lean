import Definitions.Def_BitcoinBlockV2
import Definitions.Def_BitcoinActivation
import Definitions.Def_BitcoinSer

theorem BitcoinBlockV2.connectLoop_iff (f : BitcoinActivation.ScriptFlags) (H : Nat) (mtp : Nat → Nat) (ltf : Nat)
    (txs : List BitcoinSer.Tx) (u : Ledger) (fees : Int) (sigOps : Nat) (undo : BlockUndo)
    (hpos : ∀ tx ∈ txs, 0 ≤ BitcoinBlockV2.valueOut tx) (hfees : 0 ≤ fees) :
    (∃ st, BitcoinBlockV2.connectLoop f H mtp ltf ⟨u, fees, sigOps, undo⟩ txs = some st) ↔
      BitcoinBlockV2.TxsSpec f H mtp ltf u fees sigOps txs := by sorry
