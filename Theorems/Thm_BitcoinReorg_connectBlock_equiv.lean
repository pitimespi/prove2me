import Definitions.Def_BitcoinReorg
import Definitions.Def_BitcoinSer
open BitcoinReorg BitcoinBlockV2

theorem BitcoinReorg.connectBlock_equiv (H : List BitcoinSer.Header) (u v : Ledger) (h : BitcoinBlockV2.Equiv u v)
    (b : BitcoinSer.Block) :
    (BitcoinBlockV2.connectBlock ⟨H, u⟩ b = none ∧ BitcoinBlockV2.connectBlock ⟨H, v⟩ b = none) ∨
    (∃ u' v' undo, BitcoinBlockV2.connectBlock ⟨H, u⟩ b = some (u', undo) ∧
      BitcoinBlockV2.connectBlock ⟨H, v⟩ b = some (v', undo) ∧ BitcoinBlockV2.Equiv u' v') := by sorry
