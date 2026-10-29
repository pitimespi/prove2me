import Definitions.Def_BitcoinReorg
import Definitions.Def_BitcoinSer
open BitcoinReorg BitcoinBlockV2

theorem BitcoinReorg.validate_equiv (S T : ChainState) (h : BitcoinReorg.StateEquiv S T) (b : BitcoinSer.Block) (now : Int) :
    (BitcoinBlockV2.validate S b now = .invalid ∧ BitcoinBlockV2.validate T b now = .invalid) ∨
    (BitcoinBlockV2.validate S b now = .futureTime ∧ BitcoinBlockV2.validate T b now = .futureTime) ∨
    (BitcoinBlockV2.validate S b now = .missingPrev ∧ BitcoinBlockV2.validate T b now = .missingPrev) ∨
    (∃ S' T' undo, BitcoinBlockV2.validate S b now = .accept S' undo ∧ BitcoinBlockV2.validate T b now = .accept T' undo ∧
      BitcoinReorg.StateEquiv S' T') := by sorry
