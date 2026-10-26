import Definitions.Def_BitcoinBlock
import Definitions.Def_BitcoinSer

theorem BitcoinBlock.futureTime_iff (S : ChainState) (b : BitcoinSer.Block) (now : Int) :
    BitcoinBlock.validate S b now = .futureTime ↔
      BitcoinBlock.checkHeaderPow b.header = true ∧ b.header.prevBlock = S.tipHash ∧
      BitVec.ofNat 32 b.header.bits = S.requiredBits ∧ S.mtp < (b.header.time : Int) ∧
      now + MAX_FUTURE_BLOCK_TIME < (b.header.time : Int) := by sorry
