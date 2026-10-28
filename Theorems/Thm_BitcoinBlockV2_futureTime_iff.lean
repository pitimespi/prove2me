import Definitions.Def_BitcoinBlockV2
import Definitions.Def_BitcoinSer

theorem BitcoinBlockV2.futureTime_iff (S : ChainState) (b : BitcoinSer.Block) (now : Int) :
    BitcoinBlockV2.validate S b now = .futureTime ↔
      BitcoinBlockV2.checkHeaderPow b.header = true ∧ b.header.prevBlock = S.tipHash ∧
      BitVec.ofNat 32 b.header.bits = S.requiredBits ∧ S.mtp < (b.header.time : Int) ∧
      now + MAX_FUTURE_BLOCK_TIME < (b.header.time : Int) := by sorry
