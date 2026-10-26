import Definitions.Def_BitcoinBlock
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinHeader

theorem BitcoinBlock.acceptHeader_iff (S : ChainState) (h : BitcoinSer.Header) (now : Int) :
    BitcoinBlock.acceptHeader S h now = .accept S [] ↔
      BitcoinBlock.checkHeaderPow h = true ∧ h.prevBlock = S.tipHash ∧
      BitcoinHeader.contextualCheck ⟨h.version, (h.time : Int), BitVec.ofNat 32 h.bits⟩ S.tipHeight
        (S.timesTo S.tipHeight) S.requiredBits now = true := by sorry
