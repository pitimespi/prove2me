import Definitions.Def_BitcoinBlockV2
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinHeader

theorem BitcoinBlockV2.acceptHeader_iff (S : ChainState) (h : BitcoinSer.Header) (now : Int) :
    BitcoinBlockV2.acceptHeader S h now = .accept S [] ↔
      BitcoinBlockV2.checkHeaderPow h = true ∧ h.prevBlock = S.tipHash ∧
      BitcoinHeader.contextualCheck ⟨h.version, (h.time : Int), BitVec.ofNat 32 h.bits⟩ S.tipHeight
        (S.timesTo S.tipHeight) S.requiredBits now = true := by sorry
