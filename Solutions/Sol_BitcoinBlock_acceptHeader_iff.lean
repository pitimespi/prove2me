import Definitions.Def_BitcoinBlock
import Theorems.Thm_BitcoinPow_checkProofOfWork_iff
import Theorems.Thm_BitcoinHeader_versionOutdated_iff
import Theorems.Thm_BitcoinSubsidy_core_eq_spec
import Theorems.Thm_BitcoinBIP68_fold_acceptance
import Theorems.Thm_BitcoinBIP68_decode_sequence

open BitcoinBlock

/-- The initial state is well formed. -/
private theorem initial_wellFormed : BitcoinBlock.WellFormed BitcoinBlock.initialState := by
  refine ⟨rfl, List.nodup_nil, ?_⟩
  intro e he; cases he

/-- `AcceptBlockHeader` on top of the tip accepts exactly when the proof of work holds, the parent is
the tip, and the Header mission's `ContextualCheckBlockHeader` holds with the chain's median time past
and required work. -/
private theorem acceptHeader_eq_iff (S : ChainState) (h : BitcoinSer.Header) (now : Int) :
    BitcoinBlock.acceptHeader S h now = .accept S [] ↔
      BitcoinBlock.checkHeaderPow h = true ∧ h.prevBlock = S.tipHash ∧
      BitVec.ofNat 32 h.bits = S.requiredBits ∧ ¬ ((h.time : Int) ≤ S.mtp) ∧
      ¬ (now + MAX_FUTURE_BLOCK_TIME < (h.time : Int)) ∧
      BitcoinHeader.versionOutdated h.version S.tipHeight = false := by
  unfold acceptHeader
  simp only [Bool.not_eq_true']
  by_cases h1 : checkHeaderPow h = false <;> by_cases h2 : h.prevBlock = S.tipHash <;>
    by_cases h3 : BitVec.ofNat 32 h.bits = S.requiredBits <;> by_cases h4 : (h.time : Int) ≤ S.mtp <;>
    by_cases h5 : now + MAX_FUTURE_BLOCK_TIME < (h.time : Int) <;>
    by_cases h6 : BitcoinHeader.versionOutdated h.version S.tipHeight = true <;>
    simp only [h1, h2, h3, h4, h5, h6, ite_true, ite_false, ne_eq, not_true_eq_false, not_false_eq_true] <;>
    simp_all

theorem solution (S : ChainState) (h : BitcoinSer.Header) (now : Int) :
    BitcoinBlock.acceptHeader S h now = .accept S [] ↔
      BitcoinBlock.checkHeaderPow h = true ∧ h.prevBlock = S.tipHash ∧
      BitcoinHeader.contextualCheck ⟨h.version, (h.time : Int), BitVec.ofNat 32 h.bits⟩ S.tipHeight
        (S.timesTo S.tipHeight) S.requiredBits now = true := by
  rw [acceptHeader_eq_iff]
  have hM : BitcoinHeader.MAX_FUTURE_BLOCK_TIME = MAX_FUTURE_BLOCK_TIME := rfl
  have hmtp : BitcoinHeader.medianTimePast (S.timesTo S.tipHeight) = S.mtp := rfl
  simp only [BitcoinHeader.contextualCheck, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', hM, hmtp]
  constructor
  · rintro ⟨a, b, c, d, e, f⟩; exact ⟨a, b, ⟨⟨c, by omega⟩, by omega⟩, f⟩
  · rintro ⟨a, b, ⟨⟨c, d⟩, e⟩, f⟩; exact ⟨a, b, c, by omega, by omega, f⟩
