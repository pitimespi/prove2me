import Definitions.Def_BitcoinHeader

theorem BitcoinHeader.contextualCheck_iff (h : BitcoinHeader.Header) (prevHeight : Nat) (prevTimes : List Int)
    (required : BitVec 32) (now : Int) :
    BitcoinHeader.contextualCheck h prevHeight prevTimes required now = true ↔
      h.bits = required ∧
      BitcoinHeader.medianTimePast prevTimes < h.time ∧
      h.time ≤ now + BitcoinHeader.MAX_FUTURE_BLOCK_TIME ∧
      ¬ ((h.version < 2 ∧ BitcoinHeader.BIP34Height ≤ prevHeight + 1) ∨
         (h.version < 3 ∧ BitcoinHeader.BIP66Height ≤ prevHeight + 1) ∨
         (h.version < 4 ∧ BitcoinHeader.BIP65Height ≤ prevHeight + 1)) := by sorry
