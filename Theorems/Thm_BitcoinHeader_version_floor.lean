import Definitions.Def_BitcoinHeader

theorem BitcoinHeader.version_floor (h : BitcoinHeader.Header) (prevHeight : Nat) (prevTimes : List Int)
    (required : BitVec 32) (now : Int)
    (hc : BitcoinHeader.contextualCheck h prevHeight prevTimes required now = true) :
    (BitcoinHeader.BIP34Height ≤ prevHeight + 1 → 2 ≤ h.version) ∧
    (BitcoinHeader.BIP66Height ≤ prevHeight + 1 → 3 ≤ h.version) ∧
    (BitcoinHeader.BIP65Height ≤ prevHeight + 1 → 4 ≤ h.version) := by sorry
