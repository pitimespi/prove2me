import Definitions.Def_BitcoinHeader

theorem BitcoinHeader.versionOutdated_iff (version : Int) (prevHeight : Nat) :
    BitcoinHeader.versionOutdated version prevHeight = true ↔
      (version < 2 ∧ BitcoinHeader.BIP34Height ≤ prevHeight + 1) ∨
      (version < 3 ∧ BitcoinHeader.BIP66Height ≤ prevHeight + 1) ∨
      (version < 4 ∧ BitcoinHeader.BIP65Height ≤ prevHeight + 1) := by sorry
