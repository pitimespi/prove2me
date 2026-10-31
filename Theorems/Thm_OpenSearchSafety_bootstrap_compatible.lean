import Definitions.Def_OpenSearchSafety
open OpenSearchCoordination OpenSearchSafety

theorem OpenSearchSafety.bootstrap_compatible (eligible : NodeId → Bool) (k : Nat) (resolve placeholder : Nat → NodeId)
    (hres : ∀ i j, i < k → j < k → resolve i = resolve j → i = j)
    (hph : ∀ i j, i < k → j < k → placeholder i = placeholder j → i = j)
    (hdis : ∀ i j, i < k → j < k → placeholder i ≠ resolve j)
    (hphe : ∀ i, i < k → eligible (placeholder i) = false)
    (X Y : VotingConfiguration) (mX mY : Nat → Bool)
    (hX : BootstrapConfig k resolve placeholder mX X) (hY : BootstrapConfig k resolve placeholder mY Y)
    (q₁ q₂ : List NodeId) (hq₁ : ∀ x ∈ q₁, eligible x = true) (hq₂ : ∀ x ∈ q₂, eligible x = true)
    (h₁ : X.hasQuorum q₁ = true) (h₂ : Y.hasQuorum q₂ = true) : ∃ x, x ∈ q₁ ∧ x ∈ q₂ := by sorry
