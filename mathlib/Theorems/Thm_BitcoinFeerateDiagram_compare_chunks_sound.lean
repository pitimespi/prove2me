import Definitions.Def_BitcoinFeerateDiagram
open BitcoinFeerateDiagram BitcoinReplacement

theorem BitcoinFeerateDiagram.compare_chunks_sound (c0 c1 : List FeeFrac) (h0 : SizesPos c0)
    (h1 : SizesPos c1) :
    (compareChunks c0 c1 = .greater ↔ StrictlyBetter c0 c1) ∧
    (compareChunks c0 c1 = .less ↔ StrictlyBetter c1 c0) ∧
    (compareChunks c0 c1 = .equivalent ↔ ∀ x : ℚ, 0 ≤ x → diagram c0 x = diagram c1 x) ∧
    (compareChunks c0 c1 = .unordered ↔ BetterSomewhere c0 c1 ∧ BetterSomewhere c1 c0) := by sorry
