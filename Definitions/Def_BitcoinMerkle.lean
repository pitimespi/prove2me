import Std

namespace BitcoinMerkle

/-! Transcription of `ComputeMerkleRoot` (`src/consensus/merkle.cpp`, Bitcoin Core revision
`a773e1e33b349dc819b5a0edc1c7a4839dc73b48`). Hashes are an arbitrary type `H` with decidable
equality; the pairwise hash `SHA256D64` on two concatenated hashes is an abstract function
`c : H → H → H`, and `uint256()` (the all-zero hash returned for an empty list) is an abstract
`z : H`. The loop body is: flag any equal aligned pair `(pos, pos + 1)` of the current level
(`pos` even, `pos + 1 < size`), duplicate the last element when the level has odd length, hash
adjacent pairs, and continue while more than one hash remains. -/

variable {H : Type} [DecidableEq H]

/-- One level of the tree: hash adjacent pairs; an odd trailing element is hashed with itself,
which is `hashes.push_back(hashes.back())` followed by `SHA256D64`. -/
def pairUp (c : H → H → H) : List H → List H
  | a :: b :: rest => c a b :: pairUp c rest
  | [a] => [c a a]
  | [] => []

/-- The mutation test of one level: some aligned pair `(pos, pos + 1)` with `pos` even and
`pos + 1 < size` consists of equal hashes. The duplicated trailing element is not tested. -/
def hasEqualPair : List H → Bool
  | a :: b :: rest => decide (a = b) || hasEqualPair rest
  | _ => false

omit [DecidableEq H] in
theorem pairUp_length (c : H → H → H) : ∀ l : List H, (pairUp c l).length = (l.length + 1) / 2
  | a :: b :: rest => by
    simp only [pairUp, List.length_cons, pairUp_length c rest]
    omega
  | [a] => by simp [pairUp]
  | [] => by simp [pairUp]

/-- The `while (hashes.size() > 1)` loop with its running `mutation` flag. -/
def rootLoop (c : H → H → H) (z : H) (hs : List H) (mutation : Bool) : H × Bool :=
  if _h : 1 < hs.length then
    rootLoop c z (pairUp c hs) (mutation || hasEqualPair hs)
  else
    (hs.headD z, mutation)
termination_by hs.length
decreasing_by
  simp_wf
  rw [pairUp_length]
  omega

/-- `ComputeMerkleRoot(hashes, mutated)`: the root and the mutation flag. -/
def computeMerkleRoot (c : H → H → H) (z : H) (hs : List H) : H × Bool :=
  rootLoop c z hs false

end BitcoinMerkle
