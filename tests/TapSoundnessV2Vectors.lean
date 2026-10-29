import Definitions.Def_BitcoinTapSoundnessV2
open BitcoinTapSoundnessV2 BitcoinTaproot BitcoinSer

/-! An honest two-leaf tree: the control block for each leaf walks to that leaf (`scriptPathWitness = none`);
a control block carrying a foreign leaf hash with a borrowed path does not reach the root at all. -/
def leafA : TapTree := .leaf 0xc0 [0x51]
def leafB : TapTree := .leaf 0xc0 [0x52]
def tree : TapTree := .branch leafA leafB
def ctrlA : Bytes := [0xc0] ++ List.replicate 32 0x11 ++ leafB.hash   -- path for leaf A: sibling B
def ctrlB : Bytes := [0xc0] ++ List.replicate 32 0x11 ++ leafA.hash

example : taprootMerkleRoot ctrlA leafA.hash = tree.hash := by decide +kernel
example : scriptPathWitness tree ctrlA 0xc0 [0x51] = none := by decide +kernel
example : scriptPathWitness tree ctrlB 0xc0 [0x52] = none := by decide +kernel
example : walk tree (controlNodes ctrlA) leafA.hash = .inl leafA := by decide +kernel
-- a leaf not in the tree, with A's path, does not reach the root (no collision is exhibited)
example : taprootMerkleRoot ctrlA (tapleafHash 0xc0 [0x53]) ≠ tree.hash := by decide +kernel
-- the walk returns a pair exactly where a path claims a wrong child: here the root of a one-leaf tree
example : walk leafA [leafB.hash] leafB.hash =
    .inr (taggedPre "TapLeaf" (leafMsg 0xc0 [0x51]), taggedPre "TapBranch" (branchMsg leafB.hash leafB.hash)) := by decide +kernel
