import Definitions.Def_BitcoinMerkle
import Definitions.Def_BitcoinSer
open BitcoinMerkle BitcoinSer
/-! Spot 22 vectors (`REVIEW_SPOT22.md`): the generic `ComputeMerkleRoot` loop (`consensus/merkle.cpp`)
with its CVE-2012-2459 mutation flag, instantiated with an injective string combine `(ab)` for hand-checkable
cases and with real double SHA-256 over 32-byte leaves. Expectations computed by
`tests/reference/merkle_reference.py`. Every line prints `true`. -/
def sc (a b : String) : String := "(" ++ a ++ b ++ ")"
def hexVal (c : Char) : Nat := if c.isDigit then c.toNat - 48 else c.toLower.toNat - 87
def ofHexL : List Char → Bytes
  | a :: b :: r => BitVec.ofNat 8 (hexVal a * 16 + hexVal b) :: ofHexL r
  | _ => []
def ofHex (s : String) : Bytes := ofHexL s.toList
def hc (a b : Bytes) : Bytes := hash256 (a ++ b)
def z32 : Bytes := List.replicate 32 0
-- string instantiation (zero = "")
-- empty list: uint256() and not mutated
#eval computeMerkleRoot sc "" [] == ("", false)
-- one element: the element itself, not mutated
#eval computeMerkleRoot sc "" ["x"] == ("x", false)
-- [a,b]
#eval computeMerkleRoot sc "" ["a", "b"] == ("(ab)", false)
-- [a,a]: equal pair at position 0 -> mutated
#eval computeMerkleRoot sc "" ["a", "a"] == ("(aa)", true)
-- [a,b,c]: c duplicated, not mutated
#eval computeMerkleRoot sc "" ["a", "b", "c"] == ("((ab)(cc))", false)
-- [a,b,c,c]: mutated (CVE-2012-2459 shape)
#eval computeMerkleRoot sc "" ["a", "b", "c", "c"] == ("((ab)(cc))", true)
-- [a,b,b]: equal pair at odd position (1,2) is not tested -> not mutated
#eval computeMerkleRoot sc "" ["a", "b", "b"] == ("((ab)(bb))", false)
-- [a,b,a,b]: level 0 clean, level 1 is [(ab),(ab)] -> mutated
#eval computeMerkleRoot sc "" ["a", "b", "a", "b"] == ("((ab)(ab))", true)
-- [a,b,c,d,e,f] (Core comment, undup'd)
#eval computeMerkleRoot sc "" ["a", "b", "c", "d", "e", "f"] == ("(((ab)(cd))((ef)(ef)))", false)
-- [a,b,c,d,e,f,e,f] (Core comment: same root, mutated)
#eval computeMerkleRoot sc "" ["a", "b", "c", "d", "e", "f", "e", "f"] == ("(((ab)(cd))((ef)(ef)))", true)
-- five elements: e duplicated at level 0, (ee) duplicated at level 1
#eval computeMerkleRoot sc "" ["a", "b", "c", "d", "e"] == ("(((ab)(cd))((ee)(ee)))", false)
-- seven elements: g duplicated at level 0, (gg) duplicated at level 1
#eval computeMerkleRoot sc "" ["a", "b", "c", "d", "e", "f", "g"] == ("(((ab)(cd))((ef)(gg)))", false)
-- [a,b,c,d,e,e]: equal pair at position 4 -> mutated
#eval computeMerkleRoot sc "" ["a", "b", "c", "d", "e", "e"] == ("(((ab)(cd))((ee)(ee)))", true)
-- [a,a,b]: equal pair at position 0 of an odd level -> mutated
#eval computeMerkleRoot sc "" ["a", "a", "b"] == ("((aa)(bb))", true)
-- [a,b,c,a,b,c]: no aligned equal pair at any level
#eval computeMerkleRoot sc "" ["a", "b", "c", "a", "b", "c"] == ("(((ab)(ca))((bc)(bc)))", false)
-- CVE-2012-2459: the two lists share the root and differ only in the flag
#eval (computeMerkleRoot sc "" ["a", "b", "c", "d", "e", "f"]).1 == (computeMerkleRoot sc "" ["a", "b", "c", "d", "e", "f", "e", "f"]).1
-- pairUp / hasEqualPair on their own
#eval pairUp sc ["a", "b", "c"] == ["(ab)", "(cc)"]
#eval pairUp sc ["a", "b", "c", "d"] == ["(ab)", "(cd)"]
#eval pairUp sc ["a"] == ["(aa)"]
#eval pairUp sc ([] : List String) == []
#eval hasEqualPair ["a", "b", "b"] == false
#eval hasEqualPair ["a", "a", "b"] == true
#eval hasEqualPair ["a", "b", "c", "c"] == true
#eval hasEqualPair ["a"] == false
#eval hasEqualPair ([] : List String) == false
-- double-SHA256 instantiation over 32-byte leaves (zero = 32 zero bytes)
-- 1 distinct 32-byte leaves
#eval computeMerkleRoot hc z32 [ofHex "0101010101010101010101010101010101010101010101010101010101010101"] == (ofHex "0101010101010101010101010101010101010101010101010101010101010101", false)
-- 2 distinct 32-byte leaves
#eval computeMerkleRoot hc z32 [ofHex "0101010101010101010101010101010101010101010101010101010101010101", ofHex "0202020202020202020202020202020202020202020202020202020202020202"] == (ofHex "39ce20bede82c96b8908bec4a157b09c549b3db90b9b474bda9ae9b9030310b4", false)
-- 3 distinct 32-byte leaves
#eval computeMerkleRoot hc z32 [ofHex "0101010101010101010101010101010101010101010101010101010101010101", ofHex "0202020202020202020202020202020202020202020202020202020202020202", ofHex "0303030303030303030303030303030303030303030303030303030303030303"] == (ofHex "223e023fadf1f053df26988871f893c821c28edf77d64a955e6c2a02d547bdac", false)
-- 4 distinct 32-byte leaves
#eval computeMerkleRoot hc z32 [ofHex "0101010101010101010101010101010101010101010101010101010101010101", ofHex "0202020202020202020202020202020202020202020202020202020202020202", ofHex "0303030303030303030303030303030303030303030303030303030303030303", ofHex "0404040404040404040404040404040404040404040404040404040404040404"] == (ofHex "085aabaef98668701b87c9a1986bdf116726a9949802326b69895697d4e8c812", false)
-- 5 distinct 32-byte leaves
#eval computeMerkleRoot hc z32 [ofHex "0101010101010101010101010101010101010101010101010101010101010101", ofHex "0202020202020202020202020202020202020202020202020202020202020202", ofHex "0303030303030303030303030303030303030303030303030303030303030303", ofHex "0404040404040404040404040404040404040404040404040404040404040404", ofHex "0505050505050505050505050505050505050505050505050505050505050505"] == (ofHex "26e2870f72368b3f8baef83fa26282d95d9c194e1f33d90a12932e0f6022e5d3", false)
-- 6 distinct 32-byte leaves
#eval computeMerkleRoot hc z32 [ofHex "0101010101010101010101010101010101010101010101010101010101010101", ofHex "0202020202020202020202020202020202020202020202020202020202020202", ofHex "0303030303030303030303030303030303030303030303030303030303030303", ofHex "0404040404040404040404040404040404040404040404040404040404040404", ofHex "0505050505050505050505050505050505050505050505050505050505050505", ofHex "0606060606060606060606060606060606060606060606060606060606060606"] == (ofHex "7b66d521a8037fd37d8730a5a77b304c0994bf45fc6e225cb79073f087cf97e9", false)
-- 7 distinct 32-byte leaves
#eval computeMerkleRoot hc z32 [ofHex "0101010101010101010101010101010101010101010101010101010101010101", ofHex "0202020202020202020202020202020202020202020202020202020202020202", ofHex "0303030303030303030303030303030303030303030303030303030303030303", ofHex "0404040404040404040404040404040404040404040404040404040404040404", ofHex "0505050505050505050505050505050505050505050505050505050505050505", ofHex "0606060606060606060606060606060606060606060606060606060606060606", ofHex "0707070707070707070707070707070707070707070707070707070707070707"] == (ofHex "5cda317f9f94e784d7811b9b9884f3082f0baafc8a93a7db6f95f57ea52e9269", false)
-- 8 distinct 32-byte leaves
#eval computeMerkleRoot hc z32 [ofHex "0101010101010101010101010101010101010101010101010101010101010101", ofHex "0202020202020202020202020202020202020202020202020202020202020202", ofHex "0303030303030303030303030303030303030303030303030303030303030303", ofHex "0404040404040404040404040404040404040404040404040404040404040404", ofHex "0505050505050505050505050505050505050505050505050505050505050505", ofHex "0606060606060606060606060606060606060606060606060606060606060606", ofHex "0707070707070707070707070707070707070707070707070707070707070707", ofHex "0808080808080808080808080808080808080808080808080808080808080808"] == (ofHex "c1105948cfffba7d4dcf98de63a5eb1e4bd9c0ae1ff9dfcf0f34b9ad7eb758fc", false)
-- 4 leaves with the last duplicated (mutated)
#eval computeMerkleRoot hc z32 [ofHex "0101010101010101010101010101010101010101010101010101010101010101", ofHex "0202020202020202020202020202020202020202020202020202020202020202", ofHex "0303030303030303030303030303030303030303030303030303030303030303", ofHex "0303030303030303030303030303030303030303030303030303030303030303"] == (ofHex "223e023fadf1f053df26988871f893c821c28edf77d64a955e6c2a02d547bdac", true)
-- [1,2,3,4,5,6,5,6] (mutated, same root as 6 leaves)
#eval computeMerkleRoot hc z32 [ofHex "0101010101010101010101010101010101010101010101010101010101010101", ofHex "0202020202020202020202020202020202020202020202020202020202020202", ofHex "0303030303030303030303030303030303030303030303030303030303030303", ofHex "0404040404040404040404040404040404040404040404040404040404040404", ofHex "0505050505050505050505050505050505050505050505050505050505050505", ofHex "0606060606060606060606060606060606060606060606060606060606060606", ofHex "0505050505050505050505050505050505050505050505050505050505050505", ofHex "0606060606060606060606060606060606060606060606060606060606060606"] == (ofHex "7b66d521a8037fd37d8730a5a77b304c0994bf45fc6e225cb79073f087cf97e9", true)
-- empty byte list gives the zero hash
#eval computeMerkleRoot hc z32 ([] : List Bytes) == (z32, false)
