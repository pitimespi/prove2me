"""Independent reference for spot 22 (REVIEW_SPOT22.md): the generic ComputeMerkleRoot loop of
consensus/merkle.cpp (Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48), written from the C++
only. Emits tests/MerkleVectors.lean.

ComputeMerkleRoot(hashes, mutated):
    mutation = false
    while (hashes.size() > 1):
        for (pos = 0; pos + 1 < size; pos += 2): if hashes[pos] == hashes[pos+1]: mutation = true
        if (size & 1): hashes.push_back(hashes.back())
        SHA256D64 over adjacent pairs; resize to size/2
    *mutated = mutation
    if size == 0: return uint256()   (all zero)
    return hashes[0]

The loop is parametric here in the pair function `combine` and the empty-list value `zero` so that
the hand-checkable vectors use an injective string combine "(" + a + b + ")" (so the root spells
the tree) and the hashed vectors use real double SHA-256 of the 64-byte concatenation, which is
what SHA256D64 computes (crypto/sha256.cpp: TransformD64 = SHA-256 of 64 bytes followed by
SHA-256 of the 32-byte digest).

Usage: python3 -I merkle_reference.py OUT_LEAN
"""
import hashlib, sys


def sha256d(b):
    return hashlib.sha256(hashlib.sha256(b).digest()).digest()


def compute_merkle_root(hashes, combine, zero):
    """Line-by-line transcription of ComputeMerkleRoot with a non-null `mutated` pointer."""
    hashes = list(hashes)
    mutation = False
    while len(hashes) > 1:
        pos = 0
        while pos + 1 < len(hashes):
            if hashes[pos] == hashes[pos + 1]:
                mutation = True
            pos += 2
        if len(hashes) & 1:
            hashes.append(hashes[-1])
        hashes = [combine(hashes[i], hashes[i + 1]) for i in range(0, len(hashes), 2)]
    if len(hashes) == 0:
        return zero, mutation
    return hashes[0], mutation


# --- hand-checkable string instantiation -------------------------------------------------------
def scomb(a, b):
    return "(" + a + b + ")"


string_cases = [
    ("empty list: uint256() and not mutated", []),
    ("one element: the element itself, not mutated", ["x"]),
    ("[a,b]", ["a", "b"]),
    ("[a,a]: equal pair at position 0 -> mutated", ["a", "a"]),
    ("[a,b,c]: c duplicated, not mutated", ["a", "b", "c"]),
    ("[a,b,c,c]: mutated (CVE-2012-2459 shape)", ["a", "b", "c", "c"]),
    ("[a,b,b]: equal pair at odd position (1,2) is not tested -> not mutated", ["a", "b", "b"]),
    ("[a,b,a,b]: level 0 clean, level 1 is [(ab),(ab)] -> mutated", ["a", "b", "a", "b"]),
    ("[a,b,c,d,e,f] (Core comment, undup'd)", ["a", "b", "c", "d", "e", "f"]),
    ("[a,b,c,d,e,f,e,f] (Core comment: same root, mutated)", ["a", "b", "c", "d", "e", "f", "e", "f"]),
    ("five elements: e duplicated at level 0, (ee) duplicated at level 1", ["a", "b", "c", "d", "e"]),
    ("seven elements: g duplicated at level 0, (gg) duplicated at level 1", ["a", "b", "c", "d", "e", "f", "g"]),
    ("[a,b,c,d,e,e]: equal pair at position 4 -> mutated", ["a", "b", "c", "d", "e", "e"]),
    ("[a,a,b]: equal pair at position 0 of an odd level -> mutated", ["a", "a", "b"]),
    ("[a,b,c,a,b,c]: no aligned equal pair at any level", ["a", "b", "c", "a", "b", "c"]),
]

# --- real double-SHA256 instantiation over 32-byte leaves -----------------------------------------
def leaf(i):
    return bytes([i] * 32)


def hcomb(a, b):
    return sha256d(a + b)


hash_cases = []
for n in range(1, 9):
    hash_cases.append((f"{n} distinct 32-byte leaves", [leaf(i) for i in range(1, n + 1)]))
hash_cases.append(("4 leaves with the last duplicated (mutated)", [leaf(1), leaf(2), leaf(3), leaf(3)]))
hash_cases.append(("[1,2,3,4,5,6,5,6] (mutated, same root as 6 leaves)", [leaf(i) for i in (1, 2, 3, 4, 5, 6, 5, 6)]))


def lean_str_list(xs):
    return "[" + ", ".join('"' + x + '"' for x in xs) + "]"


def lean_bytes_list(xs):
    return "[" + ", ".join("ofHex \"" + x.hex() + "\"" for x in xs) + "]"


def main(out):
    lines = []
    lines.append("import Definitions.Def_BitcoinMerkle")
    lines.append("import Definitions.Def_BitcoinSer")
    lines.append("open BitcoinMerkle BitcoinSer")
    lines.append("/-! Spot 22 vectors (`REVIEW_SPOT22.md`): the generic `ComputeMerkleRoot` loop (`consensus/merkle.cpp`)")
    lines.append("with its CVE-2012-2459 mutation flag, instantiated with an injective string combine `(ab)` for hand-checkable")
    lines.append("cases and with real double SHA-256 over 32-byte leaves. Expectations computed by")
    lines.append("`tests/reference/merkle_reference.py`. Every line prints `true`. -/")
    lines.append('def sc (a b : String) : String := "(" ++ a ++ b ++ ")"')
    lines.append("def hexVal (c : Char) : Nat := if c.isDigit then c.toNat - 48 else c.toLower.toNat - 87")
    lines.append("def ofHexL : List Char → Bytes")
    lines.append("  | a :: b :: r => BitVec.ofNat 8 (hexVal a * 16 + hexVal b) :: ofHexL r")
    lines.append("  | _ => []")
    lines.append("def ofHex (s : String) : Bytes := ofHexL s.toList")
    lines.append("def hc (a b : Bytes) : Bytes := hash256 (a ++ b)")
    lines.append("def z32 : Bytes := List.replicate 32 0")
    lines.append("-- string instantiation (zero = \"\")")
    for desc, xs in string_cases:
        root, mut = compute_merkle_root(xs, scomb, "")
        lines.append(f"-- {desc}")
        lines.append(f'#eval computeMerkleRoot sc "" {lean_str_list(xs)} == ("{root}", {str(mut).lower()})')
    # the CVE pair: same root, different flag
    r6, m6 = compute_merkle_root(string_cases[8][1], scomb, "")
    r8, m8 = compute_merkle_root(string_cases[9][1], scomb, "")
    assert r6 == r8 and not m6 and m8
    lines.append("-- CVE-2012-2459: the two lists share the root and differ only in the flag")
    lines.append(f'#eval (computeMerkleRoot sc "" {lean_str_list(string_cases[8][1])}).1 == (computeMerkleRoot sc "" {lean_str_list(string_cases[9][1])}).1')
    lines.append("-- pairUp / hasEqualPair on their own")
    lines.append('#eval pairUp sc ["a", "b", "c"] == ["(ab)", "(cc)"]')
    lines.append('#eval pairUp sc ["a", "b", "c", "d"] == ["(ab)", "(cd)"]')
    lines.append('#eval pairUp sc ["a"] == ["(aa)"]')
    lines.append('#eval pairUp sc ([] : List String) == []')
    lines.append('#eval hasEqualPair ["a", "b", "b"] == false')
    lines.append('#eval hasEqualPair ["a", "a", "b"] == true')
    lines.append('#eval hasEqualPair ["a", "b", "c", "c"] == true')
    lines.append('#eval hasEqualPair ["a"] == false')
    lines.append('#eval hasEqualPair ([] : List String) == false')
    lines.append("-- double-SHA256 instantiation over 32-byte leaves (zero = 32 zero bytes)")
    for desc, xs in hash_cases:
        root, mut = compute_merkle_root(xs, hcomb, bytes(32))
        lines.append(f"-- {desc}")
        lines.append(f'#eval computeMerkleRoot hc z32 {lean_bytes_list(xs)} == (ofHex "{root.hex()}", {str(mut).lower()})')
    lines.append("-- empty byte list gives the zero hash")
    lines.append('#eval computeMerkleRoot hc z32 ([] : List Bytes) == (z32, false)')
    with open(out, "w") as f:
        f.write("\n".join(lines) + "\n")
    for desc, xs in string_cases:
        print(desc, "->", compute_merkle_root(xs, scomb, ""))
    for desc, xs in hash_cases:
        r, m = compute_merkle_root(xs, hcomb, bytes(32))
        print(desc, "->", r.hex(), m)


if __name__ == "__main__":
    main(sys.argv[1])
