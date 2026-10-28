# Spot 22: `ComputeMerkleRoot` versus `BitcoinMerkle.computeMerkleRoot`, `rootLoop`, `pairUp`, `hasEqualPair`

Core: [`consensus/merkle.cpp:47`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/merkle.cpp#L47)
(`ComputeMerkleRoot`), [`crypto/sha256.cpp:749`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/crypto/sha256.cpp#L749)
(`SHA256D64`), [`crypto/sha256.cpp:185`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/crypto/sha256.cpp#L185)
and [`:442`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/crypto/sha256.cpp#L442)
(`TransformD64`, `TransformD64Wrapper`: SHA-256 of a 64-byte block followed by SHA-256 of the
32-byte digest, i.e. double SHA-256 of the concatenated pair).

Lean: `Definitions/Def_BitcoinMerkle.lean` (52 lines): `pairUp`, `hasEqualPair`, `pairUp_length`,
`rootLoop`, `computeMerkleRoot`. The instantiation `BitcoinBlockV2.blockMerkleRoot =
computeMerkleRoot merkleCombine zeroHash (vtx.map txid)` with `merkleCombine a b = hash256 (a ++ b)`
and `zeroHash = 32 zero bytes` was reviewed in `REVIEW_SPOT12.md`; this spot is the generic loop.

## Verdict

No defect. The generic loop is a faithful transcription of `ComputeMerkleRoot` with a non-null
`mutated` pointer: the loop runs exactly while more than one hash remains; at every level the
aligned pairs `(pos, pos+1)` with `pos` even and `pos + 1 < size` are tested for equality *before*
the odd-length duplication (so the duplicated trailing element is never compared, and an equal pair
at an odd position is not detected); an odd level duplicates its last element; adjacent pairs are
combined with the earlier element first; the flag is sticky across levels; the empty list gives the
zero value and a one-element list gives that element unhashed with the flag clear. The read-back
(`scratchpad/audit4/readback_Def_BitcoinMerkle.md`), written blind, states exactly these properties
(in particular "it does not test any non-aligned adjacent pair such as (1,2)" and "a singleton input
is returned unchanged in its first component, not as c(a,a)"), which match the C++ as read. The only
difference is that Core skips the equality scan when `mutated == nullptr`
(`BlockWitnessMerkleRoot` passes `nullptr`); the Lean always computes the flag and the caller
drops it with `.1`, which cannot change any verdict.

## `ComputeMerkleRoot(hashes, mutated)` — `computeMerkleRoot c z hs`

Core (`merkle.cpp:47-70`), line by line:

1. `mutation = false`.
2. `while (hashes.size() > 1)`:
   a. if `mutated` is non-null: `for (pos = 0; pos + 1 < size; pos += 2) if (hashes[pos] ==
      hashes[pos+1]) mutation = true;` — positions 0, 2, 4, …; the last element of an odd-length
      level has no partner `pos + 1 < size` and is not compared; the scan continues after a hit
      (no effect on the result).
   b. `if (size & 1) hashes.push_back(hashes.back())` — duplicate the last element.
   c. `SHA256D64(out = hashes[0], in = hashes[0], size/2)` then `resize(size/2)` — each 64-byte
      adjacent pair `(hashes[2i], hashes[2i+1])` becomes one 32-byte double-SHA-256 digest; the
      in-place write is safe because output `i` occupies bytes `[32i, 32i+32)` which input pair
      `i` at `[64i, 64i+64)` has already been consumed from (`TransformD64` reads all of `in`
      before writing `out`).
3. `if (mutated) *mutated = mutation`.
4. `if (size == 0) return uint256()` (all zero); else `return hashes[0]`.

Lean:

- `computeMerkleRoot c z hs = rootLoop c z hs false` — step 1.
- `rootLoop c z hs mutation = if 1 < hs.length then rootLoop c z (pairUp c hs) (mutation ||
  hasEqualPair hs) else (hs.headD z, mutation)` — step 2's guard (`size > 1` ↔ `1 < length`); the
  flag is OR-ed with the scan of the *current* level `hs` before pairing (2a before 2b/2c); step 4
  is `headD z`: on exit `hs.length ≤ 1`, so this is `z` for the empty list and the single element
  otherwise.
- `hasEqualPair (a :: b :: rest) = decide (a = b) || hasEqualPair rest`, `hasEqualPair [_] =
  hasEqualPair [] = false` — step 2a: it consumes the list two at a time, so it compares exactly
  positions `(0,1), (2,3), …`, and a trailing singleton is dropped, exactly `pos + 1 < size`.
- `pairUp c (a :: b :: rest) = c a b :: pairUp c rest`, `pairUp c [a] = [c a a]`, `pairUp c [] = []`
  — steps 2b and 2c fused: the trailing element of an odd level is combined with itself, which is
  `push_back(back())` followed by hashing the pair; `c` receives the earlier element first, as
  `SHA256D64` reads the 64 bytes in order. `pairUp_length` gives `⌈n/2⌉ = (n+1)/2`, which is
  `size/2` after the duplication, and is what makes the loop terminate (Core relies on the same
  fact).
- With `c = merkleCombine = hash256 (a ++ b)` the combine is `SHA256D64` (`sha256.cpp:442-470`:
  one compression of the 64 input bytes with the standard padding for a 512-bit message, then one
  compression of the 32-byte digest with padding for a 256-bit message = `SHA256(SHA256(a‖b))`);
  with `z = zeroHash` the empty case is `uint256()`.

The one-element input: Core's loop body never runs, so `hashes[0]` is the leaf itself, not
`SHA256D64(leaf‖leaf)`; the Lean returns `hs.headD z = a` without calling `pairUp`. Same.

## Vectors

`tests/MerkleVectors.lean` (36 `#eval` lines, all `true`), generated by
`tests/reference/merkle_reference.py`, which transcribes the C++ loop parametrically in the pair
function and the zero. Hand-checkable cases use the injective string combine `sc a b = "(" ++ a ++
b ++ ")"` with zero `""`, so the root spells the tree: `[] → ("", false)`; `[x] → ("x", false)`;
`[a,b] → "(ab)"`; `[a,a] → "(aa)", mutated`; `[a,b,c] → "((ab)(cc))", not mutated`; `[a,b,c,c]`
same root, mutated; `[a,b,b] → "((ab)(bb))", not mutated` (the equal pair is at odd position
(1,2)); `[a,b,a,b] → "((ab)(ab))", mutated` only at level 1; `[a,b,c,d,e,f]` and
`[a,b,c,d,e,f,e,f]` both `"(((ab)(cd))((ef)(ef)))"`, the first clean and the second mutated (the
CVE-2012-2459 example in Core's comment, with an explicit line asserting the two roots are equal);
five elements `"(((ab)(cd))((ee)(ee)))"` (duplication at two levels, not mutated); seven elements
`"(((ab)(cd))((ef)(gg)))"` (duplication at two levels, not mutated); `[a,b,c,d,e,e]` mutated at
position 4; `[a,a,b]` mutated at position 0 of an odd level; `[a,b,c,a,b,c]` clean. `pairUp` and
`hasEqualPair` are also exercised on their own. The double-SHA-256 instantiation
`hc a b = hash256 (a ++ b)`, zero = 32 zero bytes, is checked against Python `hashlib` for 1..8
distinct 32-byte leaves (`bytes([i]*32)`), for `[1,2,3,3]` (mutated, same root as `[1,2,3]`),
for `[1,2,3,4,5,6,5,6]` (mutated, same root as six leaves) and for the empty list.

Run: `lake env lean tests/MerkleVectors.lean | sort | uniq -c` → `36 true`.

## Checks from the guide

- **Order of tests.** The equality scan precedes the duplication in Core and in the Lean (`hasEqualPair
  hs` is evaluated on the pre-`pairUp` level); this is the one order that matters, because scanning
  after duplication would flag every odd level. The loop guard and the exit cases are in the same
  order (empty → zero, singleton → element).
- **Constants.** No numeric constants in the generic loop; the pair width (two) and the position
  parity (even) match. `uint256()` and `SHA256D64` are the parameters `z` and `c`, instantiated
  correctly in `Def_BitcoinBlockV2` (spot 12).
- **Integer semantics.** `size_t` positions and `size/2` with `size` even after duplication; the Lean
  uses list pattern matching, no arithmetic on indices, and `pairUp_length` is `(n+1)/2`. No
  subtraction, no overflow.
- **Defaults.** `hs.headD z` is read only when the loop has exited with `hs = []`, which happens
  exactly for empty input (a non-empty list never becomes empty under `pairUp`); Core returns
  `uint256()` there. Reachable and identical. `hasEqualPair` and `pairUp` have no defaults.
- **Policy vs consensus.** `ComputeMerkleRoot` is consensus (the mutation flag decides
  `bad-txns-duplicate` in `CheckBlock`). The `mutated == nullptr` fast path is a performance
  choice for callers that ignore the flag; the Lean computing it unconditionally is harmless.
