"""Independent reference for spot 20 (REVIEW_SPOT20.md): CalculateSequenceLocks,
EvaluateSequenceLocks and SequenceLocks (consensus/tx_verify.cpp:45..115) with the CTxIn
constants of primitives/transaction.h, written from the C++ without looking at the Lean.
Emits tests/Bip68Vectors.lean.

Interface adaptation: Core takes the CBlockIndex of the block being validated and reads
`block.GetAncestor(h)->GetMedianTimePast()` and `block.pprev->GetMedianTimePast()`; the Lean
takes a `Context ⟨height, mtp⟩` with `mtp : Nat → Nat` the chain's MTP at a height, and a list
of `⟨sequence, coinHeight⟩` inputs (the prevHeights vector, zipped with the sequences). The
reference therefore takes the same inputs: a block height, an MTP table indexed by height, and
(nSequence, coin height) pairs. Core's prevHeights is an in/out vector: the returned heights are
checked through the Lean's `returnedHeights`.

Usage: python3 -I bip68_reference.py OUT_LEAN
"""
import sys

# primitives/transaction.h
SEQUENCE_LOCKTIME_DISABLE_FLAG = 1 << 31
SEQUENCE_LOCKTIME_TYPE_FLAG = 1 << 22
SEQUENCE_LOCKTIME_MASK = 0x0000ffff
SEQUENCE_LOCKTIME_GRANULARITY = 9
LOCKTIME_VERIFY_SEQUENCE = 1 << 0     # consensus/consensus.h
U32 = 0xffffffff

def calculate(version, flags, inputs, block_height, mtp):
    """inputs: list of (nSequence, coin height); returns ((nMinHeight, nMinTime), prevHeights after)."""
    prev = [h for (_, h) in inputs]
    nMinHeight, nMinTime = -1, -1
    fEnforceBIP68 = (version & U32) >= 2 and (flags & LOCKTIME_VERIFY_SEQUENCE) != 0
    if not fEnforceBIP68:
        return (nMinHeight, nMinTime), prev
    for i, (nSequence, _) in enumerate(inputs):
        nSequence &= U32
        if nSequence & SEQUENCE_LOCKTIME_DISABLE_FLAG:
            prev[i] = 0
            continue
        nCoinHeight = prev[i]
        if nSequence & SEQUENCE_LOCKTIME_TYPE_FLAG:
            anc = max(nCoinHeight - 1, 0)
            assert 0 <= anc <= block_height          # GetAncestor would return nullptr otherwise (Assert)
            nCoinTime = mtp(anc)
            nMinTime = max(nMinTime, nCoinTime + ((nSequence & SEQUENCE_LOCKTIME_MASK) << SEQUENCE_LOCKTIME_GRANULARITY) - 1)
        else:
            nMinHeight = max(nMinHeight, nCoinHeight + (nSequence & SEQUENCE_LOCKTIME_MASK) - 1)
    return (nMinHeight, nMinTime), prev

def evaluate(block_height, mtp, lock_pair):
    """tx_verify.cpp:105: nBlockTime = block.pprev->GetMedianTimePast()."""
    assert block_height >= 1                             # assert(block.pprev)
    nBlockTime = mtp(block_height - 1)
    if lock_pair[0] >= block_height or lock_pair[1] >= nBlockTime:
        return False
    return True

def sequence_locks(version, flags, inputs, block_height, mtp):
    pair, _ = calculate(version, flags, inputs, block_height, mtp)
    return evaluate(block_height, mtp, pair)

# --- an MTP table: strictly increasing, 600 s per block, chosen so arithmetic is visible ---
MTP = [1_000_000 + 600 * h for h in range(0, 41)]
def mtp(h): return MTP[h]
H = 20                                   # the block being validated; pprev MTP = MTP[19]

def lb(b): return "true" if b else "false"
def seq_lit(s): return f"(BitVec.ofNat 32 {s:#x})"
def inputs_lit(inputs): return "[" + ", ".join(f"⟨{seq_lit(s)}, {h}⟩" for s, h in inputs) + "]"
def acc_lit(pair, prev): return f"⟨{pair[0]}, {pair[1]}, {list(reversed(prev))}⟩"

out = []
out.append("import Definitions.Def_BIP68_Core")
out.append("open BitcoinBIP68")
out.append("/-! Spot 20 vectors (`REVIEW_SPOT20.md`): `CalculateSequenceLocks`, `EvaluateSequenceLocks` and")
out.append("`SequenceLocks` on hand-chosen inputs. Expectations computed by `tests/reference/bip68_reference.py`.")
out.append("The `Context` is a block height `H` and the chain's MTP table; `mtp h` is the MTP of the block at")
out.append("height `h`, so `mtp (H - 1)` is `pprev->GetMedianTimePast()`. Every line prints `true`. -/")
out.append(f"def mtpTab : List Nat := {MTP}")
out.append(f"def ctx : Context := ⟨{H}, fun h => mtpTab.getD h 0⟩")
out.append("def ctxAt (height : Nat) : Context := ⟨height, fun h => mtpTab.getD h 0⟩")

V2, V1, FL = 2, 1, LOCKTIME_VERIFY_SEQUENCE
DIS, TYP = SEQUENCE_LOCKTIME_DISABLE_FLAG, SEQUENCE_LOCKTIME_TYPE_FLAG

def case(label, version, flags, inputs, height=H):
    pair, prev = calculate(version, flags, inputs, height, mtp)
    ok = sequence_locks(version, flags, inputs, height, mtp)
    c = "ctx" if height == H else f"(ctxAt {height})"
    out.append(f"-- {label}")
    out.append(f"#eval calculate {seq_lit(version)} {seq_lit(flags)} {c} {inputs_lit(inputs)} == {acc_lit(pair, prev)}")
    out.append(f"#eval returnedHeights (calculate {seq_lit(version)} {seq_lit(flags)} {c} {inputs_lit(inputs)}) == {prev}")
    out.append(f"#eval sequenceLocks {seq_lit(version)} {seq_lit(flags)} {c} {inputs_lit(inputs)} == {lb(ok)}")

out.append("-- constants / predicates")
out.append(f"#eval coreDisabled {seq_lit(DIS)} == true")
out.append(f"#eval coreDisabled {seq_lit(DIS - 1)} == false")
out.append(f"#eval coreTimeBased {seq_lit(TYP)} == true")
out.append(f"#eval coreTimeBased {seq_lit(TYP - 1)} == false")
out.append(f"#eval coreDelay {seq_lit(0xffffffff)} == 65535")
out.append(f"#eval coreDelay {seq_lit(0xffff0000)} == 0")
out.append(f"#eval coreSeconds {seq_lit(TYP | 0xffff)} == {0xffff << 9}")
out.append(f"#eval coreSeconds {seq_lit(TYP | 1)} == 512")
for v, f, e in [(2, 1, True), (1, 1, False), (0, 1, False), (2, 0, False), (2, 2, False), (2, 3, True),
                (3, 1, True), (0xffffffff, 1, True), (0x80000000, 1, True), (2, 0xffffffff, True)]:
    out.append(f"#eval coreEnabled {seq_lit(v)} {seq_lit(f)} == {lb(e)}")

case("empty input list", V2, FL, [])
case("disabled flag: minima untouched, height reported as 0", V2, FL, [(DIS | 5, 10)])
case("disabled flag with the type flag and a huge delay: still ignored", V2, FL, [(DIS | TYP | 0xffff, 19)])
case("version 1: not enforced, heights unchanged even with the disable flag", V1, FL, [(DIS | 5, 10), (0xffff, 19)])
case("version 2 but flags 0: not enforced", V2, 0, [(0xffff, 19)])
case("version 2, flags with only other bits: not enforced", V2, 2, [(0xffff, 19)])
case("version 0xffffffff (unsigned): enforced", 0xffffffff, FL, [(1, 20)])
case("height lock, mask 0: nMinHeight = coin - 1", V2, FL, [(0, 10)])
case("height lock, mask 0 on a coin at height 0: nMinHeight = -1", V2, FL, [(0, 0)])
case("height lock, mask 1: nMinHeight = coin height; coin at H-1 passes", V2, FL, [(1, H - 1)])
case("height lock, mask 1: coin at H gives nMinHeight = H, fails at the boundary", V2, FL, [(1, H)])
case("height lock, mask 0xffff: coin + 65534", V2, FL, [(0xffff, 3)])
case("height lock, mask 0xffff on coin 0: 65534", V2, FL, [(0xffff, 0)])
case("height lock exact boundary: coin 10 + 10 - 1 = 19 < 20 passes", V2, FL, [(10, 10)])
case("height lock exact boundary: coin 10 + 11 - 1 = 20 >= 20 fails", V2, FL, [(11, 10)])
case("time lock, 1 unit from coin at height 5: mtp(4) + 512 - 1", V2, FL, [(TYP | 1, 5)])
case("time lock, 0 units: mtp(coin-1) - 1", V2, FL, [(TYP, 5)])
case("time lock, coin at height 0 uses the ancestor at max(-1,0) = 0", V2, FL, [(TYP | 2, 0)])
case("time lock, coin at height 1 uses the ancestor at 0 too", V2, FL, [(TYP | 2, 1)])
case("time lock, coin at height 2 uses the ancestor at 1", V2, FL, [(TYP | 2, 2)])
case("time lock, mask 0xffff", V2, FL, [(TYP | 0xffff, 1)])
# pprev MTP = MTP[19] = MTP[0] + 19*600 = 11400 s above MTP[0]. 11400 = 22*512 + 136.
# coin at height 1 -> ancestor 0: nMinTime = MTP[0] + 512 n - 1; fails iff >= MTP[19], i.e. n >= 23 (512*23 - 1 = 11775 >= 11400).
case("time lock just below the boundary: 22 units from MTP[0] (11263 < 11400) passes", V2, FL, [(TYP | 22, 1)])
case("time lock past the boundary: 23 units from MTP[0] (11775 >= 11400) fails", V2, FL, [(TYP | 23, 1)])
# exact equality: coin at height 2 -> ancestor 1: MTP[1] = MTP[0]+600; MTP[19]-MTP[1] = 10800 = 21*512 + 48. Not exact.
# Build an exact case with a height where (MTP[H-1] - MTP[anc] + 1) is a multiple of 512:
# anc = 0, need 600*(H-1) + 1 = 512 n: 600*(H-1) ≡ 511 (mod 512) → 88*(H-1) ≡ 511 (mod 512); 88 = 8*11 and 511 odd: impossible.
# So instead test evaluate directly at the exact boundary (below).
case("mixed inputs: the max height lock and the max time lock, each separately", V2, FL,
     [(3, 10), (7, 5), (TYP | 4, 6), (TYP | 1, 15), (DIS | 0xffff, 18)])
case("mixed inputs where the later input is not the max", V2, FL, [(0xffff, 2), (1, 19)])
case("bits 16..21 and 23..30 set, bit 22 clear: height lock 7, the garbage bits are ignored", V2, FL, [(0x7fbf0000 | 7, 10)])
case("bits 16..21 and 23..30 set, bit 22 set: time lock 7 units", V2, FL, [(0x7fff0000 | 7, 10)])
case("bit 31 set with everything else set: disabled", V2, FL, [(0xffffffff, 10)])
case("bit 31 clear with everything else set: time lock 0xffff from the coin's ancestor", V2, FL, [(0x7fffffff, 10)])
case("intra-block spend: coin at the block's own height H with mask 1 fails (H >= H)", V2, FL, [(1, H)])
case("intra-block spend: coin at H with mask 0 passes (H - 1 < H)", V2, FL, [(0, H)])
case("intra-block spend, time lock: ancestor H-1 is pprev, so even 0 units gives mtp(H-1) - 1 < mtp(H-1): passes", V2, FL, [(TYP, H)])
case("intra-block spend, time lock 1 unit: mtp(H-1) + 511 >= mtp(H-1): fails", V2, FL, [(TYP | 1, H)])
case("block height 1 (pprev = genesis), coin at 0, height lock 1", V2, FL, [(1, 0)], height=1)
case("block height 1, coin at 0, height lock 0 passes", V2, FL, [(0, 0)], height=1)

out.append("-- EvaluateSequenceLocks at the exact boundaries")
for first, second in [(H, -1), (H - 1, -1), (-1, MTP[H - 1]), (-1, MTP[H - 1] - 1), (H, MTP[H - 1]),
                      (H - 1, MTP[H - 1] - 1), (-1, -1), (0, 0), (H + 1, 0), (0, MTP[H - 1] + 1)]:
    out.append(f"#eval evaluate ctx ⟨{first}, {second}, []⟩ == {lb(evaluate(H, mtp, (first, second)))}")
out.append("-- evaluate at block height 1: nBlockTime = mtp 0")
for first, second in [(0, MTP[0] - 1), (1, MTP[0] - 1), (0, MTP[0])]:
    out.append(f"#eval evaluate (ctxAt 1) ⟨{first}, {second}, []⟩ == {lb(evaluate(1, mtp, (first, second)))}")

with open(sys.argv[1], "w") as f:
    f.write("\n".join(out) + "\n")
print(len([l for l in out if l.startswith("#eval")]), "vectors")
