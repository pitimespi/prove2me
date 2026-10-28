import Definitions.Def_BIP68_Core
open BitcoinBIP68
/-! Spot 20 vectors (`REVIEW_SPOT20.md`): `CalculateSequenceLocks`, `EvaluateSequenceLocks` and
`SequenceLocks` on hand-chosen inputs. Expectations computed by `tests/reference/bip68_reference.py`.
The `Context` is a block height `H` and the chain's MTP table; `mtp h` is the MTP of the block at
height `h`, so `mtp (H - 1)` is `pprev->GetMedianTimePast()`. Every line prints `true`. -/
def mtpTab : List Nat := [1000000, 1000600, 1001200, 1001800, 1002400, 1003000, 1003600, 1004200, 1004800, 1005400, 1006000, 1006600, 1007200, 1007800, 1008400, 1009000, 1009600, 1010200, 1010800, 1011400, 1012000, 1012600, 1013200, 1013800, 1014400, 1015000, 1015600, 1016200, 1016800, 1017400, 1018000, 1018600, 1019200, 1019800, 1020400, 1021000, 1021600, 1022200, 1022800, 1023400, 1024000]
def ctx : Context := ⟨20, fun h => mtpTab.getD h 0⟩
def ctxAt (height : Nat) : Context := ⟨height, fun h => mtpTab.getD h 0⟩
-- constants / predicates
#eval coreDisabled (BitVec.ofNat 32 0x80000000) == true
#eval coreDisabled (BitVec.ofNat 32 0x7fffffff) == false
#eval coreTimeBased (BitVec.ofNat 32 0x400000) == true
#eval coreTimeBased (BitVec.ofNat 32 0x3fffff) == false
#eval coreDelay (BitVec.ofNat 32 0xffffffff) == 65535
#eval coreDelay (BitVec.ofNat 32 0xffff0000) == 0
#eval coreSeconds (BitVec.ofNat 32 0x40ffff) == 33553920
#eval coreSeconds (BitVec.ofNat 32 0x400001) == 512
#eval coreEnabled (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) == true
#eval coreEnabled (BitVec.ofNat 32 0x1) (BitVec.ofNat 32 0x1) == false
#eval coreEnabled (BitVec.ofNat 32 0x0) (BitVec.ofNat 32 0x1) == false
#eval coreEnabled (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x0) == false
#eval coreEnabled (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x2) == false
#eval coreEnabled (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x3) == true
#eval coreEnabled (BitVec.ofNat 32 0x3) (BitVec.ofNat 32 0x1) == true
#eval coreEnabled (BitVec.ofNat 32 0xffffffff) (BitVec.ofNat 32 0x1) == true
#eval coreEnabled (BitVec.ofNat 32 0x80000000) (BitVec.ofNat 32 0x1) == true
#eval coreEnabled (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0xffffffff) == true
-- empty input list
#eval calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [] == ⟨-1, -1, []⟩
#eval returnedHeights (calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx []) == []
#eval sequenceLocks (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [] == true
-- disabled flag: minima untouched, height reported as 0
#eval calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x80000005), 10⟩] == ⟨-1, -1, [0]⟩
#eval returnedHeights (calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x80000005), 10⟩]) == [0]
#eval sequenceLocks (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x80000005), 10⟩] == true
-- disabled flag with the type flag and a huge delay: still ignored
#eval calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x8040ffff), 19⟩] == ⟨-1, -1, [0]⟩
#eval returnedHeights (calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x8040ffff), 19⟩]) == [0]
#eval sequenceLocks (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x8040ffff), 19⟩] == true
-- version 1: not enforced, heights unchanged even with the disable flag
#eval calculate (BitVec.ofNat 32 0x1) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x80000005), 10⟩, ⟨(BitVec.ofNat 32 0xffff), 19⟩] == ⟨-1, -1, [19, 10]⟩
#eval returnedHeights (calculate (BitVec.ofNat 32 0x1) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x80000005), 10⟩, ⟨(BitVec.ofNat 32 0xffff), 19⟩]) == [10, 19]
#eval sequenceLocks (BitVec.ofNat 32 0x1) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x80000005), 10⟩, ⟨(BitVec.ofNat 32 0xffff), 19⟩] == true
-- version 2 but flags 0: not enforced
#eval calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x0) ctx [⟨(BitVec.ofNat 32 0xffff), 19⟩] == ⟨-1, -1, [19]⟩
#eval returnedHeights (calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x0) ctx [⟨(BitVec.ofNat 32 0xffff), 19⟩]) == [19]
#eval sequenceLocks (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x0) ctx [⟨(BitVec.ofNat 32 0xffff), 19⟩] == true
-- version 2, flags with only other bits: not enforced
#eval calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x2) ctx [⟨(BitVec.ofNat 32 0xffff), 19⟩] == ⟨-1, -1, [19]⟩
#eval returnedHeights (calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x2) ctx [⟨(BitVec.ofNat 32 0xffff), 19⟩]) == [19]
#eval sequenceLocks (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x2) ctx [⟨(BitVec.ofNat 32 0xffff), 19⟩] == true
-- version 0xffffffff (unsigned): enforced
#eval calculate (BitVec.ofNat 32 0xffffffff) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x1), 20⟩] == ⟨20, -1, [20]⟩
#eval returnedHeights (calculate (BitVec.ofNat 32 0xffffffff) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x1), 20⟩]) == [20]
#eval sequenceLocks (BitVec.ofNat 32 0xffffffff) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x1), 20⟩] == false
-- height lock, mask 0: nMinHeight = coin - 1
#eval calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x0), 10⟩] == ⟨9, -1, [10]⟩
#eval returnedHeights (calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x0), 10⟩]) == [10]
#eval sequenceLocks (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x0), 10⟩] == true
-- height lock, mask 0 on a coin at height 0: nMinHeight = -1
#eval calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x0), 0⟩] == ⟨-1, -1, [0]⟩
#eval returnedHeights (calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x0), 0⟩]) == [0]
#eval sequenceLocks (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x0), 0⟩] == true
-- height lock, mask 1: nMinHeight = coin height; coin at H-1 passes
#eval calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x1), 19⟩] == ⟨19, -1, [19]⟩
#eval returnedHeights (calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x1), 19⟩]) == [19]
#eval sequenceLocks (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x1), 19⟩] == true
-- height lock, mask 1: coin at H gives nMinHeight = H, fails at the boundary
#eval calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x1), 20⟩] == ⟨20, -1, [20]⟩
#eval returnedHeights (calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x1), 20⟩]) == [20]
#eval sequenceLocks (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x1), 20⟩] == false
-- height lock, mask 0xffff: coin + 65534
#eval calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0xffff), 3⟩] == ⟨65537, -1, [3]⟩
#eval returnedHeights (calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0xffff), 3⟩]) == [3]
#eval sequenceLocks (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0xffff), 3⟩] == false
-- height lock, mask 0xffff on coin 0: 65534
#eval calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0xffff), 0⟩] == ⟨65534, -1, [0]⟩
#eval returnedHeights (calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0xffff), 0⟩]) == [0]
#eval sequenceLocks (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0xffff), 0⟩] == false
-- height lock exact boundary: coin 10 + 10 - 1 = 19 < 20 passes
#eval calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0xa), 10⟩] == ⟨19, -1, [10]⟩
#eval returnedHeights (calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0xa), 10⟩]) == [10]
#eval sequenceLocks (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0xa), 10⟩] == true
-- height lock exact boundary: coin 10 + 11 - 1 = 20 >= 20 fails
#eval calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0xb), 10⟩] == ⟨20, -1, [10]⟩
#eval returnedHeights (calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0xb), 10⟩]) == [10]
#eval sequenceLocks (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0xb), 10⟩] == false
-- time lock, 1 unit from coin at height 5: mtp(4) + 512 - 1
#eval calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x400001), 5⟩] == ⟨-1, 1002911, [5]⟩
#eval returnedHeights (calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x400001), 5⟩]) == [5]
#eval sequenceLocks (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x400001), 5⟩] == true
-- time lock, 0 units: mtp(coin-1) - 1
#eval calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x400000), 5⟩] == ⟨-1, 1002399, [5]⟩
#eval returnedHeights (calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x400000), 5⟩]) == [5]
#eval sequenceLocks (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x400000), 5⟩] == true
-- time lock, coin at height 0 uses the ancestor at max(-1,0) = 0
#eval calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x400002), 0⟩] == ⟨-1, 1001023, [0]⟩
#eval returnedHeights (calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x400002), 0⟩]) == [0]
#eval sequenceLocks (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x400002), 0⟩] == true
-- time lock, coin at height 1 uses the ancestor at 0 too
#eval calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x400002), 1⟩] == ⟨-1, 1001023, [1]⟩
#eval returnedHeights (calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x400002), 1⟩]) == [1]
#eval sequenceLocks (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x400002), 1⟩] == true
-- time lock, coin at height 2 uses the ancestor at 1
#eval calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x400002), 2⟩] == ⟨-1, 1001623, [2]⟩
#eval returnedHeights (calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x400002), 2⟩]) == [2]
#eval sequenceLocks (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x400002), 2⟩] == true
-- time lock, mask 0xffff
#eval calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x40ffff), 1⟩] == ⟨-1, 34553919, [1]⟩
#eval returnedHeights (calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x40ffff), 1⟩]) == [1]
#eval sequenceLocks (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x40ffff), 1⟩] == false
-- time lock just below the boundary: 22 units from MTP[0] (11263 < 11400) passes
#eval calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x400016), 1⟩] == ⟨-1, 1011263, [1]⟩
#eval returnedHeights (calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x400016), 1⟩]) == [1]
#eval sequenceLocks (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x400016), 1⟩] == true
-- time lock past the boundary: 23 units from MTP[0] (11775 >= 11400) fails
#eval calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x400017), 1⟩] == ⟨-1, 1011775, [1]⟩
#eval returnedHeights (calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x400017), 1⟩]) == [1]
#eval sequenceLocks (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x400017), 1⟩] == false
-- mixed inputs: the max height lock and the max time lock, each separately
#eval calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x3), 10⟩, ⟨(BitVec.ofNat 32 0x7), 5⟩, ⟨(BitVec.ofNat 32 0x400004), 6⟩, ⟨(BitVec.ofNat 32 0x400001), 15⟩, ⟨(BitVec.ofNat 32 0x8000ffff), 18⟩] == ⟨12, 1008911, [0, 15, 6, 5, 10]⟩
#eval returnedHeights (calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x3), 10⟩, ⟨(BitVec.ofNat 32 0x7), 5⟩, ⟨(BitVec.ofNat 32 0x400004), 6⟩, ⟨(BitVec.ofNat 32 0x400001), 15⟩, ⟨(BitVec.ofNat 32 0x8000ffff), 18⟩]) == [10, 5, 6, 15, 0]
#eval sequenceLocks (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x3), 10⟩, ⟨(BitVec.ofNat 32 0x7), 5⟩, ⟨(BitVec.ofNat 32 0x400004), 6⟩, ⟨(BitVec.ofNat 32 0x400001), 15⟩, ⟨(BitVec.ofNat 32 0x8000ffff), 18⟩] == true
-- mixed inputs where the later input is not the max
#eval calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0xffff), 2⟩, ⟨(BitVec.ofNat 32 0x1), 19⟩] == ⟨65536, -1, [19, 2]⟩
#eval returnedHeights (calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0xffff), 2⟩, ⟨(BitVec.ofNat 32 0x1), 19⟩]) == [2, 19]
#eval sequenceLocks (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0xffff), 2⟩, ⟨(BitVec.ofNat 32 0x1), 19⟩] == false
-- bits 16..21 and 23..30 set, bit 22 clear: height lock 7, the garbage bits are ignored
#eval calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x7fbf0007), 10⟩] == ⟨16, -1, [10]⟩
#eval returnedHeights (calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x7fbf0007), 10⟩]) == [10]
#eval sequenceLocks (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x7fbf0007), 10⟩] == true
-- bits 16..21 and 23..30 set, bit 22 set: time lock 7 units
#eval calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x7fff0007), 10⟩] == ⟨-1, 1008983, [10]⟩
#eval returnedHeights (calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x7fff0007), 10⟩]) == [10]
#eval sequenceLocks (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x7fff0007), 10⟩] == true
-- bit 31 set with everything else set: disabled
#eval calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0xffffffff), 10⟩] == ⟨-1, -1, [0]⟩
#eval returnedHeights (calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0xffffffff), 10⟩]) == [0]
#eval sequenceLocks (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0xffffffff), 10⟩] == true
-- bit 31 clear with everything else set: time lock 0xffff from the coin's ancestor
#eval calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x7fffffff), 10⟩] == ⟨-1, 34559319, [10]⟩
#eval returnedHeights (calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x7fffffff), 10⟩]) == [10]
#eval sequenceLocks (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x7fffffff), 10⟩] == false
-- intra-block spend: coin at the block's own height H with mask 1 fails (H >= H)
#eval calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x1), 20⟩] == ⟨20, -1, [20]⟩
#eval returnedHeights (calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x1), 20⟩]) == [20]
#eval sequenceLocks (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x1), 20⟩] == false
-- intra-block spend: coin at H with mask 0 passes (H - 1 < H)
#eval calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x0), 20⟩] == ⟨19, -1, [20]⟩
#eval returnedHeights (calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x0), 20⟩]) == [20]
#eval sequenceLocks (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x0), 20⟩] == true
-- intra-block spend, time lock: ancestor H-1 is pprev, so even 0 units gives mtp(H-1) - 1 < mtp(H-1): passes
#eval calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x400000), 20⟩] == ⟨-1, 1011399, [20]⟩
#eval returnedHeights (calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x400000), 20⟩]) == [20]
#eval sequenceLocks (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x400000), 20⟩] == true
-- intra-block spend, time lock 1 unit: mtp(H-1) + 511 >= mtp(H-1): fails
#eval calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x400001), 20⟩] == ⟨-1, 1011911, [20]⟩
#eval returnedHeights (calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x400001), 20⟩]) == [20]
#eval sequenceLocks (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) ctx [⟨(BitVec.ofNat 32 0x400001), 20⟩] == false
-- block height 1 (pprev = genesis), coin at 0, height lock 1
#eval calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) (ctxAt 1) [⟨(BitVec.ofNat 32 0x1), 0⟩] == ⟨0, -1, [0]⟩
#eval returnedHeights (calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) (ctxAt 1) [⟨(BitVec.ofNat 32 0x1), 0⟩]) == [0]
#eval sequenceLocks (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) (ctxAt 1) [⟨(BitVec.ofNat 32 0x1), 0⟩] == true
-- block height 1, coin at 0, height lock 0 passes
#eval calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) (ctxAt 1) [⟨(BitVec.ofNat 32 0x0), 0⟩] == ⟨-1, -1, [0]⟩
#eval returnedHeights (calculate (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) (ctxAt 1) [⟨(BitVec.ofNat 32 0x0), 0⟩]) == [0]
#eval sequenceLocks (BitVec.ofNat 32 0x2) (BitVec.ofNat 32 0x1) (ctxAt 1) [⟨(BitVec.ofNat 32 0x0), 0⟩] == true
-- EvaluateSequenceLocks at the exact boundaries
#eval evaluate ctx ⟨20, -1, []⟩ == false
#eval evaluate ctx ⟨19, -1, []⟩ == true
#eval evaluate ctx ⟨-1, 1011400, []⟩ == false
#eval evaluate ctx ⟨-1, 1011399, []⟩ == true
#eval evaluate ctx ⟨20, 1011400, []⟩ == false
#eval evaluate ctx ⟨19, 1011399, []⟩ == true
#eval evaluate ctx ⟨-1, -1, []⟩ == true
#eval evaluate ctx ⟨0, 0, []⟩ == true
#eval evaluate ctx ⟨21, 0, []⟩ == false
#eval evaluate ctx ⟨0, 1011401, []⟩ == false
-- evaluate at block height 1: nBlockTime = mtp 0
#eval evaluate (ctxAt 1) ⟨0, 999999, []⟩ == true
#eval evaluate (ctxAt 1) ⟨1, 999999, []⟩ == false
#eval evaluate (ctxAt 1) ⟨0, 1000000, []⟩ == false
