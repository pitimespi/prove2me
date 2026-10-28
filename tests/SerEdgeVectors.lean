import Definitions.Def_BitcoinSer
open BitcoinSer
/-! Spot 16 vectors (`REVIEW_SPOT16.md`): CompactSize canonical-encoding and range-check edge cases,
`UnserializeTransaction` flag-byte edge cases (empty vin, superfluous witness, unknown flag), witness
round trips, `ComputeHash`/`ComputeWitnessHash`, header/block round trips, and weights. Expectations
computed by `tests/reference/ser_reference.py`. Every line prints `true`. -/
def hexVal (c : Char) : Nat := if c.isDigit then c.toNat - 48 else c.toLower.toNat - 87
def ofHexL : List Char → Bytes
  | a :: b :: r => BitVec.ofNat 8 (hexVal a * 16 + hexVal b) :: ofHexL r
  | _ => []
def ofHex (s : String) : Bytes := ofHexL s.toList
def hex (b : Bytes) : String := String.join (b.map fun x => let s := (Nat.toDigits 16 x.toNat); String.ofList (if s.length = 1 then '0' :: s else s))
-- CompactSize: canonical-encoding rejections (both with and without the range check)
#eval readCompactSize true (ofHex "fd0000") == none
#eval readCompactSize false (ofHex "fd0000") == none
#eval readCompactSize true (ofHex "fdfc00") == none
#eval readCompactSize false (ofHex "fdfc00") == none
#eval readCompactSize true (ofHex "feffff0000") == none
#eval readCompactSize false (ofHex "feffff0000") == none
#eval readCompactSize true (ofHex "ffffffffff00000000") == none
#eval readCompactSize false (ofHex "ffffffffff00000000") == none
-- CompactSize: boundary values accepted, trailing byte returned
#eval readCompactSize true (ofHex "fdfd0042") == some (253, [0x42])
#eval readCompactSize false (ofHex "fdfd0042") == some (253, [0x42])
#eval readCompactSize true (ofHex "fe0000010042") == some (65536, [0x42])
#eval readCompactSize false (ofHex "fe0000010042") == some (65536, [0x42])
#eval readCompactSize true (ofHex "ff000000000100000042") == none
#eval readCompactSize false (ofHex "ff000000000100000042") == some (4294967296, [0x42])
#eval readCompactSize true (ofHex "fc42") == some (252, [0x42])
#eval readCompactSize false (ofHex "fc42") == some (252, [0x42])
#eval readCompactSize true (ofHex "fdffff42") == some (65535, [0x42])
#eval readCompactSize false (ofHex "fdffff42") == some (65535, [0x42])
#eval readCompactSize true (ofHex "feffffffff42") == none
#eval readCompactSize false (ofHex "feffffffff42") == some (4294967295, [0x42])
#eval readCompactSize true (ofHex "fe0000000242") == some (33554432, [0x42])
#eval readCompactSize false (ofHex "fe0000000242") == some (33554432, [0x42])
#eval readCompactSize true (ofHex "fe0100000242") == none
#eval readCompactSize false (ofHex "fe0100000242") == some (33554433, [0x42])
#eval readCompactSize true (ofHex "ffffffffffffffffff42") == none
#eval readCompactSize false (ofHex "ffffffffffffffffff42") == some (18446744073709551615, [0x42])
-- CompactSize: truncated inputs
#eval readCompactSize true ([]) == none
#eval readCompactSize true (ofHex "fd") == none
#eval readCompactSize true (ofHex "fd01") == none
#eval readCompactSize true (ofHex "fe000001") == none
#eval readCompactSize true (ofHex "ff00000000010000") == none
-- WriteCompactSize at the boundaries
#eval hex (writeCompactSize 0) == "00"
#eval hex (writeCompactSize 252) == "fc"
#eval hex (writeCompactSize 253) == "fdfd00"
#eval hex (writeCompactSize 65535) == "fdffff"
#eval hex (writeCompactSize 65536) == "fe00000100"
#eval hex (writeCompactSize 4294967295) == "feffffffff"
#eval hex (writeCompactSize 4294967296) == "ff0000000001000000"
#eval hex (writeCompactSize 33554432) == "fe00000002"
-- readBytes / readList: a range-checked count (0x02000001 rejected even though the bytes would be short anyway)
#eval readBytes (ofHex "fe01000002") == none
#eval readBytes (ofHex "03aabbccdd") == some (ofHex "aabbcc", ofHex "dd")
#eval readBytes (ofHex "03aabb") == none
#eval readList (readLE 1) (ofHex "fd0000") == none
#eval readList (readLE 1) (ofHex "020a0b0c") == some ([10, 11], [0x0c])
def tEmpty : Tx := ⟨1, [], [], 0⟩
def tNoInOneOut : Tx := ⟨1, [], [⟨5000000000, ofHex "51"⟩], 0⟩
def tNoInZeroVal : Tx := ⟨1, [], [⟨0, []⟩], 0⟩
def tPlain : Tx := ⟨2, [⟨⟨ofHex "1111111111111111111111111111111111111111111111111111111111111111", 17⟩, ofHex "0001", 4294967294, []⟩], [⟨1, ofHex "6a"⟩], 500000⟩
def tWit2 : Tx := ⟨2, [⟨⟨ofHex "1111111111111111111111111111111111111111111111111111111111111111", 17⟩, [], 0, []⟩, ⟨⟨ofHex "2222222222222222222222222222222222222222222222222222222222222222", 34⟩, ofHex "51", 4294967295, [ofHex "010203", [], ofHex "aaaa"]⟩], [⟨-1, ofHex "51"⟩, ⟨9223372036854775807, []⟩], 4294967295⟩
def tWitEmptyElem : Tx := ⟨4294967295, [⟨⟨ofHex "3333333333333333333333333333333333333333333333333333333333333333", 51⟩, [], 1, [[]]⟩], [⟨0, []⟩], 0⟩
def tAllEmptyWit : Tx := ⟨1, [⟨⟨ofHex "1111111111111111111111111111111111111111111111111111111111111111", 17⟩, [], 4294967295, []⟩, ⟨⟨ofHex "2222222222222222222222222222222222222222222222222222222222222222", 34⟩, [], 4294967295, []⟩], [⟨0, []⟩], 0⟩
-- hasWitness: some input has a non-empty stack (an empty element still counts)
#eval tEmpty.hasWitness == false
#eval tNoInOneOut.hasWitness == false
#eval tNoInZeroVal.hasWitness == false
#eval tPlain.hasWitness == false
#eval tWit2.hasWitness == true
#eval tWitEmptyElem.hasWitness == true
#eval tAllEmptyWit.hasWitness == false
-- SerializeTransaction with and without witness, and round trips (trailing byte 0x99 returned)
#eval hex (serTx true tEmpty) == "01000000000000000000"
#eval readTx true (serTx true tEmpty ++ [0x99]) == some (⟨1, [], [], 0⟩, ofHex "99")
#eval readTx false (serTx true tEmpty ++ [0x99]) == some (⟨1, [], [], 0⟩, ofHex "99")
#eval hex (serTx false tEmpty) == "01000000000000000000"
#eval readTx true (serTx false tEmpty ++ [0x99]) == some (⟨1, [], [], 0⟩, ofHex "99")
#eval readTx false (serTx false tEmpty ++ [0x99]) == some (⟨1, [], [], 0⟩, ofHex "99")
#eval hex (serTx true tNoInOneOut) == "01000000000100f2052a01000000015100000000"
#eval readTx true (serTx true tNoInOneOut ++ [0x99]) == none
#eval readTx false (serTx true tNoInOneOut ++ [0x99]) == some (⟨1, [], [⟨5000000000, ofHex "51"⟩], 0⟩, ofHex "99")
#eval hex (serTx false tNoInOneOut) == "01000000000100f2052a01000000015100000000"
#eval readTx true (serTx false tNoInOneOut ++ [0x99]) == none
#eval readTx false (serTx false tNoInOneOut ++ [0x99]) == some (⟨1, [], [⟨5000000000, ofHex "51"⟩], 0⟩, ofHex "99")
#eval hex (serTx true tNoInZeroVal) == "01000000000100000000000000000000000000"
#eval readTx true (serTx true tNoInZeroVal ++ [0x99]) == none
#eval readTx false (serTx true tNoInZeroVal ++ [0x99]) == some (⟨1, [], [⟨0, []⟩], 0⟩, ofHex "99")
#eval hex (serTx false tNoInZeroVal) == "01000000000100000000000000000000000000"
#eval readTx true (serTx false tNoInZeroVal ++ [0x99]) == none
#eval readTx false (serTx false tNoInZeroVal ++ [0x99]) == some (⟨1, [], [⟨0, []⟩], 0⟩, ofHex "99")
#eval hex (serTx true tPlain) == "0200000001111111111111111111111111111111111111111111111111111111111111111111000000020001feffffff010100000000000000016a20a10700"
#eval readTx true (serTx true tPlain ++ [0x99]) == some (⟨2, [⟨⟨ofHex "1111111111111111111111111111111111111111111111111111111111111111", 17⟩, ofHex "0001", 4294967294, []⟩], [⟨1, ofHex "6a"⟩], 500000⟩, ofHex "99")
#eval readTx false (serTx true tPlain ++ [0x99]) == some (⟨2, [⟨⟨ofHex "1111111111111111111111111111111111111111111111111111111111111111", 17⟩, ofHex "0001", 4294967294, []⟩], [⟨1, ofHex "6a"⟩], 500000⟩, ofHex "99")
#eval hex (serTx false tPlain) == "0200000001111111111111111111111111111111111111111111111111111111111111111111000000020001feffffff010100000000000000016a20a10700"
#eval readTx true (serTx false tPlain ++ [0x99]) == some (⟨2, [⟨⟨ofHex "1111111111111111111111111111111111111111111111111111111111111111", 17⟩, ofHex "0001", 4294967294, []⟩], [⟨1, ofHex "6a"⟩], 500000⟩, ofHex "99")
#eval readTx false (serTx false tPlain ++ [0x99]) == some (⟨2, [⟨⟨ofHex "1111111111111111111111111111111111111111111111111111111111111111", 17⟩, ofHex "0001", 4294967294, []⟩], [⟨1, ofHex "6a"⟩], 500000⟩, ofHex "99")
#eval hex (serTx true tWit2) == "0200000000010211111111111111111111111111111111111111111111111111111111111111111100000000000000002222222222222222222222222222222222222222222222222222222222222222220000000151ffffffff02ffffffffffffffff0151ffffffffffffff7f000003030102030002aaaaffffffff"
#eval readTx true (serTx true tWit2 ++ [0x99]) == some (⟨2, [⟨⟨ofHex "1111111111111111111111111111111111111111111111111111111111111111", 17⟩, [], 0, []⟩, ⟨⟨ofHex "2222222222222222222222222222222222222222222222222222222222222222", 34⟩, ofHex "51", 4294967295, [ofHex "010203", [], ofHex "aaaa"]⟩], [⟨-1, ofHex "51"⟩, ⟨9223372036854775807, []⟩], 4294967295⟩, ofHex "99")
#eval readTx false (serTx true tWit2 ++ [0x99]) == some (⟨2, [], [⟨1229782938247303426, ofHex "1111111111111111111111111111111111"⟩], 286331153⟩, ofHex "1111111100000000000000002222222222222222222222222222222222222222222222222222222222222222220000000151ffffffff02ffffffffffffffff0151ffffffffffffff7f000003030102030002aaaaffffffff99")
#eval hex (serTx false tWit2) == "020000000211111111111111111111111111111111111111111111111111111111111111111100000000000000002222222222222222222222222222222222222222222222222222222222222222220000000151ffffffff02ffffffffffffffff0151ffffffffffffff7f00ffffffff"
#eval readTx true (serTx false tWit2 ++ [0x99]) == some (⟨2, [⟨⟨ofHex "1111111111111111111111111111111111111111111111111111111111111111", 17⟩, [], 0, []⟩, ⟨⟨ofHex "2222222222222222222222222222222222222222222222222222222222222222", 34⟩, ofHex "51", 4294967295, []⟩], [⟨-1, ofHex "51"⟩, ⟨9223372036854775807, []⟩], 4294967295⟩, ofHex "99")
#eval readTx false (serTx false tWit2 ++ [0x99]) == some (⟨2, [⟨⟨ofHex "1111111111111111111111111111111111111111111111111111111111111111", 17⟩, [], 0, []⟩, ⟨⟨ofHex "2222222222222222222222222222222222222222222222222222222222222222", 34⟩, ofHex "51", 4294967295, []⟩], [⟨-1, ofHex "51"⟩, ⟨9223372036854775807, []⟩], 4294967295⟩, ofHex "99")
#eval hex (serTx true tWitEmptyElem) == "ffffffff000101333333333333333333333333333333333333333333333333333333333333333333000000000100000001000000000000000000010000000000"
#eval readTx true (serTx true tWitEmptyElem ++ [0x99]) == some (⟨4294967295, [⟨⟨ofHex "3333333333333333333333333333333333333333333333333333333333333333", 51⟩, [], 1, [[]]⟩], [⟨0, []⟩], 0⟩, ofHex "99")
#eval readTx false (serTx true tWitEmptyElem ++ [0x99]) == none
#eval hex (serTx false tWitEmptyElem) == "ffffffff0133333333333333333333333333333333333333333333333333333333333333333300000000010000000100000000000000000000000000"
#eval readTx true (serTx false tWitEmptyElem ++ [0x99]) == some (⟨4294967295, [⟨⟨ofHex "3333333333333333333333333333333333333333333333333333333333333333", 51⟩, [], 1, []⟩], [⟨0, []⟩], 0⟩, ofHex "99")
#eval readTx false (serTx false tWitEmptyElem ++ [0x99]) == some (⟨4294967295, [⟨⟨ofHex "3333333333333333333333333333333333333333333333333333333333333333", 51⟩, [], 1, []⟩], [⟨0, []⟩], 0⟩, ofHex "99")
#eval hex (serTx true tAllEmptyWit) == "010000000211111111111111111111111111111111111111111111111111111111111111111100000000ffffffff22222222222222222222222222222222222222222222222222222222222222222200000000ffffffff0100000000000000000000000000"
#eval readTx true (serTx true tAllEmptyWit ++ [0x99]) == some (⟨1, [⟨⟨ofHex "1111111111111111111111111111111111111111111111111111111111111111", 17⟩, [], 4294967295, []⟩, ⟨⟨ofHex "2222222222222222222222222222222222222222222222222222222222222222", 34⟩, [], 4294967295, []⟩], [⟨0, []⟩], 0⟩, ofHex "99")
#eval readTx false (serTx true tAllEmptyWit ++ [0x99]) == some (⟨1, [⟨⟨ofHex "1111111111111111111111111111111111111111111111111111111111111111", 17⟩, [], 4294967295, []⟩, ⟨⟨ofHex "2222222222222222222222222222222222222222222222222222222222222222", 34⟩, [], 4294967295, []⟩], [⟨0, []⟩], 0⟩, ofHex "99")
#eval hex (serTx false tAllEmptyWit) == "010000000211111111111111111111111111111111111111111111111111111111111111111100000000ffffffff22222222222222222222222222222222222222222222222222222222222222222200000000ffffffff0100000000000000000000000000"
#eval readTx true (serTx false tAllEmptyWit ++ [0x99]) == some (⟨1, [⟨⟨ofHex "1111111111111111111111111111111111111111111111111111111111111111", 17⟩, [], 4294967295, []⟩, ⟨⟨ofHex "2222222222222222222222222222222222222222222222222222222222222222", 34⟩, [], 4294967295, []⟩], [⟨0, []⟩], 0⟩, ofHex "99")
#eval readTx false (serTx false tAllEmptyWit ++ [0x99]) == some (⟨1, [⟨⟨ofHex "1111111111111111111111111111111111111111111111111111111111111111", 17⟩, [], 4294967295, []⟩, ⟨⟨ofHex "2222222222222222222222222222222222222222222222222222222222222222", 34⟩, [], 4294967295, []⟩], [⟨0, []⟩], 0⟩, ofHex "99")
-- a tx whose witnesses are all empty serializes without the flag; stripWitness is the TX_NO_WITNESS read
#eval serTx true tAllEmptyWit == serTx false tAllEmptyWit
#eval serTx true tWit2 ≠ serTx false tWit2
#eval (serTx true tWit2).take 6 == ofHex "020000000001"
#eval readTx false (serTx false tWit2) == some (tWit2.stripWitness, [])
#eval (readTx true (serTx true tWit2)).map (fun p => p.1.stripWitness) == some tWit2.stripWitness
-- hand-built flag-byte edge cases
#eval readTx true (ofHex "0100000000010111111111111111111111111111111111111111111111111111111111111111111100000000ffffffff01070000000000000001510000000000") == none   -- flag 1 but the single witness stack is empty: Superfluous witness record
#eval readTx false (ofHex "0100000000010111111111111111111111111111111111111111111111111111111111111111111100000000ffffffff01070000000000000001510000000000") == some (⟨1, [], [⟨1229782938247303425, ofHex "1111111111111111111111111111111111"⟩], 286331153⟩, ofHex "1111111100000000ffffffff01070000000000000001510000000000")   -- flag 1 but the single witness stack is empty: Superfluous witness record
#eval readTx true (ofHex "0100000000010211111111111111111111111111111111111111111111111111111111111111111100000000ffffffff22222222222222222222222222222222222222222222222222222222222222222200000000ffffffff0107000000000000000151000000000000") == none   -- flag 1, two inputs, both stacks empty
#eval readTx false (ofHex "0100000000010211111111111111111111111111111111111111111111111111111111111111111100000000ffffffff22222222222222222222222222222222222222222222222222222222222222222200000000ffffffff0107000000000000000151000000000000") == some (⟨1, [], [⟨1229782938247303426, ofHex "1111111111111111111111111111111111"⟩], 286331153⟩, ofHex "1111111100000000ffffffff22222222222222222222222222222222222222222222222222222222222222222200000000ffffffff0107000000000000000151000000000000")   -- flag 1, two inputs, both stacks empty
#eval readTx true (ofHex "010000000001000000000000") == none   -- flag 1 with an empty re-read vin: no stacks, Superfluous witness record
#eval readTx false (ofHex "010000000001000000000000") == none   -- flag 1 with an empty re-read vin: no stacks, Superfluous witness record
#eval readTx true (ofHex "0100000000020111111111111111111111111111111111111111111111111111111111111111111100000000ffffffff010700000000000000015100000000") == none   -- flag 2: Unknown transaction optional data
#eval readTx false (ofHex "0100000000020111111111111111111111111111111111111111111111111111111111111111111100000000ffffffff010700000000000000015100000000") == some (⟨1, [], [⟨1229782938247303425, ofHex "1111111111111111111111111111111111"⟩, ⟨1229782938247303441, []⟩], 4278190080⟩, ofHex "ffffff010700000000000000015100000000")   -- flag 2: Unknown transaction optional data
#eval readTx true (ofHex "0100000000030111111111111111111111111111111111111111111111111111111111111111111100000000ffffffff01070000000000000001510101ab00000000") == none   -- flag 3 with a real witness: bit 1 is consumed, flag 2 remains
#eval readTx false (ofHex "0100000000030111111111111111111111111111111111111111111111111111111111111111111100000000ffffffff01070000000000000001510101ab00000000") == some (⟨1, [], [⟨1229782938247303425, ofHex "1111111111111111111111111111111111"⟩, ⟨1229782938247303441, []⟩, ⟨144115188059078656, ofHex "00000000000000"⟩], 16863489⟩, ofHex "ab00000000")   -- flag 3 with a real witness: bit 1 is consumed, flag 2 remains
#eval readTx true (ofHex "0100000000010111111111111111111111111111111111111111111111111111111111111111111100000000ffffffff01070000000000000001510101ab00000000") == some (⟨1, [⟨⟨ofHex "1111111111111111111111111111111111111111111111111111111111111111", 17⟩, [], 4294967295, [ofHex "ab"]⟩], [⟨7, ofHex "51"⟩], 0⟩, [])   -- flag 1 with a real witness: ok
#eval readTx false (ofHex "0100000000010111111111111111111111111111111111111111111111111111111111111111111100000000ffffffff01070000000000000001510101ab00000000") == some (⟨1, [], [⟨1229782938247303425, ofHex "1111111111111111111111111111111111"⟩], 286331153⟩, ofHex "1111111100000000ffffffff01070000000000000001510101ab00000000")   -- flag 1 with a real witness: ok
#eval readTx true (ofHex "0100000000810111111111111111111111111111111111111111111111111111111111111111111100000000ffffffff01070000000000000001510101ab00000000") == none   -- flag 0x81: 0x80 remains
#eval readTx false (ofHex "0100000000810111111111111111111111111111111111111111111111111111111111111111111100000000ffffffff01070000000000000001510101ab00000000") == none   -- flag 0x81: 0x80 remains
#eval readTx true (ofHex "0100000000010111111111111111111111111111111111111111111111111111111111111111111100000000ffffffff0107000000000000000151010000000000") == some (⟨1, [⟨⟨ofHex "1111111111111111111111111111111111111111111111111111111111111111", 17⟩, [], 4294967295, [[]]⟩], [⟨7, ofHex "51"⟩], 0⟩, [])   -- flag 1 with a witness whose stack has one empty element: ok (stack non-empty)
#eval readTx false (ofHex "0100000000010111111111111111111111111111111111111111111111111111111111111111111100000000ffffffff0107000000000000000151010000000000") == some (⟨1, [], [⟨1229782938247303425, ofHex "1111111111111111111111111111111111"⟩], 286331153⟩, ofHex "1111111100000000ffffffff0107000000000000000151010000000000")   -- flag 1 with a witness whose stack has one empty element: ok (stack non-empty)
#eval readTx true (ofHex "0100000000") == none   -- empty vin then no flag byte: short read
#eval readTx false (ofHex "0100000000") == none   -- empty vin then no flag byte: short read
#eval readTx true (ofHex "010000000000efbeadde") == some (⟨1, [], [], 3735928559⟩, [])   -- empty vin, flag 0, then nLockTime: vout is not read
#eval readTx false (ofHex "010000000000efbeadde") == some (⟨1, [], [], 3735928559⟩, [])   -- empty vin, flag 0, then nLockTime: vout is not read
#eval readTx true (ofHex "0100000000000102030405") == some (⟨1, [], [], 67305985⟩, ofHex "05")   -- empty vin, flag 0, output count byte would follow: it is the flag, vout stays empty, the rest is nLockTime
#eval readTx false (ofHex "0100000000000102030405") == some (⟨1, [], [], 67305985⟩, ofHex "05")   -- empty vin, flag 0, output count byte would follow: it is the flag, vout stays empty, the rest is nLockTime
#eval readTx true (ofHex "0200000000010211111111111111111111111111111111111111111111111111111111111111111100000000000000002222222222222222222222222222222222222222222222222222222222222222220000000151ffffffff02ffffffffffffffff0151ffffffffffffff7f000003030102030002aaaaffffff") == none   -- witness tx truncated by one byte
#eval readTx false (ofHex "0200000000010211111111111111111111111111111111111111111111111111111111111111111100000000000000002222222222222222222222222222222222222222222222222222222222222222220000000151ffffffff02ffffffffffffffff0151ffffffffffffff7f000003030102030002aaaaffffff") == some (⟨2, [], [⟨1229782938247303426, ofHex "1111111111111111111111111111111111"⟩], 286331153⟩, ofHex "1111111100000000000000002222222222222222222222222222222222222222222222222222222222222222220000000151ffffffff02ffffffffffffffff0151ffffffffffffff7f000003030102030002aaaaffffff")   -- witness tx truncated by one byte
#eval readTx true (ofHex "0100000000010111111111111111111111111111111111111111111111111111111111111111111100000000ffffffff010700000000000000015101fd0100ab00000000") == none   -- witness tx with a non-canonical stack-element length
#eval readTx false (ofHex "0100000000010111111111111111111111111111111111111111111111111111111111111111111100000000ffffffff010700000000000000015101fd0100ab00000000") == some (⟨1, [], [⟨1229782938247303425, ofHex "1111111111111111111111111111111111"⟩], 286331153⟩, ofHex "1111111100000000ffffffff010700000000000000015101fd0100ab00000000")   -- witness tx with a non-canonical stack-element length
#eval readTx true (ofHex "01000000fe01000002") == none   -- vin count 0x02000001 (above MAX_SIZE) is rejected before any input is read
#eval readTx false (ofHex "01000000fe01000002") == none   -- vin count 0x02000001 (above MAX_SIZE) is rejected before any input is read
-- ComputeHash (witness-stripped), ComputeWitnessHash (= txid without witness), weights
#eval hex (txid tEmpty) == "43ec7a579f5561a42a7e9637ad4156672735a658be2752181801f723ba3316d2"
#eval hex (wtxid tEmpty) == "43ec7a579f5561a42a7e9637ad4156672735a658be2752181801f723ba3316d2"
#eval txWeight tEmpty == 40
#eval hex (txid tNoInOneOut) == "2773b9f5475a9304f342eee60e7f67aabc8a08dba285c64270d7633507fa020e"
#eval hex (wtxid tNoInOneOut) == "2773b9f5475a9304f342eee60e7f67aabc8a08dba285c64270d7633507fa020e"
#eval txWeight tNoInOneOut == 80
#eval hex (txid tNoInZeroVal) == "132ea360b529301fc1051e2ba419ca2eeca56abf5681bef610ebe925962290cf"
#eval hex (wtxid tNoInZeroVal) == "132ea360b529301fc1051e2ba419ca2eeca56abf5681bef610ebe925962290cf"
#eval txWeight tNoInZeroVal == 76
#eval hex (txid tPlain) == "ecc5efb6967718766ef9e8692617a2cec1c84753689d93b086cc523c53c6698f"
#eval hex (wtxid tPlain) == "ecc5efb6967718766ef9e8692617a2cec1c84753689d93b086cc523c53c6698f"
#eval txWeight tPlain == 252
#eval hex (txid tWit2) == "413773c33b9be37ce3b6aee7e756307ef35774564c653357bba08d3ff1735438"
#eval hex (wtxid tWit2) == "ae1e542ec64b19dc4b39ee1a3b0e1f00cf6a3c55f647e431a393360f80f2d491"
#eval txWeight tWit2 == 460
#eval hex (txid tWitEmptyElem) == "4db6aa00a208b31b6880b177a0a23043f0c42755152e3ec8c6f1b927ed51108f"
#eval hex (wtxid tWitEmptyElem) == "8647d95c6d41cdfab4b1a915c61260f2d5d93dacd40948bed6d7c65386b22a10"
#eval txWeight tWitEmptyElem == 244
#eval hex (txid tAllEmptyWit) == "65be46a64bedaaf4abe68076b00dadd088d159d5379ca9dffd768529659d1df1"
#eval hex (wtxid tAllEmptyWit) == "65be46a64bedaaf4abe68076b00dadd088d159d5379ca9dffd768529659d1df1"
#eval txWeight tAllEmptyWit == 404
#eval wtxid tAllEmptyWit == txid tAllEmptyWit
#eval wtxid tWit2 ≠ txid tWit2
#eval txWeight tWit2 == 3 * 112 + 124
-- CAmount is int64 two's complement; version and nLockTime are uint32
#eval hex (serInt64 (-1)) == "ffffffffffffffff"
#eval hex (serInt64 (-(2^63))) == "0000000000000080"
#eval hex (serInt64 (2^63 - 1)) == "ffffffffffffff7f"
#eval readInt64 (ofHex "ffffffffffffffff") == some (-1, [])
#eval readInt64 (ofHex "0000000000000080") == some (-(2^63), [])
#eval readInt64 (ofHex "ffffffffffffff7f") == some (2^63 - 1, [])
#eval readTxOut (ofHex "ffffffffffffffff00") == some (⟨-1, []⟩, [])
#eval (readTx true (serTx true tWitEmptyElem)).map (fun p => p.1.version) == some 4294967295
#eval (readTx true (serTx true tWit2)).map (fun p => p.1.nLockTime) == some 4294967295
-- CBlockHeader: int32_t nVersion; the genesis header and version -1 / INT32_MIN / INT32_MAX
#eval hex (serHeader genesisHeader) == "0100000000000000000000000000000000000000000000000000000000000000000000003ba3edfd7a7b12b27ac72c3e67768f617fc81bc3888a51323a9fb8aa4b1e5e4a29ab5f49ffff001d1dac2b7c"
#eval readHeader (serHeader genesisHeader ++ [1]) == some (genesisHeader, [1])
#eval readHeader (ofHex "0100000000000000000000000000000000000000000000000000000000000000000000003ba3edfd7a7b12b27ac72c3e67768f617fc81bc3888a51323a9fb8aa4b1e5e4a29ab5f49ffff001d1dac2b7c") == some (genesisHeader, [])
#eval readHeader (ofHex "0100000000000000000000000000000000000000000000000000000000000000000000003ba3edfd7a7b12b27ac72c3e67768f617fc81bc3888a51323a9fb8aa4b1e5e4a29ab5f49ffff001d1dac2b") == none
def hdrm1 : Header := ⟨-1, ofHex "0000000000000000000000000000000000000000000000000000000000000000", ofHex "3ba3edfd7a7b12b27ac72c3e67768f617fc81bc3888a51323a9fb8aa4b1e5e4a", 1231006505, 486604799, 2083236893⟩
#eval hex (serHeader hdrm1) == "ffffffff00000000000000000000000000000000000000000000000000000000000000003ba3edfd7a7b12b27ac72c3e67768f617fc81bc3888a51323a9fb8aa4b1e5e4a29ab5f49ffff001d1dac2b7c"
#eval readHeader (ofHex "ffffffff00000000000000000000000000000000000000000000000000000000000000003ba3edfd7a7b12b27ac72c3e67768f617fc81bc3888a51323a9fb8aa4b1e5e4a29ab5f49ffff001d1dac2b7c") == some (hdrm1, [])
#eval hex (headerHash hdrm1) == "9903f1b4d13aaa9bd7e4b903c61add7c295f47dea12571e0a7635fa83cdf4923"
def hdrm2147483648 : Header := ⟨-2147483648, ofHex "0000000000000000000000000000000000000000000000000000000000000000", ofHex "3ba3edfd7a7b12b27ac72c3e67768f617fc81bc3888a51323a9fb8aa4b1e5e4a", 1231006505, 486604799, 2083236893⟩
#eval hex (serHeader hdrm2147483648) == "0000008000000000000000000000000000000000000000000000000000000000000000003ba3edfd7a7b12b27ac72c3e67768f617fc81bc3888a51323a9fb8aa4b1e5e4a29ab5f49ffff001d1dac2b7c"
#eval readHeader (ofHex "0000008000000000000000000000000000000000000000000000000000000000000000003ba3edfd7a7b12b27ac72c3e67768f617fc81bc3888a51323a9fb8aa4b1e5e4a29ab5f49ffff001d1dac2b7c") == some (hdrm2147483648, [])
#eval hex (headerHash hdrm2147483648) == "d3b16ab9d7a2a89f5756cc063076a9c76a3852486f8bbff2e90481dd5da5a596"
def hdr2147483647 : Header := ⟨2147483647, ofHex "0000000000000000000000000000000000000000000000000000000000000000", ofHex "3ba3edfd7a7b12b27ac72c3e67768f617fc81bc3888a51323a9fb8aa4b1e5e4a", 1231006505, 486604799, 2083236893⟩
#eval hex (serHeader hdr2147483647) == "ffffff7f00000000000000000000000000000000000000000000000000000000000000003ba3edfd7a7b12b27ac72c3e67768f617fc81bc3888a51323a9fb8aa4b1e5e4a29ab5f49ffff001d1dac2b7c"
#eval readHeader (ofHex "ffffff7f00000000000000000000000000000000000000000000000000000000000000003ba3edfd7a7b12b27ac72c3e67768f617fc81bc3888a51323a9fb8aa4b1e5e4a29ab5f49ffff001d1dac2b7c") == some (hdr2147483647, [])
#eval hex (headerHash hdr2147483647) == "d2f1db939640044ed154ec57153d1fd3146237699b5531d58416c9793fac686c"
#eval (readHeader (ofHex "ffffffff" ++ List.replicate 76 0)).map (fun p => p.1.version) == some (-1)
#eval (readHeader (ofHex "00000080" ++ List.replicate 76 0)).map (fun p => p.1.version) == some (-2147483648)
#eval (readHeader (ofHex "ffffff7f" ++ List.replicate 76 0)).map (fun p => p.1.version) == some 2147483647
-- CBlock with witness transactions: GetSerializeSize(TX_NO_WITNESS(block)), GetBlockWeight, round trips
def blkW : Block := ⟨genesisHeader, [genesisCoinbase, tWit2, tPlain, tWitEmptyElem]⟩
#eval (serBlock false blkW).length == 520
#eval (serBlock false blkW).length == 80 + 1 + 204 + 112 + 63 + 60
#eval (serBlock true blkW).length == 536
#eval hex (serBlock true blkW) == "0100000000000000000000000000000000000000000000000000000000000000000000003ba3edfd7a7b12b27ac72c3e67768f617fc81bc3888a51323a9fb8aa4b1e5e4a29ab5f49ffff001d1dac2b7c0401000000010000000000000000000000000000000000000000000000000000000000000000ffffffff4d04ffff001d0104455468652054696d65732030332f4a616e2f32303039204368616e63656c6c6f72206f6e206272696e6b206f66207365636f6e64206261696c6f757420666f722062616e6b73ffffffff0100f2052a01000000434104678afdb0fe5548271967f1a67130b7105cd6a828e03909a67962e0ea1f61deb649f6bc3f4cef38c4f35504e51ec112de5c384df7ba0b8d578a4c702b6bf11d5fac000000000200000000010211111111111111111111111111111111111111111111111111111111111111111100000000000000002222222222222222222222222222222222222222222222222222222222222222220000000151ffffffff02ffffffffffffffff0151ffffffffffffff7f000003030102030002aaaaffffffff0200000001111111111111111111111111111111111111111111111111111111111111111111000000020001feffffff010100000000000000016a20a10700ffffffff000101333333333333333333333333333333333333333333333333333333333333333333000000000100000001000000000000000000010000000000"
#eval hex (serBlock false blkW) == "0100000000000000000000000000000000000000000000000000000000000000000000003ba3edfd7a7b12b27ac72c3e67768f617fc81bc3888a51323a9fb8aa4b1e5e4a29ab5f49ffff001d1dac2b7c0401000000010000000000000000000000000000000000000000000000000000000000000000ffffffff4d04ffff001d0104455468652054696d65732030332f4a616e2f32303039204368616e63656c6c6f72206f6e206272696e6b206f66207365636f6e64206261696c6f757420666f722062616e6b73ffffffff0100f2052a01000000434104678afdb0fe5548271967f1a67130b7105cd6a828e03909a67962e0ea1f61deb649f6bc3f4cef38c4f35504e51ec112de5c384df7ba0b8d578a4c702b6bf11d5fac00000000020000000211111111111111111111111111111111111111111111111111111111111111111100000000000000002222222222222222222222222222222222222222222222222222222222222222220000000151ffffffff02ffffffffffffffff0151ffffffffffffff7f00ffffffff0200000001111111111111111111111111111111111111111111111111111111111111111111000000020001feffffff010100000000000000016a20a10700ffffffff0133333333333333333333333333333333333333333333333333333333333333333300000000010000000100000000000000000000000000"
#eval blockWeight blkW == 2096
#eval blockWeight blkW == 3 * 520 + 536
#eval blockWeight blkW == (blkW.vtx.map txWeight).sum + 4 * 81
#eval readBlock true (serBlock true blkW ++ [5]) == some (blkW, [5])
#eval readBlock false (serBlock false blkW) == some (⟨genesisHeader, blkW.vtx.map Tx.stripWitness⟩, [])
#eval readBlock false (serBlock true blkW) == none   -- witness bytes read as TX_NO_WITNESS
#eval readBlock true (serBlock true blkW).dropLast == none
#eval blockWeight genesisBlock == 1140
#eval blockWeight genesisBlock == 4 * (serBlock false genesisBlock).length
