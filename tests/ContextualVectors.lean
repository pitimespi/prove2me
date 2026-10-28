import Definitions.Def_BitcoinBlockV2
open BitcoinBlockV2 BitcoinSer
/-! Spot 13 vectors (`REVIEW_SPOT13.md`): `IsFinalTx`, the BIP34 `CScript() << nHeight` prefix, and
`ContextualCheckBlock`'s cutoff and tests on synthetic chains. Expectations from `tests/reference/contextual_reference.py`.
Every line prints `true`. -/
def hexVal (c : Char) : Nat := if c.isDigit then c.toNat - 48 else c.toLower.toNat - 87
def ofHexL : List Char → Bytes
  | a :: b :: r => BitVec.ofNat 8 (hexVal a * 16 + hexVal b) :: ofHexL r
  | _ => []
def ofHex (s : String) : Bytes := ofHexL s.toList
-- CScript() << nHeight
#eval heightScript 0 == ofHex "00"
#eval heightScript 1 == ofHex "51"
#eval heightScript 2 == ofHex "52"
#eval heightScript 16 == ofHex "60"
#eval heightScript 17 == ofHex "0111"
#eval heightScript 127 == ofHex "017f"
#eval heightScript 128 == ofHex "028000"
#eval heightScript 255 == ofHex "02ff00"
#eval heightScript 256 == ofHex "020001"
#eval heightScript 32767 == ofHex "02ff7f"
#eval heightScript 32768 == ofHex "03008000"
#eval heightScript 65535 == ofHex "03ffff00"
#eval heightScript 65536 == ofHex "03000001"
#eval heightScript 227931 == ofHex "035b7a03"
#eval heightScript 8388607 == ofHex "03ffff7f"
#eval heightScript 8388608 == ofHex "0400008000"
#eval heightScript 16777215 == ofHex "04ffffff00"
#eval heightScript 16777216 == ofHex "0400000001"
#eval heightScript 2147483647 == ofHex "04ffffff7f"
-- IsFinalTx(tx, nBlockHeight, nBlockTime): (locktime, sequences, height, time)
#eval isFinalTx ⟨1, [⟨⟨List.replicate 32 1, 0⟩, [], 0, []⟩], [⟨1, [0x51]⟩], 0⟩ 100 0 == true   -- locktime 0, seqs ['0'], height 100, time 0
#eval isFinalTx ⟨1, [⟨⟨List.replicate 32 1, 0⟩, [], 0, []⟩], [⟨1, [0x51]⟩], 99⟩ 100 0 == true   -- locktime 99, seqs ['0'], height 100, time 0
#eval isFinalTx ⟨1, [⟨⟨List.replicate 32 1, 0⟩, [], 0, []⟩], [⟨1, [0x51]⟩], 100⟩ 100 0 == false   -- locktime 100, seqs ['0'], height 100, time 0
#eval isFinalTx ⟨1, [⟨⟨List.replicate 32 1, 0⟩, [], 4294967295, []⟩], [⟨1, [0x51]⟩], 100⟩ 100 0 == true   -- locktime 100, seqs ['ffffffff'], height 100, time 0
#eval isFinalTx ⟨1, [⟨⟨List.replicate 32 1, 0⟩, [], 4294967295, []⟩, ⟨⟨List.replicate 32 1, 1⟩, [], 4294967295, []⟩], [⟨1, [0x51]⟩], 101⟩ 100 0 == true   -- locktime 101, seqs ['ffffffff', 'ffffffff'], height 100, time 0
#eval isFinalTx ⟨1, [⟨⟨List.replicate 32 1, 0⟩, [], 4294967295, []⟩, ⟨⟨List.replicate 32 1, 1⟩, [], 0, []⟩], [⟨1, [0x51]⟩], 101⟩ 100 0 == false   -- locktime 101, seqs ['ffffffff', '0'], height 100, time 0
#eval isFinalTx ⟨1, [⟨⟨List.replicate 32 1, 0⟩, [], 0, []⟩], [⟨1, [0x51]⟩], 499999999⟩ 1 0 == false   -- locktime 499999999, seqs ['0'], height 1, time 0
#eval isFinalTx ⟨1, [⟨⟨List.replicate 32 1, 0⟩, [], 0, []⟩], [⟨1, [0x51]⟩], 499999999⟩ 500000000 0 == true   -- locktime 499999999, seqs ['0'], height 500000000, time 0
#eval isFinalTx ⟨1, [⟨⟨List.replicate 32 1, 0⟩, [], 0, []⟩], [⟨1, [0x51]⟩], 500000000⟩ 10000000 500000001 == true   -- locktime 500000000, seqs ['0'], height 10000000, time 500000001
#eval isFinalTx ⟨1, [⟨⟨List.replicate 32 1, 0⟩, [], 0, []⟩], [⟨1, [0x51]⟩], 500000000⟩ 10000000 500000000 == false   -- locktime 500000000, seqs ['0'], height 10000000, time 500000000
#eval isFinalTx ⟨1, [⟨⟨List.replicate 32 1, 0⟩, [], 4294967295, []⟩], [⟨1, [0x51]⟩], 500000000⟩ 0 0 == true   -- locktime 500000000, seqs ['ffffffff'], height 0, time 0
#eval isFinalTx ⟨1, [⟨⟨List.replicate 32 1, 0⟩, [], 0, []⟩], [⟨1, [0x51]⟩], 1700000000⟩ 900000 1700000000 == false   -- locktime 1700000000, seqs ['0'], height 900000, time 1700000000
#eval isFinalTx ⟨1, [⟨⟨List.replicate 32 1, 0⟩, [], 0, []⟩], [⟨1, [0x51]⟩], 1700000000⟩ 900000 1700000001 == true   -- locktime 1700000000, seqs ['0'], height 900000, time 1700000001
#eval isFinalTx ⟨1, [⟨⟨List.replicate 32 1, 0⟩, [], 4294967294, []⟩], [⟨1, [0x51]⟩], 1700000000⟩ 0 0 == false   -- locktime 1700000000, seqs ['fffffffe'], height 0, time 0
#eval isFinalTx ⟨1, [], [⟨1, [0x51]⟩], 5⟩ 1 0 == true   -- locktime 5, seqs [], height 1, time 0
-- ContextualCheckBlock on synthetic chains (only its own tests; PoW and CheckBlock are not involved)
def hdrT (t : Nat) : Header := ⟨1, List.replicate 32 0, List.replicate 32 0, t, 0x1d00ffff, 0⟩
/-- a chain of `n` headers with times 600 apart: the tip's MTP is the time of the 6th most recent block. -/
def chainN (n : Nat) : ChainState := ⟨(List.range n).map fun i => hdrT (1500000000 + 600 * i), []⟩
def cbAt (ss : Bytes) : Tx := ⟨1, [⟨⟨List.replicate 32 0, 0xffffffff⟩, ss, 0xffffffff, []⟩], [⟨5000000000, [0x51]⟩], 0⟩
def blk (S : ChainState) (txs : List Tx) : Block := ⟨hdrT (1500000000 + 600 * S.nextHeight), txs⟩
-- pre-BIP34 (next height 170): no height prefix needed, cutoff is the block's own time
#eval contextualCheckBlock (chainN 170) (blk (chainN 170) [cbAt [0x04, 0xff, 0xff, 0x00, 0x1d, 0x01, 0x02]])
#eval contextualCheckBlock (chainN 170) (blk (chainN 170) [cbAt [], ⟨1, [⟨⟨List.replicate 32 1, 0⟩, [], 0, []⟩], [⟨1, [0x51]⟩], 170⟩]) == false   -- locktime 170 = height: not final
#eval contextualCheckBlock (chainN 170) (blk (chainN 170) [cbAt [], ⟨1, [⟨⟨List.replicate 32 1, 0⟩, [], 0, []⟩], [⟨1, [0x51]⟩], 169⟩])   -- locktime 169 < height 170: final
#eval contextualCheckBlock (chainN 170) (blk (chainN 170) [cbAt [], ⟨1, [⟨⟨List.replicate 32 1, 0⟩, [], 0, []⟩], [⟨1, [0x51]⟩], 1500101999⟩])   -- time lock just below the block time (pre-CSV cutoff): final
#eval contextualCheckBlock (chainN 170) (blk (chainN 170) [cbAt [], ⟨1, [⟨⟨List.replicate 32 1, 0⟩, [], 0, []⟩], [⟨1, [0x51]⟩], 1500102000⟩]) == false   -- equal to the block time: not final
-- BIP34 active (next height 227931): the coinbase scriptSig must start with the height push
#eval heightScript 227931 == ofHex "035b7a03"
#eval contextualCheckBlock (chainN 227931) (blk (chainN 227931) [cbAt (ofHex "035b7a03" ++ [0x01, 0x02])])   -- prefix with trailing bytes
#eval contextualCheckBlock (chainN 227931) (blk (chainN 227931) [cbAt (ofHex "035b7a03")])   -- exact
#eval contextualCheckBlock (chainN 227931) (blk (chainN 227931) [cbAt (ofHex "035a7a03")]) == false   -- previous height
#eval contextualCheckBlock (chainN 227931) (blk (chainN 227931) [cbAt (ofHex "035b7a")]) == false   -- truncated
#eval contextualCheckBlock (chainN 227931) (blk (chainN 227931) [cbAt (ofHex "045b7a0300")]) == false   -- non-minimal push of the same number is a different prefix
#eval contextualCheckBlock (chainN 227930) (blk (chainN 227930) [cbAt []])   -- next height 227930: not yet enforced
-- CSV active (next height 419328): the cutoff is the previous block's MTP, not the block time
#eval (chainN 419328).mtp == 1751593200
#eval contextualCheckBlock (chainN 419328) (blk (chainN 419328) [cbAt (ofHex "03006606"), ⟨1, [⟨⟨List.replicate 32 1, 0⟩, [], 0, []⟩], [⟨1, [0x51]⟩], 1751593199⟩])   -- time lock below the MTP: final
#eval contextualCheckBlock (chainN 419328) (blk (chainN 419328) [cbAt (ofHex "03006606"), ⟨1, [⟨⟨List.replicate 32 1, 0⟩, [], 0, []⟩], [⟨1, [0x51]⟩], 1751593200⟩]) == false   -- equal to the MTP: not final although below the block time
#eval contextualCheckBlock (chainN 419328) (blk (chainN 419328) [cbAt (ofHex "03006606"), ⟨1, [⟨⟨List.replicate 32 1, 0⟩, [], 0xffffffff, []⟩], [⟨1, [0x51]⟩], 1751693200⟩])   -- SEQUENCE_FINAL ignores the lock time
#eval contextualCheckBlock (chainN 419327) (blk (chainN 419327) [cbAt (ofHex "03ff6506"), ⟨1, [⟨⟨List.replicate 32 1, 0⟩, [], 0, []⟩], [⟨1, [0x51]⟩], 1751593200⟩])   -- one block earlier CSV is not active for the next block: block-time cutoff, final
-- SegWit active (next height 481824): witness data without a commitment is rejected; before, the same
#eval contextualCheckBlock (chainN 481824) (blk (chainN 481824) [cbAt (ofHex "03205a07"), ⟨1, [⟨⟨List.replicate 32 1, 0⟩, [], 0, [[0x01]]⟩], [⟨1, [0x51]⟩], 0⟩]) == false
#eval contextualCheckBlock (chainN 481823) (blk (chainN 481823) [cbAt (ofHex "031f5a07"), ⟨1, [⟨⟨List.replicate 32 1, 0⟩, [], 0, [[0x01]]⟩], [⟨1, [0x51]⟩], 0⟩]) == false   -- unexpected-witness applies when SegWit is not active too
#eval contextualCheckBlock (chainN 481824) (blk (chainN 481824) [cbAt (ofHex "03205a07")])   -- no witness, no commitment needed
-- weight: a coinbase whose scriptSig makes the block weigh exactly 4,000,000 passes, one byte more fails
def bigSS : Bytes := ofHex "035b7a03" ++ List.replicate (999854 - 4) 0
#eval blockWeight (blk (chainN 227931) [cbAt bigSS]) == 4000000
#eval contextualCheckBlock (chainN 227931) (blk (chainN 227931) [cbAt bigSS])
#eval contextualCheckBlock (chainN 227931) (blk (chainN 227931) [cbAt (bigSS ++ [0])]) == false
