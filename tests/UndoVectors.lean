import Definitions.Def_BitcoinBlockV2
open BitcoinBlockV2 BitcoinSer
/-! Spot 18 vectors (`REVIEW_SPOT18.md`): `DisconnectBlock` and `ApplyTxInUndo` over small ledgers, expectations
from `tests/reference/txcheck_undo_reference.py` (a dictionary coin view). Every line prints `true`. -/
def hexVal (c : Char) : Nat := if c.isDigit then c.toNat - 48 else c.toLower.toNat - 87
def ofHexL : List Char → Bytes
  | a :: b :: r => BitVec.ofNat 8 (hexVal a * 16 + hexVal b) :: ofHexL r
  | _ => []
def ofHex (s : String) : Bytes := ofHexL s.toList
def res (r : Option (Ledger × Bool)) : Option Bool := r.map Prod.snd
def coinAt (r : Option (Ledger × Bool)) (op : OutPoint) : Option Coin := r.bind fun p => getCoin p.1 op
def base18 : Ledger := [(⟨ofHex "0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a", 0⟩, ⟨⟨5000, ofHex "51"⟩, 50, false⟩), (⟨ofHex "0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a", 1⟩, ⟨⟨7000, ofHex "51"⟩, 50, false⟩), (⟨ofHex "0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b", 0⟩, ⟨⟨5000000000, ofHex "51"⟩, 60, true⟩)]
def cb18 : Tx := ⟨1, [⟨⟨ofHex "0000000000000000000000000000000000000000000000000000000000000000", 4294967295⟩, ofHex "030102", 4294967295, []⟩], [⟨5000001000, ofHex "51"⟩, ⟨0, ofHex "6a0102"⟩], 0⟩
def t1 : Tx := ⟨1, [⟨⟨ofHex "0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a", 0⟩, [], 4294967295, []⟩, ⟨⟨ofHex "0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a", 1⟩, [], 4294967295, []⟩], [⟨11000, ofHex "51"⟩], 0⟩
def t2 : Tx := ⟨1, [⟨⟨ofHex "24ecb134dcdd478a54b5d1a4d28b8a31c4cde75e02618bf29bad7c36a40c2ed0", 0⟩, [], 4294967295, []⟩], [⟨6000, ofHex "51"⟩, ⟨5000, ofHex "6a"⟩], 0⟩
def hdr0 : BitcoinSer.Header := ⟨1, List.replicate 32 0, List.replicate 32 0, 0, 0, 0⟩
def blk18 : Block := ⟨hdr0, [cb18, t1, t2]⟩
def undo18 : BlockUndo := [[⟨⟨5000, ofHex "51"⟩, 50, false⟩, ⟨⟨7000, ofHex "51"⟩, 50, false⟩], [⟨⟨11000, ofHex "51"⟩, 200, false⟩]]
def conn18 : Ledger := (connectLoop ⟨true, true, true, true, true, true, true⟩ 200 (fun _ => 0) 0 ⟨base18, 0, 0, []⟩ blk18.vtx).map (·.utxo) |>.getD []
def undoLean : BlockUndo := (connectLoop ⟨true, true, true, true, true, true, true⟩ 200 (fun _ => 0) 0 ⟨base18, 0, 0, []⟩ blk18.vtx).map (·.undo) |>.getD []
#eval undoLean == undo18                                        -- the undo data the model records is what UpdateCoins moves out
#eval (getCoin conn18 ⟨txid t2, 1⟩).isNone                     -- an OP_RETURN output is never stored
#eval (getCoin conn18 ⟨txid t1, 0⟩).isNone                     -- spent in-block
def hashX : Bytes := List.replicate 32 9
def d1 := disconnectBlock conn18 200 hashX blk18 undo18
#eval res d1 == some true                                   -- clean round trip
#eval coinAt d1 ⟨ofHex "0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a", 0⟩ == some ⟨⟨5000, ofHex "51"⟩, 50, false⟩
#eval coinAt d1 ⟨ofHex "0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a", 1⟩ == some ⟨⟨7000, ofHex "51"⟩, 50, false⟩
#eval coinAt d1 ⟨ofHex "0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b", 0⟩ == some ⟨⟨5000000000, ofHex "51"⟩, 60, true⟩
#eval (d1.map fun p => p.1.length) == some 3                   -- nothing else remains
#eval res (disconnectBlock conn18 200 hashX blk18 (undo18.take 1)) == none       -- block and undo data inconsistent
#eval res (disconnectBlock conn18 200 hashX ⟨hdr0, [cb18, t1]⟩ undo18) == none
#eval res (disconnectBlock conn18 200 hashX blk18 [undo18.headD [] ++ [dummyCoin], undo18.getD 1 []]) == none   -- transaction and undo data inconsistent
#eval res (disconnectBlock (spendCoin conn18 ⟨txid t2, 0⟩) 200 hashX blk18 undo18) == some false   -- t2's output already spent: unclean
#eval (disconnectBlock (spendCoin conn18 ⟨txid t2, 0⟩) 200 hashX blk18 undo18).map (fun p => p.1.length) == some 3   -- but fully restored
#eval res (disconnectBlock conn18 201 hashX blk18 undo18) == some false         -- height mismatch on every output
#eval res (disconnectBlock (addCoin conn18 ⟨txid t2, 0⟩ ⟨⟨6000, [0x51]⟩, 200, true⟩) 200 hashX blk18 undo18) == some false   -- coinbase flag mismatch
#eval res (disconnectBlock (addCoin conn18 ⟨txid t2, 0⟩ ⟨⟨6001, [0x51]⟩, 200, false⟩) 200 hashX blk18 undo18) == some false   -- value mismatch
def connDup : Ledger := addCoin conn18 ⟨ofHex "0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a", 0⟩ ⟨⟨1, [0x51]⟩, 1, false⟩   -- A0 is somehow unspent already
#eval res (disconnectBlock connDup 200 hashX blk18 undo18) == some false
#eval coinAt (disconnectBlock connDup 200 hashX blk18 undo18) ⟨ofHex "0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a", 0⟩ == some ⟨⟨5000, ofHex "51"⟩, 50, false⟩   -- the undo coin overwrites
def undoH0a : BlockUndo := [[⟨⟨5000, ofHex "51"⟩, 50, false⟩, ⟨⟨7000, [0x51]⟩, 0, false⟩], [⟨⟨11000, ofHex "51"⟩, 200, false⟩]]
#eval res (disconnectBlock conn18 200 hashX blk18 undoH0a) == none            -- A1 is restored first (reverse order) and no unspent sibling exists: DISCONNECT_FAILED
def undoH0b : BlockUndo := [[⟨⟨5000, [0x51]⟩, 0, false⟩, ⟨⟨7000, ofHex "51"⟩, 50, false⟩], [⟨⟨11000, ofHex "51"⟩, 200, false⟩]]
#eval res (disconnectBlock conn18 200 hashX blk18 undoH0b) == some true       -- A0's metadata copied from the already-restored A1
#eval coinAt (disconnectBlock conn18 200 hashX blk18 undoH0b) ⟨ofHex "0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a", 0⟩ == some ⟨⟨5000, ofHex "51"⟩, 50, false⟩
def blkCb : Block := ⟨hdr0, [cb18]⟩
def connCb : Ledger := (connectLoop ⟨true, true, true, true, true, true, true⟩ 91722 (fun _ => 0) 0 ⟨base18, 0, 0, []⟩ blkCb.vtx).map (·.utxo) |>.getD []
#eval res (disconnectBlock (spendCoin connCb ⟨txid cb18, 0⟩) 91722 bip30Unspendable91722 blkCb []) == some true    -- overwritten coinbase: excused
#eval res (disconnectBlock (spendCoin connCb ⟨txid cb18, 0⟩) 91722 hashX blkCb []) == some false                   -- same height, other hash: unclean
#eval res (disconnectBlock (spendCoin connCb ⟨txid cb18, 0⟩) 91812 bip30Unspendable91812 blkCb []) == some true
#eval res (disconnectBlock (spendCoin connCb ⟨txid cb18, 0⟩) 91812 bip30Unspendable91722 blkCb []) == some false    -- the hash goes with its height
#eval res (disconnectBlock (spendCoin connCb ⟨txid cb18, 0⟩) 91722 bip30Unspendable91722 blkCb []) == some true
def conn22 : Ledger := (connectLoop ⟨true, true, true, true, true, true, true⟩ 91722 (fun _ => 0) 0 ⟨base18, 0, 0, []⟩ blk18.vtx).map (·.utxo) |>.getD []
def undo22 : BlockUndo := (connectLoop ⟨true, true, true, true, true, true, true⟩ 91722 (fun _ => 0) 0 ⟨base18, 0, 0, []⟩ blk18.vtx).map (·.undo) |>.getD []   -- undo data belongs to the height it was recorded at
#eval res (disconnectBlock (spendCoin conn22 ⟨txid t2, 0⟩) 91722 bip30Unspendable91722 blk18 undo22) == some false   -- the exception covers the coinbase only
#eval res (disconnectBlock (spendCoin conn22 ⟨txid cb18, 0⟩) 91722 bip30Unspendable91722 blk18 undo22) == some true
#eval res (disconnectBlock conn22 91722 hashX blk18 undo18) == some false       -- undo data recorded at height 200 restores t1's output with height 200: unclean at 91722
-- the two unspendable-coinbase hashes, display order
#eval bip30Unspendable91722.reverse == ofHex "00000000000271a2dc26e7667f8419f2e15416dc6955e5a6c6cdf3f2574dd08e"
#eval bip30Unspendable91812.reverse == ofHex "00000000000af0aed4792b1acee3d966af36cf5def14935db8de83d6f9306f2f"
#eval res (disconnectBlock conn18 200 hashX ⟨hdr0, [cb18, t2, t1]⟩ [undo18.getD 1 [], undo18.getD 0 []]) == some false   -- wrong block order: t1's output is spent when t1 is undone... (t1 undone first: its output is absent → unclean)
