"""Independent reference for spots 21 and 18 (REVIEW_SPOT21.md, REVIEW_SPOT18.md): CheckTransaction,
CheckTxInputs, and DisconnectBlock / ApplyTxInUndo over a dictionary coin view, written from the C++ only.
Emits tests/TxCheckVectors.lean and tests/UndoVectors.lean.  Usage: python3 -I txcheck_undo_reference.py OUT21 OUT18
"""
import sys, hashlib, struct

MAX_MONEY = 21_000_000 * 100_000_000
def money_range(v): return 0 <= v <= MAX_MONEY
NULL_HASH = bytes(32); NULL_N = 0xffffffff

# tx = dict(version, vin=[(hash, n, scriptSig, seq)], vout=[(value, spk)], lock)
def is_coinbase(tx): return len(tx["vin"]) == 1 and tx["vin"][0][0] == NULL_HASH and tx["vin"][0][1] == NULL_N
def cs(n): return bytes([n]) if n < 0xfd else (b"\xfd" + struct.pack("<H", n) if n <= 0xffff else b"\xfe" + struct.pack("<I", n))
def ser_stripped(tx):
    out = struct.pack("<I", tx["version"]) + cs(len(tx["vin"]))
    for h, n, ss, seq in tx["vin"]: out += h + struct.pack("<I", n) + cs(len(ss)) + ss + struct.pack("<I", seq)
    out += cs(len(tx["vout"]))
    for v, spk in tx["vout"]: out += struct.pack("<q", v) + cs(len(spk)) + spk
    return out + struct.pack("<I", tx["lock"])
def txid(tx): return hashlib.sha256(hashlib.sha256(ser_stripped(tx)).digest()).digest()

def check_transaction(tx):
    if not tx["vin"] or not tx["vout"]: return False
    if len(ser_stripped(tx)) * 4 > 4_000_000: return False
    total = 0
    for v, _ in tx["vout"]:
        if v < 0 or v > MAX_MONEY: return False
        total += v
        if not money_range(total): return False
    seen = set()
    for h, n, _, _ in tx["vin"]:
        if (h, n) in seen: return False
        seen.add((h, n))
    if is_coinbase(tx):
        return 2 <= len(tx["vin"][0][2]) <= 100
    return all(not (h == NULL_HASH and n == NULL_N) for h, n, _, _ in tx["vin"])

# coin view: dict (hash, n) -> (value, spk, height, coinbase)
def check_tx_inputs(view, tx, spend_height):
    """returns fee or None"""
    if not is_coinbase(tx) and any((h, n) not in view for h, n, _, _ in tx["vin"]): return None
    value_in = 0
    for h, n, _, _ in tx["vin"]:
        if (h, n) not in view: return None   # only a coinbase reaches here with a missing input; Core never calls this for one
        v, spk, height, cb = view[(h, n)]
        if cb and spend_height - height < 100: return None
        value_in += v
        if not money_range(v) or not money_range(value_in): return None
    value_out = sum(v for v, _ in tx["vout"])
    if value_in < value_out: return None
    fee = value_in - value_out
    if not money_range(fee): return None
    return fee

def unspendable(spk): return (len(spk) > 0 and spk[0] == 0x6a) or len(spk) > 10000

def add_coin(view, out, coin):
    if unspendable(coin[1]): return
    view[out] = coin

def update_coins(view, tx, height):
    """UpdateCoins: returns the CTxUndo (list of spent coins) for a non-coinbase"""
    undo = []
    if not is_coinbase(tx):
        for h, n, _, _ in tx["vin"]:
            undo.append(view.pop((h, n)))
    t = txid(tx)
    for i, (v, spk) in enumerate(tx["vout"]): add_coin(view, (t, i), (v, spk, height, is_coinbase(tx)))
    return undo

def apply_tx_in_undo(view, undo, out):
    """returns 'FAILED' | 'OK' | 'UNCLEAN'"""
    clean = out not in view
    v, spk, height, cb = undo
    if height == 0:
        alt = None
        for n in range(0, 10_000):   # AccessByTxid scans n upward
            if (out[0], n) in view: alt = view[(out[0], n)]; break
        if alt is None: return "FAILED"
        height, cb = alt[2], alt[3]
    add_coin(view, out, (v, spk, height, cb))
    return "OK" if clean else "UNCLEAN"

def disconnect_block(view, vtx, undos, height, bip30_unspendable):
    """returns None (FAILED) or clean flag"""
    if len(undos) + 1 != len(vtx): return None
    clean = True
    for i in range(len(vtx) - 1, -1, -1):
        tx = vtx[i]; t = txid(tx); cb = is_coinbase(tx); exc = cb and bip30_unspendable
        for o, (v, spk) in enumerate(tx["vout"]):
            if not unspendable(spk):
                coin = view.pop((t, o), None)
                if coin is None or coin[0] != v or coin[1] != spk or coin[2] != height or coin[3] != cb:
                    if not exc: clean = False
        if i > 0:
            undo = undos[i - 1]
            if len(undo) != len(tx["vin"]): return None
            for j in range(len(tx["vin"]) - 1, -1, -1):
                res = apply_tx_in_undo(view, undo[j], (tx["vin"][j][0], tx["vin"][j][1]))
                if res == "FAILED": return None
                clean = clean and res != "UNCLEAN"
    return clean

# ------------------------------------------------------------------ Lean emission helpers
HDR = "def hexVal (c : Char) : Nat := if c.isDigit then c.toNat - 48 else c.toLower.toNat - 87\ndef ofHexL : List Char → Bytes\n  | a :: b :: r => BitVec.ofNat 8 (hexVal a * 16 + hexVal b) :: ofHexL r\n  | _ => []\ndef ofHex (s : String) : Bytes := ofHexL s.toList"
def lb(b): return f"ofHex \"{b.hex()}\"" if b else "[]"
def lean_tx(tx):
    ins = ", ".join(f"⟨⟨{lb(h)}, {n}⟩, {lb(ss)}, {seq}, []⟩" for h, n, ss, seq in tx["vin"])
    outs = ", ".join(f"⟨{v}, {lb(spk)}⟩" for v, spk in tx["vout"])
    return f"⟨{tx['version']}, [{ins}], [{outs}], {tx['lock']}⟩"
def lean_coin(c): return f"⟨⟨{c[0]}, {lb(c[1])}⟩, {c[2]}, {'true' if c[3] else 'false'}⟩"
def lean_view(view): return "[" + ", ".join(f"(⟨{lb(h)}, {n}⟩, {lean_coin(c)})" for (h, n), c in view.items()) + "]"
def H(i): return bytes([i]) * 32
P2PK = bytes([0x51])  # OP_TRUE stands in for a script; only its bytes matter here

def spot21(out):
    L = ["import Definitions.Def_BitcoinBlockV2\nopen BitcoinBlockV2 BitcoinSer",
         "/-! Spot 21 vectors (`REVIEW_SPOT21.md`): `CheckTransaction` and `CheckTxInputs`, expectations from\n`tests/reference/txcheck_undo_reference.py`. Every line prints `true`. -/", HDR]
    def inp(i, n=0, ss=b"", seq=0xffffffff): return (H(i), n, ss, seq)
    cbin = (NULL_HASH, NULL_N, bytes(4), 0xffffffff)
    cases = [
        ("normal", dict(version=1, vin=[inp(1)], vout=[(1000, P2PK)], lock=0)),
        ("no inputs", dict(version=1, vin=[], vout=[(1000, P2PK)], lock=0)),
        ("no outputs", dict(version=1, vin=[inp(1)], vout=[], lock=0)),
        ("negative output", dict(version=1, vin=[inp(1)], vout=[(-1, P2PK)], lock=0)),
        ("output = MAX_MONEY", dict(version=1, vin=[inp(1)], vout=[(MAX_MONEY, P2PK)], lock=0)),
        ("output = MAX_MONEY + 1", dict(version=1, vin=[inp(1)], vout=[(MAX_MONEY + 1, P2PK)], lock=0)),
        ("two outputs summing to MAX_MONEY", dict(version=1, vin=[inp(1)], vout=[(MAX_MONEY - 1, P2PK), (1, P2PK)], lock=0)),
        ("two outputs summing to MAX_MONEY + 1", dict(version=1, vin=[inp(1)], vout=[(MAX_MONEY, P2PK), (1, P2PK)], lock=0)),
        ("zero-value output", dict(version=1, vin=[inp(1)], vout=[(0, P2PK)], lock=0)),
        ("duplicate prevout", dict(version=1, vin=[inp(1), inp(1)], vout=[(1, P2PK)], lock=0)),
        ("same hash, different index", dict(version=1, vin=[inp(1, 0), inp(1, 1)], vout=[(1, P2PK)], lock=0)),
        ("coinbase, scriptSig 2 bytes", dict(version=1, vin=[(NULL_HASH, NULL_N, bytes(2), 0xffffffff)], vout=[(1, P2PK)], lock=0)),
        ("coinbase, scriptSig 1 byte", dict(version=1, vin=[(NULL_HASH, NULL_N, bytes(1), 0xffffffff)], vout=[(1, P2PK)], lock=0)),
        ("coinbase, scriptSig 100 bytes", dict(version=1, vin=[(NULL_HASH, NULL_N, bytes(100), 0xffffffff)], vout=[(1, P2PK)], lock=0)),
        ("coinbase, scriptSig 101 bytes", dict(version=1, vin=[(NULL_HASH, NULL_N, bytes(101), 0xffffffff)], vout=[(1, P2PK)], lock=0)),
        ("non-coinbase with a null prevout", dict(version=1, vin=[inp(1), cbin], vout=[(1, P2PK)], lock=0)),
        ("null hash but index 0: not null, not a coinbase, accepted", dict(version=1, vin=[(NULL_HASH, 0, b"", 0xffffffff)], vout=[(1, P2PK)], lock=0)),
        ("index 0xffffffff but non-zero hash: accepted", dict(version=1, vin=[(H(2), NULL_N, b"", 0xffffffff)], vout=[(1, P2PK)], lock=0)),
        ("coinbase with 1-byte scriptSig: the length test, not the null-prevout test", dict(version=1, vin=[(NULL_HASH, NULL_N, b"\x00", 0xffffffff)], vout=[(1, P2PK)], lock=0)),
    ]
    for name, tx in cases:
        L.append(f"#eval checkTransaction {lean_tx(tx)} == {'true' if check_transaction(tx) else 'false'}   -- {name}")
    # size limit: stripped size * 4 <= 4,000,000 ; find the scriptSig length at the boundary
    base = dict(version=1, vin=[inp(1, 0, b"", 0xffffffff)], vout=[(1, P2PK)], lock=0)
    base_len = len(ser_stripped(base))  # with empty scriptSig (cs = 1 byte)
    Lss = 1_000_000 - (base_len - 1 + 5)   # cs(Lss) is 5 bytes for Lss > 0xffff
    big = dict(base, vin=[inp(1, 0, bytes(Lss), 0xffffffff)])
    assert len(ser_stripped(big)) == 1_000_000 and check_transaction(big)
    big1 = dict(base, vin=[inp(1, 0, bytes(Lss + 1), 0xffffffff)])
    assert not check_transaction(big1)
    L.append(f"def bigTx (k : Nat) : Tx := ⟨1, [⟨⟨{lb(H(1))}, 0⟩, List.replicate k 0, 0xffffffff, []⟩], [⟨1, [0x51]⟩], 0⟩")
    L.append(f"#eval (serTx false (bigTx {Lss})).length == 1000000")
    L.append(f"#eval checkTransaction (bigTx {Lss})               -- stripped size 1,000,000: weight exactly 4,000,000")
    L.append(f"#eval checkTransaction (bigTx {Lss + 1}) == false   -- one byte more")
    # CheckTxInputs
    L.append("-- CheckTxInputs(tx, view, nSpendHeight): `some fee` or `none`")
    view = {(H(1), 0): (5000, P2PK, 10, False), (H(1), 1): (7000, P2PK, 10, False), (H(2), 0): (50_0000_0000, P2PK, 100, True),
            (H(3), 0): (MAX_MONEY, P2PK, 10, False), (H(4), 0): (MAX_MONEY + 1, P2PK, 10, False), (H(5), 0): (-5, P2PK, 10, False)}
    L.append(f"def view21 : Ledger := {lean_view(view)}")
    tcases = [
        ("spend one coin, fee 1000", dict(version=1, vin=[inp(1, 0)], vout=[(4000, P2PK)], lock=0), 200),
        ("spend two coins, fee 0", dict(version=1, vin=[inp(1, 0), inp(1, 1)], vout=[(12000, P2PK)], lock=0), 200),
        ("value out exceeds value in", dict(version=1, vin=[inp(1, 0)], vout=[(5001, P2PK)], lock=0), 200),
        ("missing input", dict(version=1, vin=[inp(1, 0), inp(9, 0)], vout=[(1, P2PK)], lock=0), 200),
        ("coinbase coin at 100 spent at 199: immature", dict(version=1, vin=[inp(2, 0)], vout=[(1, P2PK)], lock=0), 199),
        ("coinbase coin at 100 spent at 200: mature", dict(version=1, vin=[inp(2, 0)], vout=[(1, P2PK)], lock=0), 200),
        ("coinbase coin spent below its height (truncated difference)", dict(version=1, vin=[inp(2, 0)], vout=[(1, P2PK)], lock=0), 50),
        ("non-coinbase coin at 10 spent at 11: no maturity rule", dict(version=1, vin=[inp(1, 0)], vout=[(1, P2PK)], lock=0), 11),
        ("coin of exactly MAX_MONEY", dict(version=1, vin=[inp(3, 0)], vout=[(1, P2PK)], lock=0), 200),
        ("coin above MAX_MONEY", dict(version=1, vin=[inp(4, 0)], vout=[(1, P2PK)], lock=0), 200),
        ("negative coin", dict(version=1, vin=[inp(5, 0)], vout=[(1, P2PK)], lock=0), 200),
        ("running total above MAX_MONEY", dict(version=1, vin=[inp(3, 0), inp(1, 0)], vout=[(1, P2PK)], lock=0), 200),
        ("the coinbase is not checked here (ConnectBlock skips it); a null prevout is simply missing", dict(version=1, vin=[cbin], vout=[(1, P2PK)], lock=0), 200),
    ]
    for name, tx, h in tcases:
        fee = check_tx_inputs(view, tx, h)
        if is_coinbase(tx): fee = None   # the Lean has no coinbase bypass; ConnectBlock never calls it for the coinbase
        exp = "none" if fee is None else f"some {fee}"
        L.append(f"#eval checkTxInputs view21 {lean_tx(tx)} {h} == {exp}   -- {name}")
    open(out, "w").write("\n".join(L) + "\n")

def spot18(out):
    L = ["import Definitions.Def_BitcoinBlockV2\nopen BitcoinBlockV2 BitcoinSer",
         "/-! Spot 18 vectors (`REVIEW_SPOT18.md`): `DisconnectBlock` and `ApplyTxInUndo` over small ledgers, expectations\nfrom `tests/reference/txcheck_undo_reference.py` (a dictionary coin view). Every line prints `true`. -/", HDR,
         "def res (r : Option (Ledger × Bool)) : Option Bool := r.map Prod.snd",
         "def coinAt (r : Option (Ledger × Bool)) (op : OutPoint) : Option Coin := r.bind fun p => getCoin p.1 op"]
    def inp(h, n=0): return (h, n, b"", 0xffffffff)
    cbin = (NULL_HASH, NULL_N, bytes([0x03, 0x01, 0x02]), 0xffffffff)
    # starting ledger: coins A0, A1 (height 50), B0 (height 60, coinbase)
    base = {(H(0xa), 0): (5000, P2PK, 50, False), (H(0xa), 1): (7000, P2PK, 50, False), (H(0xb), 0): (50_0000_0000, P2PK, 60, True)}
    cb = dict(version=1, vin=[cbin], vout=[(50_0000_0000 + 1000, P2PK), (0, bytes([0x6a, 0x01, 0x02]))], lock=0)   # second output unspendable
    t1 = dict(version=1, vin=[inp(H(0xa), 0), inp(H(0xa), 1)], vout=[(11000, P2PK)], lock=0)                  # fee 1000
    t2 = dict(version=1, vin=[inp(txid(t1), 0)], vout=[(6000, P2PK), (5000, bytes([0x6a]))], lock=0)         # spends t1 in-block
    H_ = 200
    def connect(view, vtx):
        undos = []
        for tx in vtx:
            u = update_coins(view, tx, H_)
            if not is_coinbase(tx): undos.append(u)
        return undos
    L.append(f"def base18 : Ledger := {lean_view(base)}")
    L.append(f"def cb18 : Tx := {lean_tx(cb)}\ndef t1 : Tx := {lean_tx(t1)}\ndef t2 : Tx := {lean_tx(t2)}")
    L.append("def hdr0 : BitcoinSer.Header := ⟨1, List.replicate 32 0, List.replicate 32 0, 0, 0, 0⟩")
    L.append("def blk18 : Block := ⟨hdr0, [cb18, t1, t2]⟩")
    # connected ledger and undo, computed by the reference
    view = dict(base); undos = connect(view, [cb, t1, t2])
    L.append(f"def undo18 : BlockUndo := [{', '.join('[' + ', '.join(lean_coin(c) for c in u) + ']' for u in undos)}]")
    L.append("def conn18 : Ledger := (connectLoop ⟨true, true, true, true, true, true, true⟩ 200 (fun _ => 0) 0 ⟨base18, 0, 0, []⟩ blk18.vtx).map (·.utxo) |>.getD []")
    L.append("def undoLean : BlockUndo := (connectLoop ⟨true, true, true, true, true, true, true⟩ 200 (fun _ => 0) 0 ⟨base18, 0, 0, []⟩ blk18.vtx).map (·.undo) |>.getD []")
    L.append("#eval undoLean == undo18                                        -- the undo data the model records is what UpdateCoins moves out")
    L.append(f"#eval (getCoin conn18 ⟨txid t2, 1⟩).isNone                     -- an OP_RETURN output is never stored")
    L.append(f"#eval (getCoin conn18 ⟨txid t1, 0⟩).isNone                     -- spent in-block")
    def lean_opt(x): return "none" if x is None else ("true" if x else "false")
    def case(name, view0, vtx, undos_, height, exc_hash=None, checks=()):
        v = dict(view0); r = disconnect_block(v, vtx, undos_, height, exc_hash is not None)
        return v, r
    # 1. clean round trip
    v, r = case("round trip", view, [cb, t1, t2], undos, H_)
    assert r is True and v == base
    L.append("def hashX : Bytes := List.replicate 32 9")
    L.append("def d1 := disconnectBlock conn18 200 hashX blk18 undo18")
    L.append(f"#eval res d1 == some {lean_opt(r)}                                   -- clean round trip")
    for (h, n), c in base.items():
        L.append(f"#eval coinAt d1 ⟨{lb(h)}, {n}⟩ == some {lean_coin(c)}")
    L.append("#eval (d1.map fun p => p.1.length) == some 3                   -- nothing else remains")
    # 2. undo count mismatch
    L.append("#eval res (disconnectBlock conn18 200 hashX blk18 (undo18.take 1)) == none       -- block and undo data inconsistent")
    L.append("#eval res (disconnectBlock conn18 200 hashX ⟨hdr0, [cb18, t1]⟩ undo18) == none")
    # 3. vprevout size mismatch
    L.append("#eval res (disconnectBlock conn18 200 hashX blk18 [undo18.headD [] ++ [dummyCoin], undo18.getD 1 []]) == none   -- transaction and undo data inconsistent")
    # 4. a coin already gone (spent by a later block): unclean but OK
    v2 = dict(view); v2.pop((txid(t2), 0))
    vv, r = case("missing output", v2, [cb, t1, t2], undos, H_); assert r is False and vv == base
    L.append(f"#eval res (disconnectBlock (spendCoin conn18 ⟨txid t2, 0⟩) 200 hashX blk18 undo18) == some false   -- t2's output already spent: unclean")
    L.append(f"#eval (disconnectBlock (spendCoin conn18 ⟨txid t2, 0⟩) 200 hashX blk18 undo18).map (fun p => p.1.length) == some 3   -- but fully restored")
    # 5. wrong height / wrong coinbase flag / wrong value: unclean
    L.append("#eval res (disconnectBlock conn18 201 hashX blk18 undo18) == some false         -- height mismatch on every output")
    L.append(f"#eval res (disconnectBlock (addCoin conn18 ⟨txid t2, 0⟩ ⟨⟨6000, [0x51]⟩, 200, true⟩) 200 hashX blk18 undo18) == some false   -- coinbase flag mismatch")
    L.append(f"#eval res (disconnectBlock (addCoin conn18 ⟨txid t2, 0⟩ ⟨⟨6001, [0x51]⟩, 200, false⟩) 200 hashX blk18 undo18) == some false   -- value mismatch")
    # 6. restoring over an existing coin: unclean, overwritten
    L.append(f"def connDup : Ledger := addCoin conn18 ⟨{lb(H(0xa))}, 0⟩ ⟨⟨1, [0x51]⟩, 1, false⟩   -- A0 is somehow unspent already")
    L.append(f"#eval res (disconnectBlock connDup 200 hashX blk18 undo18) == some false")
    L.append(f"#eval coinAt (disconnectBlock connDup 200 hashX blk18 undo18) ⟨{lb(H(0xa))}, 0⟩ == some {lean_coin(base[(H(0xa), 0)])}   -- the undo coin overwrites")
    # 7. undo coin with height 0: metadata from an unspent sibling, or FAILED. Inputs restore in reverse order,
    #    so A1 (input 1) is restored before A0 (input 0).
    u0 = [list(undos[0]), list(undos[1])]
    u0[0][1] = (7000, P2PK, 0, False)   # A1's undo lost its metadata: restored first, no sibling present yet
    vv, r = case("height-0 undo, no sibling yet", view, [cb, t1, t2], [tuple(u0[0]), tuple(u0[1])], H_)
    assert r is None
    L.append(f"def undoH0a : BlockUndo := [[{lean_coin(undos[0][0])}, ⟨⟨7000, [0x51]⟩, 0, false⟩], [{lean_coin(undos[1][0])}]]")
    L.append("#eval res (disconnectBlock conn18 200 hashX blk18 undoH0a) == none            -- A1 is restored first (reverse order) and no unspent sibling exists: DISCONNECT_FAILED")
    u1 = [list(undos[0]), list(undos[1])]
    u1[0][0] = (5000, P2PK, 0, False)   # A0's undo lost its metadata: A1 is restored before it
    vv, r = case("height-0 undo with sibling", view, [cb, t1, t2], [tuple(u1[0]), tuple(u1[1])], H_)
    assert r is True and vv == base
    L.append(f"def undoH0b : BlockUndo := [[⟨⟨5000, [0x51]⟩, 0, false⟩, {lean_coin(undos[0][1])}], [{lean_coin(undos[1][0])}]]")
    L.append("#eval res (disconnectBlock conn18 200 hashX blk18 undoH0b) == some true       -- A0's metadata copied from the already-restored A1")
    L.append(f"#eval coinAt (disconnectBlock conn18 200 hashX blk18 undoH0b) ⟨{lb(H(0xa))}, 0⟩ == some {lean_coin(base[(H(0xa), 0)])}")
    # 8. the BIP30 exceptions: at (91722, its hash) a missing coinbase output is not unclean; a missing t1 output still is
    L.append("def blkCb : Block := ⟨hdr0, [cb18]⟩")
    L.append("def connCb : Ledger := (connectLoop ⟨true, true, true, true, true, true, true⟩ 91722 (fun _ => 0) 0 ⟨base18, 0, 0, []⟩ blkCb.vtx).map (·.utxo) |>.getD []")
    L.append("#eval res (disconnectBlock (spendCoin connCb ⟨txid cb18, 0⟩) 91722 bip30Unspendable91722 blkCb []) == some true    -- overwritten coinbase: excused")
    L.append("#eval res (disconnectBlock (spendCoin connCb ⟨txid cb18, 0⟩) 91722 hashX blkCb []) == some false                   -- same height, other hash: unclean")
    L.append("#eval res (disconnectBlock (spendCoin connCb ⟨txid cb18, 0⟩) 91812 bip30Unspendable91812 blkCb []) == some true")
    L.append("#eval res (disconnectBlock (spendCoin connCb ⟨txid cb18, 0⟩) 91812 bip30Unspendable91722 blkCb []) == some false    -- the hash goes with its height")
    L.append("#eval res (disconnectBlock (spendCoin connCb ⟨txid cb18, 0⟩) 91722 bip30Unspendable91722 blkCb []) == some true")
    L.append("def conn22 : Ledger := (connectLoop ⟨true, true, true, true, true, true, true⟩ 91722 (fun _ => 0) 0 ⟨base18, 0, 0, []⟩ blk18.vtx).map (·.utxo) |>.getD []")
    L.append("def undo22 : BlockUndo := (connectLoop ⟨true, true, true, true, true, true, true⟩ 91722 (fun _ => 0) 0 ⟨base18, 0, 0, []⟩ blk18.vtx).map (·.undo) |>.getD []   -- undo data belongs to the height it was recorded at")
    L.append("#eval res (disconnectBlock (spendCoin conn22 ⟨txid t2, 0⟩) 91722 bip30Unspendable91722 blk18 undo22) == some false   -- the exception covers the coinbase only")
    L.append("#eval res (disconnectBlock (spendCoin conn22 ⟨txid cb18, 0⟩) 91722 bip30Unspendable91722 blk18 undo22) == some true")
    L.append("#eval res (disconnectBlock conn22 91722 hashX blk18 undo18) == some false       -- undo data recorded at height 200 restores t1's output with height 200: unclean at 91722")
    L.append("-- the two unspendable-coinbase hashes, display order")
    L.append("#eval bip30Unspendable91722.reverse == ofHex \"00000000000271a2dc26e7667f8419f2e15416dc6955e5a6c6cdf3f2574dd08e\"")
    L.append("#eval bip30Unspendable91812.reverse == ofHex \"00000000000af0aed4792b1acee3d966af36cf5def14935db8de83d6f9306f2f\"")
    # 9. in-block dependency: t2 spends t1; disconnecting t1 before t2 would be wrong; the reverse order restores t1's output then spends it
    L.append("#eval res (disconnectBlock conn18 200 hashX ⟨hdr0, [cb18, t2, t1]⟩ [undo18.getD 1 [], undo18.getD 0 []]) == some false   -- wrong block order: t1's output is spent when t1 is undone... (t1 undone first: its output is absent → unclean)")
    open(out, "w").write("\n".join(L) + "\n")

spot21(sys.argv[1]); spot18(sys.argv[2]); print("wrote", sys.argv[1], sys.argv[2])
