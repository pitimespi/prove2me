"""Independent reference for spot 16 (REVIEW_SPOT16.md): serialize.h (WriteCompactSize /
ReadCompactSize with and without range_check, vector<T>, prevector), primitives/transaction.h
(SerializeTransaction / UnserializeTransaction with TX_NO_WITNESS / TX_WITH_WITNESS),
primitives/block.h (CBlockHeader, CBlock), ComputeHash / ComputeWitnessHash, GetTransactionWeight /
GetBlockWeight, written from the C++ at a773e1e33b349dc819b5a0edc1c7a4839dc73b48 without looking at
the Lean. Emits tests/SerEdgeVectors.lean.

Usage: python3 -I ser_reference.py OUT_LEAN
"""
import hashlib, struct, sys

MAX_SIZE = 0x02000000          # serialize.h
WITNESS_SCALE_FACTOR = 4       # consensus/consensus.h

def sha256d(b): return hashlib.sha256(hashlib.sha256(b).digest()).digest()

class Fail(Exception):
    """std::ios_base::failure"""

class Stream:
    def __init__(self, b): self.b = bytes(b); self.p = 0
    def read(self, n):
        if self.p + n > len(self.b): raise Fail("end of data")
        r = self.b[self.p:self.p + n]; self.p += n; return r
    def rest(self): return self.b[self.p:]

# ---- serialize.h ----
def write_compact_size(n):
    if n < 253: return bytes([n])
    if n <= 0xffff: return bytes([253]) + struct.pack("<H", n)
    if n <= 0xffffffff: return bytes([254]) + struct.pack("<I", n)
    return bytes([255]) + struct.pack("<Q", n)

def read_compact_size(s, range_check=True):
    ch = s.read(1)[0]
    if ch < 253: n = ch
    elif ch == 253:
        n = struct.unpack("<H", s.read(2))[0]
        if n < 253: raise Fail("non-canonical ReadCompactSize()")
    elif ch == 254:
        n = struct.unpack("<I", s.read(4))[0]
        if n < 0x10000: raise Fail("non-canonical ReadCompactSize()")
    else:
        n = struct.unpack("<Q", s.read(8))[0]
        if n < 0x100000000: raise Fail("non-canonical ReadCompactSize()")
    if range_check and n > MAX_SIZE: raise Fail("ReadCompactSize(): size too large")
    return n

def read_bytes(s):             # vector<unsigned char> / prevector<N, uint8_t>: range-checked size, raw bytes
    return s.read(read_compact_size(s))
def read_vector(s, f):         # VectorFormatter<DefaultFormatter>::Unser
    n = read_compact_size(s); return [f(s) for _ in range(n)]
def ser_bytes(b): return write_compact_size(len(b)) + bytes(b)
def ser_vector(f, v): return write_compact_size(len(v)) + b"".join(f(x) for x in v)

# ---- primitives/transaction.h ----
# tx = dict(version, vin=[dict(hash, n, scriptSig, nSequence, witness=[bytes...])], vout=[(nValue, spk)], nLockTime)
def ser_txin(i): return bytes(i["hash"]) + struct.pack("<I", i["n"]) + ser_bytes(i["scriptSig"]) + struct.pack("<I", i["nSequence"])
def ser_txout(o): return struct.pack("<q", o[0]) + ser_bytes(o[1])
def read_txin(s):
    h = s.read(32); n = struct.unpack("<I", s.read(4))[0]; ss = read_bytes(s); seq = struct.unpack("<I", s.read(4))[0]
    return dict(hash=h, n=n, scriptSig=ss, nSequence=seq, witness=[])
def read_txout(s):
    v = struct.unpack("<q", s.read(8))[0]; return (v, read_bytes(s))
def has_witness(tx): return any(len(i["witness"]) != 0 for i in tx["vin"])   # !scriptWitness.IsNull()

def serialize_transaction(tx, allow_witness):
    out = struct.pack("<I", tx["version"])
    flags = 0
    if allow_witness and has_witness(tx): flags |= 1
    if flags: out += ser_vector(ser_txin, []) + bytes([flags])
    out += ser_vector(ser_txin, tx["vin"]) + ser_vector(ser_txout, tx["vout"])
    if flags & 1:
        for i in tx["vin"]: out += ser_vector(ser_bytes, i["witness"])
    out += struct.pack("<I", tx["nLockTime"])
    return out

def unserialize_transaction(s, allow_witness):
    version = struct.unpack("<I", s.read(4))[0]
    flags = 0
    vin = read_vector(s, read_txin); vout = []
    if len(vin) == 0 and allow_witness:
        flags = s.read(1)[0]
        if flags != 0:
            vin = read_vector(s, read_txin); vout = read_vector(s, read_txout)
    else:
        vout = read_vector(s, read_txout)
    if (flags & 1) and allow_witness:
        flags ^= 1
        for i in vin: i["witness"] = read_vector(s, read_bytes)
        if not any(len(i["witness"]) != 0 for i in vin): raise Fail("Superfluous witness record")
    if flags: raise Fail("Unknown transaction optional data")
    lock = struct.unpack("<I", s.read(4))[0]
    return dict(version=version, vin=vin, vout=vout, nLockTime=lock)

def txid(tx): return sha256d(serialize_transaction(tx, False))
def wtxid(tx): return txid(tx) if not has_witness(tx) else sha256d(serialize_transaction(tx, True))
def tx_weight(tx): return len(serialize_transaction(tx, False)) * (WITNESS_SCALE_FACTOR - 1) + len(serialize_transaction(tx, True))

# ---- primitives/block.h ----
def ser_header(h):
    return struct.pack("<i", h["version"]) + bytes(h["prev"]) + bytes(h["merkle"]) + struct.pack("<III", h["time"], h["bits"], h["nonce"])
def read_header(s):
    v = struct.unpack("<i", s.read(4))[0]; p = s.read(32); m = s.read(32); t, b, n = struct.unpack("<III", s.read(12))
    return dict(version=v, prev=p, merkle=m, time=t, bits=b, nonce=n)
def ser_block(blk, allow_witness): return ser_header(blk["header"]) + ser_vector(lambda t: serialize_transaction(t, allow_witness), blk["vtx"])
def read_block(s, allow_witness): return dict(header=read_header(s), vtx=read_vector(s, lambda s: unserialize_transaction(s, allow_witness)))
def block_weight(blk): return len(ser_block(blk, False)) * (WITNESS_SCALE_FACTOR - 1) + len(ser_block(blk, True))

def try_read(f, b, *a):
    """Run a reader on bytes; return (value, remainder) or None where Core throws."""
    s = Stream(b)
    try: v = f(s, *a)
    except Fail: return None
    return v, s.rest()

# ---- Lean emission ----
def hx(b): return bytes(b).hex()
def lean_bytes(b): return f'ofHex "{hx(b)}"' if len(b) else "[]"
def lean_txin(i): return f'⟨⟨{lean_bytes(i["hash"])}, {i["n"]}⟩, {lean_bytes(i["scriptSig"])}, {i["nSequence"]}, [{", ".join(lean_bytes(w) for w in i["witness"])}]⟩'
def lean_txout(o): return f'⟨{o[0]}, {lean_bytes(o[1])}⟩'
def lean_tx(t): return f'⟨{t["version"]}, [{", ".join(lean_txin(i) for i in t["vin"])}], [{", ".join(lean_txout(o) for o in t["vout"])}], {t["nLockTime"]}⟩'
def lean_header(h): return f'⟨{h["version"]}, {lean_bytes(h["prev"])}, {lean_bytes(h["merkle"])}, {h["time"]}, {h["bits"]}, {h["nonce"]}⟩'
def lean_opt(v, inner): return "none" if v is None else f"some ({inner(v[0])}, {lean_bytes(v[1])})"

def main(out_path):
    L = ["import Definitions.Def_BitcoinSer", "open BitcoinSer",
         "/-! Spot 16 vectors (`REVIEW_SPOT16.md`): CompactSize canonical-encoding and range-check edge cases,",
         "`UnserializeTransaction` flag-byte edge cases (empty vin, superfluous witness, unknown flag), witness",
         "round trips, `ComputeHash`/`ComputeWitnessHash`, header/block round trips, and weights. Expectations",
         "computed by `tests/reference/ser_reference.py`. Every line prints `true`. -/",
         "def hexVal (c : Char) : Nat := if c.isDigit then c.toNat - 48 else c.toLower.toNat - 87",
         "def ofHexL : List Char → Bytes", "  | a :: b :: r => BitVec.ofNat 8 (hexVal a * 16 + hexVal b) :: ofHexL r", "  | _ => []",
         "def ofHex (s : String) : Bytes := ofHexL s.toList",
         'def hex (b : Bytes) : String := String.join (b.map fun x => let s := (Nat.toDigits 16 x.toNat); String.ofList (if s.length = 1 then \'0\' :: s else s))',
         "-- CompactSize: canonical-encoding rejections (both with and without the range check)"]
    bad = [bytes([0xfd, 0, 0]), bytes([0xfd, 0xfc, 0]), bytes([0xfe, 0xff, 0xff, 0, 0]), bytes([0xff, 0xff, 0xff, 0xff, 0xff, 0, 0, 0, 0])]
    for b in bad:
        for rc in (True, False):
            assert try_read(read_compact_size, b, rc) is None
            L.append(f'#eval readCompactSize {str(rc).lower()} (ofHex "{hx(b)}") == none')
    L.append("-- CompactSize: boundary values accepted, trailing byte returned")
    good = [bytes([0xfd, 0xfd, 0]), bytes([0xfe, 0, 0, 1, 0]), bytes([0xff, 0, 0, 0, 0, 1, 0, 0, 0]), bytes([0xfc]), bytes([0xfd, 0xff, 0xff]), bytes([0xfe, 0xff, 0xff, 0xff, 0xff]),
            bytes([0xfe, 0, 0, 0, 2]), bytes([0xfe, 1, 0, 0, 2]), bytes([0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff])]
    for b in good:
        for rc in (True, False):
            r = try_read(read_compact_size, b + bytes([0x42]), rc)
            exp = "none" if r is None else f"some ({r[0]}, [0x42])"
            L.append(f'#eval readCompactSize {str(rc).lower()} (ofHex "{hx(b)}42") == {exp}')
    L.append("-- CompactSize: truncated inputs")
    for b in [b"", bytes([0xfd]), bytes([0xfd, 1]), bytes([0xfe, 0, 0, 1]), bytes([0xff, 0, 0, 0, 0, 1, 0, 0])]:
        assert try_read(read_compact_size, b, True) is None
        L.append(f'#eval readCompactSize true ({lean_bytes(b)}) == none')
    L.append("-- WriteCompactSize at the boundaries")
    for n in [0, 252, 253, 0xffff, 0x10000, 0xffffffff, 0x100000000, MAX_SIZE]:
        L.append(f'#eval hex (writeCompactSize {n}) == "{hx(write_compact_size(n))}"')
    L.append("-- readBytes / readList: a range-checked count (0x02000001 rejected even though the bytes would be short anyway)")
    L.append(f'#eval readBytes (ofHex "fe01000002") == none')
    L.append(f'#eval readBytes (ofHex "03aabbccdd") == some (ofHex "aabbcc", ofHex "dd")')
    L.append(f'#eval readBytes (ofHex "03aabb") == none')
    L.append(f'#eval readList (readLE 1) (ofHex "fd0000") == none')
    L.append(f'#eval readList (readLE 1) (ofHex "020a0b0c") == some ([10, 11], [0x0c])')

    # ---- transactions ----
    H = lambda k: bytes([k]) * 32
    tin = lambda k, ss=b"", seq=0xffffffff, w=(): dict(hash=H(k), n=k, scriptSig=ss, nSequence=seq, witness=[bytes(x) for x in w])
    txs = {}
    txs["tEmpty"] = dict(version=1, vin=[], vout=[], nLockTime=0)
    txs["tNoInOneOut"] = dict(version=1, vin=[], vout=[(5000000000, bytes([0x51]))], nLockTime=0)
    txs["tNoInZeroVal"] = dict(version=1, vin=[], vout=[(0, b"")], nLockTime=0)
    txs["tPlain"] = dict(version=2, vin=[tin(0x11, bytes([0x00, 0x01]), 0xfffffffe)], vout=[(1, bytes([0x6a]))], nLockTime=500000)
    txs["tWit2"] = dict(version=2, vin=[tin(0x11, b"", 0, ()), tin(0x22, bytes([0x51]), 0xffffffff, (bytes([1, 2, 3]), b"", bytes([0xaa]) * 2))],
                        vout=[(-1, bytes([0x51])), (2 ** 63 - 1, b"")], nLockTime=0xffffffff)
    txs["tWitEmptyElem"] = dict(version=0xffffffff, vin=[tin(0x33, b"", 1, (b"",))], vout=[(0, b"")], nLockTime=0)
    txs["tAllEmptyWit"] = dict(version=1, vin=[tin(0x11), tin(0x22)], vout=[(0, b"")], nLockTime=0)
    for k, t in txs.items(): L.append(f"def {k} : Tx := {lean_tx(t)}")
    L.append("-- hasWitness: some input has a non-empty stack (an empty element still counts)")
    for k, t in txs.items():
        L.append(f"#eval {k}.hasWitness == {str(has_witness(t)).lower()}")
    L.append("-- SerializeTransaction with and without witness, and round trips (trailing byte 0x99 returned)")
    for k, t in txs.items():
        for aw in (True, False):
            b = serialize_transaction(t, aw)
            L.append(f'#eval hex (serTx {str(aw).lower()} {k}) == "{hx(b)}"')
            for raw in (True, False):
                r = try_read(unserialize_transaction, b + bytes([0x99]), raw)
                exp = "none" if r is None else f"some ({lean_tx(r[0])}, {lean_bytes(r[1])})"   # the remainder is [0x99] only when the modes agree
                L.append(f'#eval readTx {str(raw).lower()} (serTx {str(aw).lower()} {k} ++ [0x99]) == {exp}')
    L.append("-- a tx whose witnesses are all empty serializes without the flag; stripWitness is the TX_NO_WITNESS read")
    L.append("#eval serTx true tAllEmptyWit == serTx false tAllEmptyWit")
    L.append("#eval serTx true tWit2 ≠ serTx false tWit2")
    L.append("#eval (serTx true tWit2).take 6 == ofHex \"020000000001\"")
    L.append("#eval readTx false (serTx false tWit2) == some (tWit2.stripWitness, [])")
    L.append("#eval (readTx true (serTx true tWit2)).map (fun p => p.1.stripWitness) == some tWit2.stripWitness")
    L.append("-- hand-built flag-byte edge cases")
    one_in = ser_vector(ser_txin, [tin(0x11)]); one_out = ser_vector(ser_txout, [(7, bytes([0x51]))]); lock = struct.pack("<I", 0)
    cases = [
        ("flag 1 but the single witness stack is empty: Superfluous witness record", struct.pack("<I", 1) + bytes([0, 1]) + one_in + one_out + bytes([0]) + lock),
        ("flag 1, two inputs, both stacks empty", struct.pack("<I", 1) + bytes([0, 1]) + ser_vector(ser_txin, [tin(0x11), tin(0x22)]) + one_out + bytes([0, 0]) + lock),
        ("flag 1 with an empty re-read vin: no stacks, Superfluous witness record", struct.pack("<I", 1) + bytes([0, 1, 0, 0]) + lock),
        ("flag 2: Unknown transaction optional data", struct.pack("<I", 1) + bytes([0, 2]) + one_in + one_out + lock),
        ("flag 3 with a real witness: bit 1 is consumed, flag 2 remains", struct.pack("<I", 1) + bytes([0, 3]) + one_in + one_out + bytes([1, 1, 0xab]) + lock),
        ("flag 1 with a real witness: ok", struct.pack("<I", 1) + bytes([0, 1]) + one_in + one_out + bytes([1, 1, 0xab]) + lock),
        ("flag 0x81: 0x80 remains", struct.pack("<I", 1) + bytes([0, 0x81]) + one_in + one_out + bytes([1, 1, 0xab]) + lock),
        ("flag 1 with a witness whose stack has one empty element: ok (stack non-empty)", struct.pack("<I", 1) + bytes([0, 1]) + one_in + one_out + bytes([1, 0]) + lock),
        ("empty vin then no flag byte: short read", struct.pack("<I", 1) + bytes([0])),
        ("empty vin, flag 0, then nLockTime: vout is not read", struct.pack("<I", 1) + bytes([0, 0]) + struct.pack("<I", 0xdeadbeef)),
        ("empty vin, flag 0, output count byte would follow: it is the flag, vout stays empty, the rest is nLockTime", struct.pack("<I", 1) + bytes([0, 0]) + bytes([1, 2, 3, 4, 5])),
        ("witness tx truncated by one byte", serialize_transaction(txs["tWit2"], True)[:-1]),
        ("witness tx with a non-canonical stack-element length", struct.pack("<I", 1) + bytes([0, 1]) + one_in + one_out + bytes([1, 0xfd, 1, 0, 0xab]) + lock),
        ("vin count 0x02000001 (above MAX_SIZE) is rejected before any input is read", struct.pack("<I", 1) + bytes([0xfe, 1, 0, 0, 2])),
    ]
    for name, b in cases:
        for raw in (True, False):
            r = try_read(unserialize_transaction, b, raw)
            exp = "none" if r is None else f"some ({lean_tx(r[0])}, {lean_bytes(r[1])})"
            L.append(f'#eval readTx {str(raw).lower()} (ofHex "{hx(b)}") == {exp}   -- {name}')
    L.append("-- ComputeHash (witness-stripped), ComputeWitnessHash (= txid without witness), weights")
    for k, t in txs.items():
        L.append(f'#eval hex (txid {k}) == "{hx(txid(t))}"')
        L.append(f'#eval hex (wtxid {k}) == "{hx(wtxid(t))}"')
        L.append(f'#eval txWeight {k} == {tx_weight(t)}')
    L.append("#eval wtxid tAllEmptyWit == txid tAllEmptyWit")
    L.append("#eval wtxid tWit2 ≠ txid tWit2")
    L.append(f"#eval txWeight tWit2 == 3 * {len(serialize_transaction(txs['tWit2'], False))} + {len(serialize_transaction(txs['tWit2'], True))}")
    L.append("-- CAmount is int64 two's complement; version and nLockTime are uint32")
    L.append('#eval hex (serInt64 (-1)) == "ffffffffffffffff"')
    L.append(f'#eval hex (serInt64 (-(2^63))) == "{struct.pack("<q", -2**63).hex()}"')
    L.append(f'#eval hex (serInt64 (2^63 - 1)) == "{struct.pack("<q", 2**63 - 1).hex()}"')
    L.append('#eval readInt64 (ofHex "ffffffffffffffff") == some (-1, [])')
    L.append('#eval readInt64 (ofHex "0000000000000080") == some (-(2^63), [])')
    L.append('#eval readInt64 (ofHex "ffffffffffffff7f") == some (2^63 - 1, [])')
    L.append('#eval readTxOut (ofHex "ffffffffffffffff00") == some (⟨-1, []⟩, [])')
    L.append('#eval (readTx true (serTx true tWitEmptyElem)).map (fun p => p.1.version) == some 4294967295')
    L.append('#eval (readTx true (serTx true tWit2)).map (fun p => p.1.nLockTime) == some 4294967295')

    # ---- headers and blocks ----
    genesis_cb = dict(version=1, vin=[dict(hash=bytes(32), n=0xffffffff, scriptSig=bytes.fromhex("04ffff001d0104455468652054696d65732030332f4a616e2f32303039204368616e63656c6c6f72206f6e206272696e6b206f66207365636f6e64206261696c6f757420666f722062616e6b73"), nSequence=0xffffffff, witness=[])],
                      vout=[(5000000000, bytes.fromhex("4104678afdb0fe5548271967f1a67130b7105cd6a828e03909a67962e0ea1f61deb649f6bc3f4cef38c4f35504e51ec112de5c384df7ba0b8d578a4c702b6bf11d5fac"))], nLockTime=0)
    genesis_h = dict(version=1, prev=bytes(32), merkle=txid(genesis_cb), time=1231006505, bits=0x1d00ffff, nonce=2083236893)
    gh = ser_header(genesis_h)
    assert gh.hex() == "0100000000000000000000000000000000000000000000000000000000000000000000003ba3edfd7a7b12b27ac72c3e67768f617fc81bc3888a51323a9fb8aa4b1e5e4a29ab5f49ffff001d1dac2b7c"
    assert sha256d(gh)[::-1].hex() == "000000000019d6689c085ae165831e934ff763ae46a2a6c172b3f1b60a8ce26f"
    L.append("-- CBlockHeader: int32_t nVersion; the genesis header and version -1 / INT32_MIN / INT32_MAX")
    L.append(f'#eval hex (serHeader genesisHeader) == "{gh.hex()}"')
    L.append(f'#eval readHeader (serHeader genesisHeader ++ [1]) == some (genesisHeader, [1])')
    L.append(f'#eval readHeader (ofHex "{gh.hex()}") == some (genesisHeader, [])')
    L.append(f'#eval readHeader (ofHex "{gh[:-1].hex()}") == none')
    for v in (-1, -2 ** 31, 2 ** 31 - 1):
        h = dict(genesis_h, version=v); b = ser_header(h)
        L.append(f'def hdr{v if v >= 0 else "m" + str(-v)} : Header := {lean_header(h)}')
        L.append(f'#eval hex (serHeader hdr{v if v >= 0 else "m" + str(-v)}) == "{b.hex()}"')
        L.append(f'#eval readHeader (ofHex "{b.hex()}") == some (hdr{v if v >= 0 else "m" + str(-v)}, [])')
        L.append(f'#eval hex (headerHash hdr{v if v >= 0 else "m" + str(-v)}) == "{sha256d(b).hex()}"')
    L.append('#eval (readHeader (ofHex "ffffffff" ++ List.replicate 76 0)).map (fun p => p.1.version) == some (-1)')
    L.append('#eval (readHeader (ofHex "00000080" ++ List.replicate 76 0)).map (fun p => p.1.version) == some (-2147483648)')
    L.append('#eval (readHeader (ofHex "ffffff7f" ++ List.replicate 76 0)).map (fun p => p.1.version) == some 2147483647')
    L.append("-- CBlock with witness transactions: GetSerializeSize(TX_NO_WITNESS(block)), GetBlockWeight, round trips")
    blk = dict(header=genesis_h, vtx=[genesis_cb, txs["tWit2"], txs["tPlain"], txs["tWitEmptyElem"]])
    L.append('def blkW : Block := ⟨genesisHeader, [genesisCoinbase, tWit2, tPlain, tWitEmptyElem]⟩')
    nw = ser_block(blk, False); ww = ser_block(blk, True)
    L.append(f'#eval (serBlock false blkW).length == {len(nw)}')
    L.append(f'#eval (serBlock false blkW).length == 80 + 1 + {" + ".join(str(len(serialize_transaction(t, False))) for t in blk["vtx"])}')
    L.append(f'#eval (serBlock true blkW).length == {len(ww)}')
    L.append(f'#eval hex (serBlock true blkW) == "{ww.hex()}"')
    L.append(f'#eval hex (serBlock false blkW) == "{nw.hex()}"')
    L.append(f'#eval blockWeight blkW == {block_weight(blk)}')
    L.append(f'#eval blockWeight blkW == 3 * {len(nw)} + {len(ww)}')
    L.append(f'#eval blockWeight blkW == (blkW.vtx.map txWeight).sum + 4 * 81')
    L.append('#eval readBlock true (serBlock true blkW ++ [5]) == some (blkW, [5])')
    L.append('#eval readBlock false (serBlock false blkW) == some (⟨genesisHeader, blkW.vtx.map Tx.stripWitness⟩, [])')
    r = try_read(read_block, ww, False)
    L.append(f'#eval readBlock false (serBlock true blkW) == {lean_opt(r, lambda b: "⟨" + lean_header(b["header"]) + ", [" + ", ".join(lean_tx(t) for t in b["vtx"]) + "]⟩") if r else "none"}   -- witness bytes read as TX_NO_WITNESS')
    L.append('#eval readBlock true (serBlock true blkW).dropLast == none')
    L.append(f'#eval blockWeight genesisBlock == {block_weight(dict(header=genesis_h, vtx=[genesis_cb]))}')
    L.append('#eval blockWeight genesisBlock == 4 * (serBlock false genesisBlock).length')
    open(out_path, "w").write("\n".join(L) + "\n")
    print("wrote", out_path, "evals", sum(1 for l in L if l.startswith("#eval")))

if __name__ == "__main__":
    main(sys.argv[1])
