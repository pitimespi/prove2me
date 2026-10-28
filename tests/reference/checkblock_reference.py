"""Independent reference for spot 12 (REVIEW_SPOT12.md): BlockMerkleRoot with mutation detection,
BlockWitnessMerkleRoot, GetWitnessCommitmentIndex and CheckWitnessMalleation, written from the C++
without looking at the Lean. Emits tests/CheckBlockVectors.lean.

Usage: python3 checkblock_reference.py BLOCK586_RAW OUT_LEAN
"""
import hashlib, struct, sys

def sha256d(b): return hashlib.sha256(hashlib.sha256(b).digest()).digest()
def cs(n):
    if n < 0xfd: return bytes([n])
    if n <= 0xffff: return b"\xfd" + struct.pack("<H", n)
    return b"\xfe" + struct.pack("<I", n)

def merkle_root(hashes, want_mutation=False):
    """ComputeMerkleRoot(hashes, &mutated): returns (root, mutated)."""
    hashes = list(hashes); mutation = False
    while len(hashes) > 1:
        for pos in range(0, len(hashes) - 1, 2):
            if hashes[pos] == hashes[pos + 1]: mutation = True
        if len(hashes) & 1: hashes.append(hashes[-1])
        hashes = [sha256d(hashes[i] + hashes[i + 1]) for i in range(0, len(hashes), 2)]
    return (hashes[0] if hashes else bytes(32)), mutation

# --- minimal tx parser / serializer (witness-aware) ---
def read_cs(b, p):
    n = b[p]
    if n < 0xfd: return n, p + 1
    if n == 0xfd: return struct.unpack_from("<H", b, p + 1)[0], p + 3
    if n == 0xfe: return struct.unpack_from("<I", b, p + 1)[0], p + 5
    return struct.unpack_from("<Q", b, p + 1)[0], p + 9

def read_tx(b, p):
    start = p
    version = struct.unpack_from("<I", b, p)[0]; p += 4
    flags = 0
    n, q = read_cs(b, p)
    if n == 0 and b[q] != 0:  # marker + flag
        flags = b[q]; p = q + 1; n, p = read_cs(b, p)
    else: p = q
    vin = []
    for _ in range(n):
        prev = b[p:p + 32]; idx = struct.unpack_from("<I", b, p + 32)[0]; p += 36
        l, p = read_cs(b, p); ss = b[p:p + l]; p += l
        seq = struct.unpack_from("<I", b, p)[0]; p += 4
        vin.append([prev, idx, ss, seq, []])
    n, p = read_cs(b, p); vout = []
    for _ in range(n):
        v = struct.unpack_from("<q", b, p)[0]; p += 8
        l, p = read_cs(b, p); spk = b[p:p + l]; p += l
        vout.append((v, spk))
    if flags & 1:
        for i in range(len(vin)):
            k, p = read_cs(b, p); st = []
            for _ in range(k):
                l, p = read_cs(b, p); st.append(b[p:p + l]); p += l
            vin[i][4] = st
    lock = struct.unpack_from("<I", b, p)[0]; p += 4
    return dict(version=version, vin=vin, vout=vout, lock=lock), p

def ser_tx(tx, witness):
    has_w = witness and any(i[4] for i in tx["vin"])
    out = struct.pack("<I", tx["version"])
    if has_w: out += b"\x00\x01"
    out += cs(len(tx["vin"]))
    for prev, idx, ss, seq, _ in tx["vin"]:
        out += prev + struct.pack("<I", idx) + cs(len(ss)) + ss + struct.pack("<I", seq)
    out += cs(len(tx["vout"]))
    for v, spk in tx["vout"]:
        out += struct.pack("<q", v) + cs(len(spk)) + spk
    if has_w:
        for i in tx["vin"]:
            out += cs(len(i[4]))
            for e in i[4]: out += cs(len(e)) + e
    return out + struct.pack("<I", tx["lock"])

def txid(tx): return sha256d(ser_tx(tx, False))
def wtxid(tx): return sha256d(ser_tx(tx, True))   # equals txid when there is no witness

def commitment_index(vtx):
    pos = -1
    if vtx:
        for o, (_, spk) in enumerate(vtx[0]["vout"]):
            if len(spk) >= 38 and spk[:6] == bytes([0x6a, 0x24, 0xaa, 0x21, 0xa9, 0xed]): pos = o
    return pos

def witness_root(vtx):
    return merkle_root([bytes(32)] + [wtxid(t) for t in vtx[1:]])[0]

def check_witness_malleation(vtx, expect):
    if expect:
        pos = commitment_index(vtx)
        if pos != -1:
            stack = vtx[0]["vin"][0][4]
            if len(stack) != 1 or len(stack[0]) != 32: return False
            h = sha256d(witness_root(vtx) + stack[0])
            return h == vtx[0]["vout"][pos][1][6:38]
    return not any(any(i[4] for i in t["vin"]) for t in vtx)

# ---------------------------------------------------------------- Lean emission
def hexs(b): return b.hex()
def lean_tx(tx):
    ins = ", ".join(f"⟨⟨ofHex \"{hexs(prev)}\", {idx}⟩, ofHex \"{hexs(ss)}\", {seq}, [{', '.join('ofHex \"' + hexs(e) + '\"' for e in w)}]⟩"
                    for prev, idx, ss, seq, w in tx["vin"])
    outs = ", ".join(f"⟨{v}, ofHex \"{hexs(spk)}\"⟩" for v, spk in tx["vout"])
    return f"⟨{tx['version']}, [{ins}], [{outs}], {tx['lock']}⟩"

def main(raw_path, out_path):
    raw = open(raw_path, "rb").read()
    hdr = raw[:80]; n, p = read_cs(raw, 80); vtx = []
    for _ in range(n):
        t, p = read_tx(raw, p); vtx.append(t)
    assert p == len(raw) and n == 3
    merkle_hdr = hdr[36:68]
    root3, mut3 = merkle_root([txid(t) for t in vtx], True)
    assert root3 == merkle_hdr and not mut3
    vtx4 = vtx + [vtx[2]]                       # CVE-2012-2459 mutation: repeat the last tx
    root4, mut4 = merkle_root([txid(t) for t in vtx4], True)
    assert root4 == merkle_hdr and mut4
    vtx5 = vtx + [vtx[1], vtx[2]]               # [a,b,c,b,c]: different root, not flagged at any level
    root5, mut5 = merkle_root([txid(t) for t in vtx5], True)
    assert root5 != merkle_hdr and not mut5
    vtx_dup2 = [vtx[0], vtx[1], vtx[1]]         # [a,b,b]: root differs, no equal pair at an even position
    root_d, mut_d = merkle_root([txid(t) for t in vtx_dup2], True)
    assert not mut_d and root_d != merkle_hdr
    size_strip4 = 80 + len(cs(4)) + sum(len(ser_tx(t, False)) for t in vtx4)

    # --- synthetic witness-commitment cases (expectations from the C++ only) ---
    zero = bytes(32); nonce = bytes(range(32)); nonce31 = nonce[:31]
    def cb_with(outs, stack):
        return dict(version=1, vin=[[zero, 0xffffffff, b"\x03\x40\x42\x0f", 0xffffffff, stack]], vout=outs, lock=0)
    t1 = dict(version=2, vin=[[bytes([1]) * 32, 0, b"", 0xffffffff, [bytes([0x30, 0x44]), bytes([2]) * 33]]],
              vout=[(5000, bytes([0x00, 0x14]) + bytes([3]) * 20)], lock=0)
    t2 = dict(version=2, vin=[[bytes([4]) * 32, 1, b"\x16\x00\x14" + bytes([5]) * 20, 0xfffffffe, []]],
              vout=[(7000, bytes([0x6a]))], lock=0)
    pay = (5000000000, bytes([0x00, 0x14]) + bytes([9]) * 20)
    root_w = witness_root([cb_with([], []), t1, t2])
    good = sha256d(root_w + nonce)
    commit = (0, bytes([0x6a, 0x24, 0xaa, 0x21, 0xa9, 0xed]) + good)
    commit_bad = (0, bytes([0x6a, 0x24, 0xaa, 0x21, 0xa9, 0xed]) + sha256d(root_w + nonce31 + b"\x00"))
    commit_long = (0, commit[1] + b"\x01\x02")                       # extra bytes after the 38 are ignored
    short37 = (0, commit[1][:37])                                     # 37 bytes: not a commitment
    wrong_prefix = (0, bytes([0x6a, 0x24, 0xaa, 0x21, 0xa9, 0xee]) + good)
    cases = []  # (name, vtx, expect, expected)
    cases.append(("expect, commitment last, correct", [cb_with([pay, commit], [nonce]), t1, t2], True, True))
    cases.append(("expect, commitment first then pay", [cb_with([commit, pay], [nonce]), t1, t2], True, True))
    cases.append(("expect, two commitments: the last one counts", [cb_with([commit_bad, commit], [nonce]), t1, t2], True, True))
    cases.append(("expect, two commitments: the last one is wrong", [cb_with([commit, commit_bad], [nonce]), t1, t2], True, False))
    cases.append(("expect, commitment with trailing bytes", [cb_with([pay, commit_long], [nonce]), t1, t2], True, True))
    cases.append(("expect, 37-byte output is not a commitment, witness present", [cb_with([pay, short37], [nonce]), t1, t2], True, False))
    cases.append(("expect, wrong prefix byte, witness present", [cb_with([pay, wrong_prefix], [nonce]), t1, t2], True, False))
    cases.append(("expect, no commitment, no witness anywhere", [cb_with([pay], []), t2], True, True))
    cases.append(("expect, no commitment, witness in a later tx", [cb_with([pay], []), t1, t2], True, False))
    cases.append(("expect, commitment, nonce of 31 bytes", [cb_with([pay, commit], [nonce31]), t1, t2], True, False))
    cases.append(("expect, commitment, two-element stack", [cb_with([pay, commit], [nonce, nonce]), t1, t2], True, False))
    cases.append(("expect, commitment, empty coinbase witness", [cb_with([pay, commit], []), t1, t2], True, False))
    cases.append(("expect, commitment, witness root over a different tx order", [cb_with([pay, commit], [nonce]), t2, t1], True, False))
    cases.append(("expect, commitment computed over t1 alone, block has t1 only", [cb_with([pay, (0, commit[1][:6] + sha256d(witness_root([cb_with([], []), t1]) + nonce))], [nonce]), t1], True, True))
    cases.append(("expect, commitment with only the coinbase (root = hash of zero leaf)", [cb_with([pay, (0, commit[1][:6] + sha256d(zero + nonce))], [nonce])], True, True))
    cases.append(("not expected, no witness", [cb_with([pay], []), t2], False, True))
    cases.append(("not expected, coinbase witness only", [cb_with([pay], [nonce]), t2], False, False))
    cases.append(("not expected, commitment present and valid but witness present", [cb_with([pay, commit], [nonce]), t1, t2], False, False))
    cases.append(("not expected, commitment present, no witness at all", [cb_with([pay, commit], []), t2], False, True))
    for name, v, e, x in cases: assert check_witness_malleation(v, e) == x, name

    L = []
    L.append("import Definitions.Def_BitcoinBlockV2\nopen BitcoinBlockV2 BitcoinSer")
    L.append("/-! Spot 12 vectors (`REVIEW_SPOT12.md`): `CheckMerkleRoot` with CVE-2012-2459 mutation detection on\nmainnet block 586 (three transactions), `GetWitnessCommitmentIndex` and `CheckWitnessMalleation` on synthetic\nblocks. Expectations computed by `tests/reference/checkblock_reference.py`. Every line prints `true`. -/")
    L.append("def hexVal (c : Char) : Nat := if c.isDigit then c.toNat - 48 else c.toLower.toNat - 87\ndef ofHexL : List Char → Bytes\n  | a :: b :: r => BitVec.ofNat 8 (hexVal a * 16 + hexVal b) :: ofHexL r\n  | _ => []\ndef ofHex (s : String) : Bytes := ofHexL s.toList")
    L.append(f"-- mainnet block 586, hash 000000000d0d23516c5efd3af4eb951603bb30b2c93884b522a318b30e918ee7\ndef block586 : Block := ((readBlock true (ofHex \"{hexs(raw)}\")).map Prod.fst).getD genesisBlock")
    L.append("#eval block586.vtx.length == 3")
    L.append("#eval headerHash block586.header == (ofHex \"000000000d0d23516c5efd3af4eb951603bb30b2c93884b522a318b30e918ee7\").reverse")
    L.append("#eval checkHeaderPow block586.header")
    L.append(f"#eval blockMerkleRoot block586 == (ofHex \"{hexs(root3)}\", false)")
    L.append("#eval checkBlock block586")
    L.append("def mutated586 : Block := ⟨block586.header, block586.vtx ++ [block586.vtx.getLastD genesisCoinbase]⟩   -- [a,b,c,c]: same root, mutated")
    L.append(f"#eval (blockMerkleRoot mutated586).1 == block586.header.merkleRoot")
    L.append("#eval (blockMerkleRoot mutated586).2 == true")
    L.append("#eval checkBlock mutated586 == false                                   -- bad-txns-duplicate")
    L.append(f"#eval (serBlock false mutated586).length == {size_strip4}            -- 80 + 1 + stripped sizes; well within the limit")
    L.append("#eval (mutated586.vtx.drop 1).all (fun tx => !isCoinBase tx) && mutated586.vtx.all checkTransaction   -- nothing else rejects it")
    L.append("def dup586 : Block := ⟨block586.header, block586.vtx ++ [block586.vtx.getD 1 genesisCoinbase, block586.vtx.getD 2 genesisCoinbase]⟩   -- [a,b,c,b,c]: different root, no equal pair")
    L.append(f"#eval blockMerkleRoot dup586 == (ofHex \"{hexs(root5)}\", false)")
    L.append("#eval checkBlock dup586 == false                                       -- bad-txnmrklroot")
    L.append("def dup2_586 : Block := ⟨block586.header, [block586.vtx.getD 0 genesisCoinbase, block586.vtx.getD 1 genesisCoinbase, block586.vtx.getD 1 genesisCoinbase]⟩   -- [a,b,b]: the equal pair is at an odd position, not flagged")
    L.append(f"#eval blockMerkleRoot dup2_586 == (ofHex \"{hexs(root_d)}\", false)")
    L.append("def empty586 : Block := ⟨block586.header, []⟩")
    L.append("#eval blockMerkleRoot empty586 == (zeroHash, false)                    -- ComputeMerkleRoot of no hashes is uint256()")
    L.append("#eval checkBlock empty586 == false")
    L.append("def twoCb586 : Block := ⟨block586.header, [block586.vtx.getD 0 genesisCoinbase, block586.vtx.getD 0 genesisCoinbase, block586.vtx.getD 2 genesisCoinbase]⟩")
    L.append("#eval checkBlock twoCb586 == false                                     -- bad-cb-multiple (the root also differs)")
    L.append("-- witness commitment: synthetic blocks (PoW is not checked by these functions)")
    L.append(f"def t1 : Tx := {lean_tx(t1)}\ndef t2 : Tx := {lean_tx(t2)}")
    L.append(f"#eval wtxid t2 == txid t2                                              -- no witness: GetWitnessHash is the txid")
    L.append(f"#eval wtxid t1 == ofHex \"{hexs(wtxid(t1))}\"")
    L.append(f"#eval blockWitnessMerkleRoot ⟨genesisHeader, [genesisCoinbase, t1, t2]⟩ == ofHex \"{hexs(root_w)}\"   -- leaf 0 is zero, coinbase witness ignored")
    for i, (name, v, e, x) in enumerate(cases):
        L.append(f"def wb{i} : Block := ⟨genesisHeader, [{', '.join(lean_tx(t) for t in v)}]⟩")
        L.append(f"#eval checkWitnessMalleation wb{i} {'true' if e else 'false'} == {'true' if x else 'false'}   -- {name}")
    idx_cases = [(0, [cb_with([pay, commit], [nonce]), t1], 1), (1, [cb_with([commit, pay], [nonce])], 0),
                 (2, [cb_with([commit_bad, pay, commit], [nonce])], 2), (3, [cb_with([pay, short37], [])], None),
                 (4, [cb_with([pay, wrong_prefix], [])], None), (5, [cb_with([pay, commit_long], [])], 1),
                 (6, [t2, cb_with([commit], [])], None), (7, [], None), (8, [cb_with([], [])], None)]
    for i, v, x in idx_cases:
        assert (commitment_index(v) if commitment_index(v) != -1 else None) == x
        L.append(f"def ib{i} : Block := ⟨genesisHeader, [{', '.join(lean_tx(t) for t in v)}]⟩")
        L.append(f"#eval witnessCommitmentIndex ib{i} == {'none' if x is None else 'some ' + str(x)}")
    L.append("-- the commitment bytes are scriptPubKey[6..38); the commitment index ignores non-coinbase transactions (ib6)")
    open(out_path, "w").write("\n".join(L) + "\n")
    print("wrote", out_path, "cases", len(cases) + len(idx_cases))

if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
