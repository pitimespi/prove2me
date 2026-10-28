"""Independent reference for spot 13 (REVIEW_SPOT13.md): IsFinalTx, CScript() << nHeight (the BIP34
coinbase prefix) and ContextualCheckBlock's cutoff rule, from the C++ only. Emits tests/ContextualVectors.lean."""
import sys

LOCKTIME_THRESHOLD = 500_000_000
SEQUENCE_FINAL = 0xffffffff

def scriptnum(n):
    """CScriptNum::serialize for n >= 0."""
    if n == 0: return b""
    out = bytearray()
    while n: out.append(n & 0xff); n >>= 8
    if out[-1] & 0x80: out.append(0)
    return bytes(out)

def push(data):
    L = len(data)
    if L < 0x4c: return bytes([L]) + data
    if L <= 0xff: return bytes([0x4c, L]) + data
    if L <= 0xffff: return bytes([0x4d, L & 0xff, L >> 8]) + data
    return bytes([0x4e]) + L.to_bytes(4, "little") + data

def height_script(n):
    """CScript() << (int64_t)n via push_int64."""
    if n == -1 or 1 <= n <= 16: return bytes([n + 0x50])
    if n == 0: return bytes([0x00])
    return push(scriptnum(n))

def is_final(locktime, sequences, height, time):
    if locktime == 0: return True
    if locktime < (height if locktime < LOCKTIME_THRESHOLD else time): return True
    return all(s == SEQUENCE_FINAL for s in sequences)

def main(out):
    L = ["import Definitions.Def_BitcoinBlockV2\nopen BitcoinBlockV2 BitcoinSer",
         "/-! Spot 13 vectors (`REVIEW_SPOT13.md`): `IsFinalTx`, the BIP34 `CScript() << nHeight` prefix, and\n`ContextualCheckBlock`'s cutoff and tests on synthetic chains. Expectations from `tests/reference/contextual_reference.py`.\nEvery line prints `true`. -/",
         "def hexVal (c : Char) : Nat := if c.isDigit then c.toNat - 48 else c.toLower.toNat - 87\ndef ofHexL : List Char → Bytes\n  | a :: b :: r => BitVec.ofNat 8 (hexVal a * 16 + hexVal b) :: ofHexL r\n  | _ => []\ndef ofHex (s : String) : Bytes := ofHexL s.toList"]
    L.append("-- CScript() << nHeight")
    for n in [0, 1, 2, 16, 17, 127, 128, 255, 256, 32767, 32768, 65535, 65536, 227931, 8388607, 8388608, 16777215, 16777216, 2147483647]:
        L.append(f"#eval heightScript {n} == ofHex \"{height_script(n).hex()}\"")
    L.append("-- IsFinalTx(tx, nBlockHeight, nBlockTime): (locktime, sequences, height, time)")
    def tx(lock, seqs):
        ins = ", ".join(f"⟨⟨List.replicate 32 1, {i}⟩, [], {s}, []⟩" for i, s in enumerate(seqs))
        return f"⟨1, [{ins}], [⟨1, [0x51]⟩], {lock}⟩"
    F = 0xffffffff
    cases = [(0, [0], 100, 0), (99, [0], 100, 0), (100, [0], 100, 0), (100, [F], 100, 0), (101, [F, F], 100, 0), (101, [F, 0], 100, 0),
             (499_999_999, [0], 1, 0), (499_999_999, [0], 500_000_000, 0), (500_000_000, [0], 10_000_000, 500_000_001), (500_000_000, [0], 10_000_000, 500_000_000),
             (500_000_000, [F], 0, 0), (1_700_000_000, [0], 900_000, 1_700_000_000), (1_700_000_000, [0], 900_000, 1_700_000_001), (1_700_000_000, [0xfffffffe], 0, 0),
             (5, [], 1, 0)]
    for lock, seqs, h, t in cases:
        L.append(f"#eval isFinalTx {tx(lock, seqs)} {h} {t} == {'true' if is_final(lock, seqs, h, t) else 'false'}   -- locktime {lock}, seqs {['%x' % s for s in seqs]}, height {h}, time {t}")
    L.append("-- ContextualCheckBlock on synthetic chains (only its own tests; PoW and CheckBlock are not involved)")
    L.append("def hdrT (t : Nat) : Header := ⟨1, List.replicate 32 0, List.replicate 32 0, t, 0x1d00ffff, 0⟩")
    L.append("/-- a chain of `n` headers with times 600 apart: the tip's MTP is the time of the 6th most recent block. -/\ndef chainN (n : Nat) : ChainState := ⟨(List.range n).map fun i => hdrT (1500000000 + 600 * i), []⟩")
    L.append("def cbAt (ss : Bytes) : Tx := ⟨1, [⟨⟨List.replicate 32 0, 0xffffffff⟩, ss, 0xffffffff, []⟩], [⟨5000000000, [0x51]⟩], 0⟩")
    L.append("def blk (S : ChainState) (txs : List Tx) : Block := ⟨hdrT (1500000000 + 600 * S.nextHeight), txs⟩")
    L.append("-- pre-BIP34 (next height 170): no height prefix needed, cutoff is the block's own time")
    L.append("#eval contextualCheckBlock (chainN 170) (blk (chainN 170) [cbAt [0x04, 0xff, 0xff, 0x00, 0x1d, 0x01, 0x02]])")
    L.append("#eval contextualCheckBlock (chainN 170) (blk (chainN 170) [cbAt [], ⟨1, [⟨⟨List.replicate 32 1, 0⟩, [], 0, []⟩], [⟨1, [0x51]⟩], 170⟩]) == false   -- locktime 170 = height: not final")
    L.append("#eval contextualCheckBlock (chainN 170) (blk (chainN 170) [cbAt [], ⟨1, [⟨⟨List.replicate 32 1, 0⟩, [], 0, []⟩], [⟨1, [0x51]⟩], 169⟩])   -- locktime 169 < height 170: final")
    L.append(f"#eval contextualCheckBlock (chainN 170) (blk (chainN 170) [cbAt [], ⟨1, [⟨⟨List.replicate 32 1, 0⟩, [], 0, []⟩], [⟨1, [0x51]⟩], {1500000000 + 600*170 - 1}⟩])   -- time lock just below the block time (pre-CSV cutoff): final")
    L.append(f"#eval contextualCheckBlock (chainN 170) (blk (chainN 170) [cbAt [], ⟨1, [⟨⟨List.replicate 32 1, 0⟩, [], 0, []⟩], [⟨1, [0x51]⟩], {1500000000 + 600*170}⟩]) == false   -- equal to the block time: not final")
    T0 = 1500000000 + 600*170
    assert is_final(170,[0],170,T0) is False and is_final(169,[0],170,T0) and is_final(T0-1,[0],170,T0) and not is_final(T0,[0],170,T0)
    L.append("-- BIP34 active (next height 227931): the coinbase scriptSig must start with the height push")
    hs = height_script(227931).hex()
    L.append(f"#eval heightScript 227931 == ofHex \"{hs}\"")
    L.append(f"#eval contextualCheckBlock (chainN 227931) (blk (chainN 227931) [cbAt (ofHex \"{hs}\" ++ [0x01, 0x02])])   -- prefix with trailing bytes")
    L.append(f"#eval contextualCheckBlock (chainN 227931) (blk (chainN 227931) [cbAt (ofHex \"{hs}\")])   -- exact")
    L.append(f"#eval contextualCheckBlock (chainN 227931) (blk (chainN 227931) [cbAt (ofHex \"{height_script(227930).hex()}\")]) == false   -- previous height")
    L.append(f"#eval contextualCheckBlock (chainN 227931) (blk (chainN 227931) [cbAt (ofHex \"{hs[:-2]}\")]) == false   -- truncated")
    L.append(f"#eval contextualCheckBlock (chainN 227931) (blk (chainN 227931) [cbAt (ofHex \"{'04' + hs[2:] + '00'}\")]) == false   -- non-minimal push of the same number is a different prefix")
    L.append(f"#eval contextualCheckBlock (chainN 227930) (blk (chainN 227930) [cbAt []])   -- next height 227930: not yet enforced")
    L.append("-- CSV active (next height 419328): the cutoff is the previous block's MTP, not the block time")
    mtp = 1500000000 + 600 * (419327 - 5)   # tip height 419327, MTP = time of height tip-5
    L.append(f"#eval (chainN 419328).mtp == {mtp}")
    L.append(f"#eval contextualCheckBlock (chainN 419328) (blk (chainN 419328) [cbAt (ofHex \"{height_script(419328).hex()}\"), ⟨1, [⟨⟨List.replicate 32 1, 0⟩, [], 0, []⟩], [⟨1, [0x51]⟩], {mtp - 1}⟩])   -- time lock below the MTP: final")
    L.append(f"#eval contextualCheckBlock (chainN 419328) (blk (chainN 419328) [cbAt (ofHex \"{height_script(419328).hex()}\"), ⟨1, [⟨⟨List.replicate 32 1, 0⟩, [], 0, []⟩], [⟨1, [0x51]⟩], {mtp}⟩]) == false   -- equal to the MTP: not final although below the block time")
    L.append(f"#eval contextualCheckBlock (chainN 419328) (blk (chainN 419328) [cbAt (ofHex \"{height_script(419328).hex()}\"), ⟨1, [⟨⟨List.replicate 32 1, 0⟩, [], 0xffffffff, []⟩], [⟨1, [0x51]⟩], {mtp + 100000}⟩])   -- SEQUENCE_FINAL ignores the lock time")
    L.append(f"#eval contextualCheckBlock (chainN 419327) (blk (chainN 419327) [cbAt (ofHex \"{height_script(419327).hex()}\"), ⟨1, [⟨⟨List.replicate 32 1, 0⟩, [], 0, []⟩], [⟨1, [0x51]⟩], {mtp}⟩])   -- one block earlier CSV is not active for the next block: block-time cutoff, final")
    assert is_final(mtp-1,[0],419328,mtp) and not is_final(mtp,[0],419328,mtp) and is_final(mtp+100000,[0xffffffff],419328,mtp)
    assert is_final(mtp,[0],419327,1500000000+600*419327)
    L.append("-- SegWit active (next height 481824): witness data without a commitment is rejected; before, the same")
    wtx = "⟨1, [⟨⟨List.replicate 32 1, 0⟩, [], 0, [[0x01]]⟩], [⟨1, [0x51]⟩], 0⟩"
    L.append(f"#eval contextualCheckBlock (chainN 481824) (blk (chainN 481824) [cbAt (ofHex \"{height_script(481824).hex()}\"), {wtx}]) == false")
    L.append(f"#eval contextualCheckBlock (chainN 481823) (blk (chainN 481823) [cbAt (ofHex \"{height_script(481823).hex()}\"), {wtx}]) == false   -- unexpected-witness applies when SegWit is not active too")
    L.append(f"#eval contextualCheckBlock (chainN 481824) (blk (chainN 481824) [cbAt (ofHex \"{height_script(481824).hex()}\")])   -- no witness, no commitment needed")
    L.append("-- weight: a coinbase whose scriptSig makes the block weigh exactly 4,000,000 passes, one byte more fails")
    # block weight = 4 * stripped size (no witness). stripped = 80 + 1 + tx size; tx size = 4 + 1 + (32+4+cs(ss)+len+4) + 1 + (8+1+1) + 4
    def cs(n): return 1 if n < 0xfd else 3 if n <= 0xffff else 5
    def stripped_block_size(L): return 80 + cs(1) + (4 + cs(1) + 32 + 4 + cs(L) + L + 4 + cs(1) + 8 + cs(1) + 1 + 4)
    Lss = next(L for L in range(999000, 1000000) if 4 * stripped_block_size(L) == 4_000_000)
    L.append(f"def bigSS : Bytes := ofHex \"{height_script(227931).hex()}\" ++ List.replicate ({Lss} - {len(height_script(227931))}) 0")
    L.append("#eval blockWeight (blk (chainN 227931) [cbAt bigSS]) == 4000000")
    L.append("#eval contextualCheckBlock (chainN 227931) (blk (chainN 227931) [cbAt bigSS])")
    L.append("#eval contextualCheckBlock (chainN 227931) (blk (chainN 227931) [cbAt (bigSS ++ [0])]) == false")
    open(out, "w").write("\n".join(L) + "\n"); print("wrote", out)

main(sys.argv[1])
