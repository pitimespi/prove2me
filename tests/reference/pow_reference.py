"""Independent reference for spot 15 (REVIEW_SPOT15.md): arith_uint256::SetCompact / GetCompact
(arith_uint256.cpp), DeriveTarget / CheckProofOfWorkImpl / CalculateNextWorkRequired /
GetNextWorkRequired / PermittedDifficultyTransition (pow.cpp) and GetBitsProof (chain.cpp) at the
mainnet parameters of kernel/chainparams.cpp, written from the C++ only. A 256-bit arith_uint256 is
modelled by a Python int kept below 2**256 with the same truncations as the C++ word loops
(operator<<= and operator*=(uint32_t) drop the carries out of the top word; operator/= is exact
integer division). Emits tests/PowVectors.lean.

Usage: python3 -I pow_reference.py OUT_LEAN
"""
import sys

M256 = 1 << 256
M64 = 1 << 64
M32 = 1 << 32

# kernel/chainparams.cpp, CMainParams
POW_LIMIT = int("00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffff", 16)
TARGET_TIMESPAN = 14 * 24 * 60 * 60
TARGET_SPACING = 10 * 60
INTERVAL = TARGET_TIMESPAN // TARGET_SPACING  # 2016
F_POW_ALLOW_MIN_DIFFICULTY = False
F_POW_NO_RETARGETING = False
ENFORCE_BIP94 = False


def shl256(a, shift):
    """base_uint<256>::operator<<=: words above index 7 are discarded."""
    return (a << shift) % M256


def mul256_u32(a, b32):
    """base_uint<256>::operator*=(uint32_t): the final carry is dropped."""
    assert 0 <= b32 < M32
    return (a * b32) % M256


def bits256(a):
    """base_uint::bits(): position of the highest set bit plus one, 0 for 0."""
    return a.bit_length()


def set_compact(n_compact):
    """arith_uint256::SetCompact(nCompact, &fNegative, &fOverflow) -> (value, fNegative, fOverflow).
    Note that for nSize <= 3 the C++ shifts nWord in place *before* the flags are computed."""
    n_compact &= 0xffffffff
    n_size = n_compact >> 24
    n_word = n_compact & 0x007fffff
    if n_size <= 3:
        n_word = (n_word >> (8 * (3 - n_size))) & 0xffffffff
        value = n_word
    else:
        value = shl256(n_word, 8 * (n_size - 3))
    f_negative = n_word != 0 and (n_compact & 0x00800000) != 0
    f_overflow = n_word != 0 and ((n_size > 34) or (n_word > 0xff and n_size > 33) or
                                  (n_word > 0xffff and n_size > 32))
    return value, f_negative, f_overflow


def get_compact(value, f_negative=False):
    """arith_uint256::GetCompact(fNegative)."""
    assert 0 <= value < M256
    n_size = (bits256(value) + 7) // 8  # CeilDiv(bits(), 8u)
    if n_size <= 3:
        n_compact = ((value % M64) << (8 * (3 - n_size))) % M32  # GetLow64() << ..., stored in uint32_t
    else:
        bn = value >> (8 * (n_size - 3))
        n_compact = (bn % M64) % M32
    if n_compact & 0x00800000:
        n_compact >>= 8
        n_size += 1
    assert (n_compact & ~0x007fffff) == 0
    assert n_size < 256
    n_compact |= n_size << 24
    n_compact |= 0x00800000 if (f_negative and (n_compact & 0x007fffff)) else 0
    return n_compact


def derive_target(n_bits, pow_limit=POW_LIMIT):
    """DeriveTarget: None when negative, zero, overflowing or above pow_limit."""
    t, neg, ovf = set_compact(n_bits)
    if neg or t == 0 or ovf or t > pow_limit:
        return None
    return t


def check_proof_of_work(hash_value, n_bits):
    """CheckProofOfWorkImpl(hash, nBits): hash read as a little-endian 256-bit number."""
    t = derive_target(n_bits)
    if t is None:
        return False
    if hash_value > t:
        return False
    return True


def calculate_next_work_required(last_bits, last_time, first_time):
    """CalculateNextWorkRequired(pindexLast, nFirstBlockTime, params) at mainnet parameters."""
    if F_POW_NO_RETARGETING:
        return last_bits
    actual = last_time - first_time  # int64_t
    if actual < TARGET_TIMESPAN // 4:
        actual = TARGET_TIMESPAN // 4
    if actual > TARGET_TIMESPAN * 4:
        actual = TARGET_TIMESPAN * 4
    bn_new, _, _ = set_compact(last_bits)  # enforce_BIP94 is false: pindexLast->nBits
    # bnNew *= nActualTimespan: int64_t -> uint32_t is a standard conversion, so the
    # operator*=(uint32_t) overload is chosen; the clamped value is < 2**32 anyway.
    bn_new = mul256_u32(bn_new, actual & 0xffffffff)
    bn_new //= TARGET_TIMESPAN  # operator/=(const base_uint&), exact division
    if bn_new > POW_LIMIT:
        bn_new = POW_LIMIT
    return get_compact(bn_new)


def get_next_work_required(last_height, last_bits, last_time, first_time):
    """GetNextWorkRequired at mainnet parameters (fPowAllowMinDifficultyBlocks false); the caller
    supplies the time of the ancestor at nHeight - (DifficultyAdjustmentInterval() - 1)."""
    if (last_height + 1) % INTERVAL != 0:
        return last_bits
    return calculate_next_work_required(last_bits, last_time, first_time)


def permitted_difficulty_transition(height, old_nbits, new_nbits):
    """PermittedDifficultyTransition at mainnet parameters."""
    if F_POW_ALLOW_MIN_DIFFICULTY:
        return True
    if height % INTERVAL == 0:
        smallest_timespan = TARGET_TIMESPAN // 4
        largest_timespan = TARGET_TIMESPAN * 4
        observed, _, _ = set_compact(new_nbits)
        largest, _, _ = set_compact(old_nbits)
        largest = mul256_u32(largest, largest_timespan) // TARGET_TIMESPAN
        if largest > POW_LIMIT:
            largest = POW_LIMIT
        maximum, _, _ = set_compact(get_compact(largest))
        if maximum < observed:
            return False
        smallest, _, _ = set_compact(old_nbits)
        smallest = mul256_u32(smallest, smallest_timespan) // TARGET_TIMESPAN
        if smallest > POW_LIMIT:
            smallest = POW_LIMIT
        minimum, _, _ = set_compact(get_compact(smallest))
        if minimum > observed:
            return False
    elif old_nbits != new_nbits:
        return False
    return True


def get_bits_proof(bits):
    """chain.cpp GetBitsProof: 0 for a negative, overflowing or zero target (no powLimit test),
    else ~target / (target + 1) + 1 in 256-bit arithmetic."""
    t, neg, ovf = set_compact(bits)
    if neg or ovf or t == 0:
        return 0
    not_t = (M256 - 1) ^ t
    t1 = (t + 1) % M256
    assert t1 != 0
    return ((not_t // t1) + 1) % M256


# ---------------------------------------------------------------------------------------------
# Vectors

def bv(x):
    return "(0x%08x : BitVec 32)" % (x & 0xffffffff)


def main(out):
    L = []
    L.append("import Definitions.Def_BitcoinPow")
    L.append("import Definitions.Def_BitcoinBlockV2")
    L.append("open BitcoinPow")
    L.append("/-! Spot 15 vectors (`REVIEW_SPOT15.md`): `arith_uint256::SetCompact` / `GetCompact`, `DeriveTarget`,")
    L.append("`CheckProofOfWorkImpl`, `CalculateNextWorkRequired`, `GetNextWorkRequired`, `PermittedDifficultyTransition`")
    L.append("and `GetBitsProof` at mainnet parameters. Expectations computed by `tests/reference/pow_reference.py`,")
    L.append("an independent Python model with 256-bit wraparound. Every line prints `true`. -/")

    L.append("-- constants")
    L.append("#eval powLimit == 0x%x" % POW_LIMIT)
    L.append("#eval targetTimespan == %d" % TARGET_TIMESPAN)
    L.append("#eval targetSpacing == %d" % TARGET_SPACING)
    L.append("#eval difficultyAdjustmentInterval == %d" % INTERVAL)
    L.append("#eval getCompact powLimit == %s" % bv(get_compact(POW_LIMIT)))  # nProofOfWorkLimit

    L.append("-- SetCompact: value, fNegative, fOverflow")
    compacts = [0x00000000, 0x00123456, 0x01003456, 0x01123456, 0x02123456, 0x03123456, 0x04123456,
                0x02008000, 0x05009234, 0x20123456, 0x1d00ffff, 0x1e00ffff, 0x207fffff,
                0x2100ffff, 0x21010000, 0x21000001, 0x220000ff, 0x22000100, 0x22000001,
                0x23000000, 0x23000001, 0x04923456, 0x20800000, 0xff123456, 0xff000000, 0x1b0404cb, 0x1d00d86a]
    for c in compacts:
        v, neg, ovf = set_compact(c)
        L.append("#eval setCompact %s == 0x%x" % (bv(c), v))
        L.append("#eval compactNegative %s == %s" % (bv(c), "true" if neg else "false"))
        L.append("#eval compactOverflow %s == %s" % (bv(c), "true" if ovf else "false"))
    # The nSize <= 3 cases where the C++ shifts the mantissa to zero before computing fNegative:
    # Core's *pfNegative is false there (nWord == 0 after the shift) while the Lean's compactNegative
    # (unshifted word) is true; the value is 0 in both, so every consumer rejects. Recorded as the
    # consumer verdicts, not as the flag (see REVIEW_SPOT15.md).
    for c in [0x01803456, 0x02800012, 0x00800001]:
        v, neg, ovf = set_compact(c)
        assert v == 0 and not neg and not ovf
        L.append("#eval setCompact %s == 0" % bv(c))
        L.append("#eval deriveTarget %s == none" % bv(c))
        L.append("#eval BitcoinBlockV2.blockProof 0x%08x == 0" % c)

    L.append("-- GetCompact (fNegative = false), including the 0x00800000 rounding")
    gets = [0, 1, 0x80, 0x1234, 0x8000, 0x123456, 0x7fffff, 0x800000, 0xffffff, 0x12345678, 0x80000000,
            1 << 255, M256 - 1, POW_LIMIT, 0xffff << 208, (0xffff << 208) >> 2, 0x404cb << 200]
    for v in gets:
        L.append("#eval getCompact 0x%x == %s" % (v, bv(get_compact(v))))
    L.append("#eval setCompact (getCompact powLimit) == 0x%x" % set_compact(get_compact(POW_LIMIT))[0])
    L.append("#eval getCompact (setCompact (0x1d00ffff : BitVec 32)) == %s" % bv(get_compact(set_compact(0x1d00ffff)[0])))

    L.append("-- DeriveTarget / CheckProofOfWork")
    for c in [0x1d00ffff, 0x1e00ffff, 0x1d01ffff, 0x04923456, 0x00000000, 0x23000000, 0x21000001, 0x2100ffff, 0x1b0404cb]:
        t = derive_target(c)
        L.append("#eval deriveTarget %s == %s" % (bv(c), "none" if t is None else "some 0x%x" % t))
    t = set_compact(0x1d00ffff)[0]
    for (h, c) in [(t, 0x1d00ffff), (t - 1, 0x1d00ffff), (t + 1, 0x1d00ffff), (0, 0x1d00ffff), (POW_LIMIT, 0x1d00ffff),
                   (0, 0x1e00ffff), (0, 0x04923456), (0, 0x00000000), (0, 0x21000001), (0, 0x2100ffff),
                   (set_compact(0x1b0404cb)[0], 0x1b0404cb), (set_compact(0x1b0404cb)[0] + 1, 0x1b0404cb),
                   (set_compact(0x1b0404cb)[0] - 1, 0x1b0404cb), (M256 - 1, 0x1d00ffff)]:
        L.append("#eval checkProofOfWork 0x%x %s == %s" % (h, bv(c), "true" if check_proof_of_work(h, c) else "false"))

    L.append("-- clampTimespan")
    for a in [-5, 0, 302399, 302400, 302401, 1209600, 4838399, 4838400, 4838401, 10 ** 12]:
        lo, hi = TARGET_TIMESPAN // 4, TARGET_TIMESPAN * 4
        r = lo if a < lo else (hi if a > hi else a)
        L.append("#eval clampTimespan (%d) == %d" % (a, r))

    L.append("-- CalculateNextWorkRequired (lastBits, lastTime, firstTime)")
    cases = [
        # real mainnet data (blockstream.info / mempool.space, fetched 2026-10-28):
        # block 0 time 1231006505, block 2015 time 1233061996 -> block 2016 bits 0x1d00ffff (cap)
        (0x1d00ffff, 1233061996, 1231006505),
        # block 30240 time 1261130161, block 32255 time 1262152739 -> block 32256 bits 0x1d00d86a
        (0x1d00ffff, 1262152739, 1261130161),
        # clamp at both ends from a mid-range target
        (0x1c05a3f4, 1279297671, 1279008237),
        (0x1c387f6f, 1269211443, 1263163443),
        (0x1b0404cb, 1000000 + 100, 1000000),            # tiny timespan -> /4
        (0x1b0404cb, 1000000, 1000000 + 100),            # negative timespan -> /4
        (0x1b0404cb, 1000000 + 302399, 1000000),         # just below lower clamp
        (0x1b0404cb, 1000000 + 302400, 1000000),         # exactly lower clamp
        (0x1b0404cb, 1000000 + 302401, 1000000),
        (0x1b0404cb, 1000000 + 1209600, 1000000),        # unchanged (up to rounding)
        (0x1b0404cb, 1000000 + 4838399, 1000000),
        (0x1b0404cb, 1000000 + 4838400, 1000000),        # exactly upper clamp
        (0x1b0404cb, 1000000 + 4838401, 1000000),
        (0x1b0404cb, 1000000 + 10 ** 9, 1000000),        # huge timespan -> *4
        # powLimit cap
        (0x1d00ffff, 1000000 + 4838400, 1000000),
        (0x1d00ffff, 1000000 + 1209601, 1000000),
        (0x1c3fffc0, 1000000 + 4838400, 1000000),        # exactly 4x -> 0xffff<<208 (not capped)
        (0x1c3fffc1, 1000000 + 4838400, 1000000),        # 4x exceeds 0xffff<<208 but not powLimit
        (0x1c7fffff, 1000000 + 4838400, 1000000),        # 4x exceeds powLimit -> cap
        # 256-bit wraparound of bnNew *= nActualTimespan (targets far above powLimit, never
        # reached from a validated chain: powLimit * 4838400 < 2^247)
        (0x21008000, 1000000 + 4838400, 1000000),        # 2^255 * even -> 0
        (0x21008000, 1000000 + 302401, 1000000),         # 2^255 * odd -> 2^255 -> cap
        (0x2100ffff, 1000000 + 4838400, 1000000),
        (0x2100ffff, 1000000 + 1209600, 1000000),
        (0x2000ffff, 1000000 + 4838400, 1000000),
        (0x20ffffff, 1000000 + 302400, 1000000),         # mantissa 0x7fffff (sign bit ignored by SetCompact)
        # degenerate last target (zero / negative bits are used as-is by the C++)
        (0x00000000, 1000000 + 1209600, 1000000),
        (0x04923456, 1000000 + 1209600, 1000000),
    ]
    for (b, lt, ft) in cases:
        L.append("#eval calculateNextWork %s %d %d == %s" % (bv(b), lt, ft, bv(calculate_next_work_required(b, lt, ft))))
    # a wrap case where the un-wrapped product would give a different answer
    unwrapped = min(((1 << 255) * 4838400) // TARGET_TIMESPAN, POW_LIMIT)
    assert get_compact(unwrapped) == 0x1d00ffff and calculate_next_work_required(0x21008000, 1000000 + 4838400, 1000000) == 0

    L.append("-- GetNextWorkRequired (lastHeight, lastBits, lastTime, firstTime)")
    for (h, b, lt, ft) in [(2015, 0x1d00ffff, 1233061996, 1231006505), (32255, 0x1d00ffff, 1262152739, 1261130161),
                           (32254, 0x1d00ffff, 1262152739, 1261130161), (32256, 0x1d00d86a, 1262152739, 1261130161),
                           (0, 0x1d00ffff, 0, 0), (2014, 0x1d00ffff, 1233061996, 1231006505),
                           (4031, 0x1b0404cb, 1000000 + 100, 1000000), (100, 0x04923456, 5, 0)]:
        L.append("#eval nextWorkRequired %d %s %d %d == %s" % (h, bv(b), lt, ft, bv(get_next_work_required(h, b, lt, ft))))

    L.append("-- PermittedDifficultyTransition (height, oldBits, newBits)")
    for (h, o, n) in [(32256, 0x1d00ffff, 0x1d00d86a), (2016, 0x1d00ffff, 0x1d00ffff), (2016, 0x1d00ffff, 0x1e00ffff),
                      (2016, 0x1d00ffff, 0x1c3fffc0), (2016, 0x1d00ffff, 0x1c3fffbf), (2016, 0x1d00ffff, 0x1c3fffc1),
                      (0, 0x1d00ffff, 0x1d00ffff), (2016, 0x1b0404cb, 0x1b010132), (2016, 0x1b0404cb, 0x1b010131),
                      (2016, 0x1b0404cb, 0x1b10132c), (2016, 0x1b0404cb, 0x1b10132d),
                      (2017, 0x1d00ffff, 0x1d00ffff), (2017, 0x1d00ffff, 0x1d00d86a), (1, 0x04923456, 0x04923456)]:
        L.append("#eval permittedTransition %d %s %s == %s" % (h, bv(o), bv(n), "true" if permitted_difficulty_transition(h, o, n) else "false"))

    L.append("-- GetBitsProof / blockProof (bits as Nat)")
    for c in [0x1d00ffff, 0x1b0404cb, 0x1d00d86a, 0x03000001, 0x00000000, 0x04923456, 0x21010000, 0xff123456, 0x01803456]:
        L.append("#eval BitcoinBlockV2.blockProof 0x%08x == 0x%x" % (c, get_bits_proof(c)))
    # Discrepancy (no verdict impact, see REVIEW_SPOT15.md): Core's GetBitsProof has no powLimit test,
    # the Lean's blockProof goes through deriveTarget and returns 0 above powLimit. Recorded here as a
    # comment because the line would print false.
    for c in [0x1e00ffff, 0x2000ffff, 0x21000001]:
        L.append("-- #eval BitcoinBlockV2.blockProof 0x%08x == 0x%x   -- Core; the Lean gives 0" % (c, get_bits_proof(c)))

    with open(out, "w") as f:
        f.write("\n".join(L) + "\n")
    print("wrote", out, sum(1 for l in L if l.startswith("#eval")), "vectors")


if __name__ == "__main__":
    main(sys.argv[1])
