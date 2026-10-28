"""Independent reference for spot 23 (REVIEW_SPOT23.md): GetBlockSubsidy (validation.cpp:1833, Bitcoin
Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48) at mainnet parameters, written from the C++ only.
Emits tests/SubsidyVectors.lean.

CAmount GetBlockSubsidy(int nHeight, const Consensus::Params& consensusParams)
{
    int halvings = nHeight / consensusParams.nSubsidyHalvingInterval;   // 210000 on mainnet
    if (halvings >= 64) return 0;                                         // shift would be UB
    CAmount nSubsidy = 50 * COIN;                                         // COIN = 100'000'000, int64
    nSubsidy >>= halvings;                                                // arithmetic shift of a positive int64
    return nSubsidy;
}

Usage: python3 -I subsidy_reference.py OUT_LEAN
"""
import sys

COIN = 100_000_000
MAX_MONEY = 21_000_000 * COIN
HALVING_INTERVAL = 210_000


def c_int_div(a, b):
    """C++ integer division truncates toward zero (only non-negative heights are used here)."""
    q = abs(a) // abs(b)
    return q if (a >= 0) == (b >= 0) else -q


def get_block_subsidy(height):
    assert -2**31 <= height < 2**31, "int nHeight"
    halvings = c_int_div(height, HALVING_INTERVAL)
    if halvings >= 64:
        return 0
    subsidy = 50 * COIN
    assert 0 <= subsidy < 2**63
    # right shift of a positive int64 by 0..63 bits: floor division by 2**halvings
    subsidy >>= halvings
    return subsidy


HEIGHTS = [0, 1, 209999, 210000, 210001, 419999, 420000, 629999, 630000, 839999, 840000, 1050000,
           6719999, 6720000, 6929999, 6930000, 6930001, 7139999, 7140000, 13439999, 13440000, 13440001,
           2**31 - 1]


def total_issuance():
    """Sum of GetBlockSubsidy over every height with a non-zero subsidy (halvings 0..32), computed
    per interval: each interval has exactly HALVING_INTERVAL heights."""
    total = 0
    k = 0
    while True:
        s = get_block_subsidy(k * HALVING_INTERVAL)
        if s == 0:
            break
        total += HALVING_INTERVAL * s
        k += 1
    return total, k


def main(out):
    total, intervals = total_issuance()
    # cross-check by brute force over the first two intervals and across the 32->33 boundary
    brute = sum(get_block_subsidy(h) for h in range(0, 2 * HALVING_INTERVAL))
    assert brute == HALVING_INTERVAL * (50 * COIN + 25 * COIN)
    lines = []
    lines.append("import Definitions.Def_BitcoinSubsidy")
    lines.append("open BitcoinSubsidy")
    lines.append("/-! Spot 23 vectors (`REVIEW_SPOT23.md`): `GetBlockSubsidy` (`validation.cpp`) at mainnet parameters:")
    lines.append("boundary heights around every interesting halving, the 64-halving early return, and the total")
    lines.append("issuance. Expectations computed by `tests/reference/subsidy_reference.py`. Every line prints `true`. -/")
    lines.append(f"#eval COIN == {COIN}")
    lines.append(f"#eval MAX_MONEY == {MAX_MONEY}")
    lines.append(f"#eval halvingInterval == {HALVING_INTERVAL}")
    lines.append(f"#eval zeroHeight == {33 * HALVING_INTERVAL}")
    lines.append("-- coreSubsidy and specSubsidy at the boundary heights")
    for h in HEIGHTS:
        s = get_block_subsidy(h)
        lines.append(f"#eval coreSubsidy {h} == {s}")
        lines.append(f"#eval specSubsidy {h} == {s}")
    lines.append("-- the subsidy at the first height of every halving interval 0..33")
    for k in range(0, 34):
        s = get_block_subsidy(k * HALVING_INTERVAL)
        lines.append(f"#eval coreSubsidy ({k} * halvingInterval) == {s}")
    lines.append("-- halving 32 is the last non-zero one (one satoshi), halving 33 is already zero by truncation")
    lines.append(f"#eval (List.range 64).map (fun k => coreSubsidy (k * halvingInterval) != 0) == {str([get_block_subsidy(k * HALVING_INTERVAL) != 0 for k in range(64)]).lower()}")
    lines.append("-- total issuance: sum over all 33 non-zero intervals, each of 210000 blocks")
    lines.append(f"#eval intervalSum {intervals} * halvingInterval == {total}")
    lines.append(f"#eval intervalSum 64 * halvingInterval == {total}")
    lines.append(f"#eval {total} < MAX_MONEY")
    lines.append(f"#eval MAX_MONEY - {total} == {MAX_MONEY - total}")
    lines.append("-- issuedBelow on small prefixes (brute-force sums from the reference)")
    for n in (0, 1, 2, 1000):
        lines.append(f"#eval issuedBelow {n} == {sum(get_block_subsidy(h) for h in range(n))}")
    with open(out, "w") as f:
        f.write("\n".join(lines) + "\n")
    for h in HEIGHTS:
        print(h, get_block_subsidy(h))
    print("non-zero intervals:", intervals, "total issuance:", total, "MAX_MONEY - total:", MAX_MONEY - total)


if __name__ == "__main__":
    main(sys.argv[1])
