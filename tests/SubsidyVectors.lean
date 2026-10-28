import Definitions.Def_BitcoinSubsidy
open BitcoinSubsidy
/-! Spot 23 vectors (`REVIEW_SPOT23.md`): `GetBlockSubsidy` (`validation.cpp`) at mainnet parameters:
boundary heights around every interesting halving, the 64-halving early return, and the total
issuance. Expectations computed by `tests/reference/subsidy_reference.py`. Every line prints `true`. -/
#eval COIN == 100000000
#eval MAX_MONEY == 2100000000000000
#eval halvingInterval == 210000
#eval zeroHeight == 6930000
-- coreSubsidy and specSubsidy at the boundary heights
#eval coreSubsidy 0 == 5000000000
#eval specSubsidy 0 == 5000000000
#eval coreSubsidy 1 == 5000000000
#eval specSubsidy 1 == 5000000000
#eval coreSubsidy 209999 == 5000000000
#eval specSubsidy 209999 == 5000000000
#eval coreSubsidy 210000 == 2500000000
#eval specSubsidy 210000 == 2500000000
#eval coreSubsidy 210001 == 2500000000
#eval specSubsidy 210001 == 2500000000
#eval coreSubsidy 419999 == 2500000000
#eval specSubsidy 419999 == 2500000000
#eval coreSubsidy 420000 == 1250000000
#eval specSubsidy 420000 == 1250000000
#eval coreSubsidy 629999 == 1250000000
#eval specSubsidy 629999 == 1250000000
#eval coreSubsidy 630000 == 625000000
#eval specSubsidy 630000 == 625000000
#eval coreSubsidy 839999 == 625000000
#eval specSubsidy 839999 == 625000000
#eval coreSubsidy 840000 == 312500000
#eval specSubsidy 840000 == 312500000
#eval coreSubsidy 1050000 == 156250000
#eval specSubsidy 1050000 == 156250000
#eval coreSubsidy 6719999 == 2
#eval specSubsidy 6719999 == 2
#eval coreSubsidy 6720000 == 1
#eval specSubsidy 6720000 == 1
#eval coreSubsidy 6929999 == 1
#eval specSubsidy 6929999 == 1
#eval coreSubsidy 6930000 == 0
#eval specSubsidy 6930000 == 0
#eval coreSubsidy 6930001 == 0
#eval specSubsidy 6930001 == 0
#eval coreSubsidy 7139999 == 0
#eval specSubsidy 7139999 == 0
#eval coreSubsidy 7140000 == 0
#eval specSubsidy 7140000 == 0
#eval coreSubsidy 13439999 == 0
#eval specSubsidy 13439999 == 0
#eval coreSubsidy 13440000 == 0
#eval specSubsidy 13440000 == 0
#eval coreSubsidy 13440001 == 0
#eval specSubsidy 13440001 == 0
#eval coreSubsidy 2147483647 == 0
#eval specSubsidy 2147483647 == 0
-- the subsidy at the first height of every halving interval 0..33
#eval coreSubsidy (0 * halvingInterval) == 5000000000
#eval coreSubsidy (1 * halvingInterval) == 2500000000
#eval coreSubsidy (2 * halvingInterval) == 1250000000
#eval coreSubsidy (3 * halvingInterval) == 625000000
#eval coreSubsidy (4 * halvingInterval) == 312500000
#eval coreSubsidy (5 * halvingInterval) == 156250000
#eval coreSubsidy (6 * halvingInterval) == 78125000
#eval coreSubsidy (7 * halvingInterval) == 39062500
#eval coreSubsidy (8 * halvingInterval) == 19531250
#eval coreSubsidy (9 * halvingInterval) == 9765625
#eval coreSubsidy (10 * halvingInterval) == 4882812
#eval coreSubsidy (11 * halvingInterval) == 2441406
#eval coreSubsidy (12 * halvingInterval) == 1220703
#eval coreSubsidy (13 * halvingInterval) == 610351
#eval coreSubsidy (14 * halvingInterval) == 305175
#eval coreSubsidy (15 * halvingInterval) == 152587
#eval coreSubsidy (16 * halvingInterval) == 76293
#eval coreSubsidy (17 * halvingInterval) == 38146
#eval coreSubsidy (18 * halvingInterval) == 19073
#eval coreSubsidy (19 * halvingInterval) == 9536
#eval coreSubsidy (20 * halvingInterval) == 4768
#eval coreSubsidy (21 * halvingInterval) == 2384
#eval coreSubsidy (22 * halvingInterval) == 1192
#eval coreSubsidy (23 * halvingInterval) == 596
#eval coreSubsidy (24 * halvingInterval) == 298
#eval coreSubsidy (25 * halvingInterval) == 149
#eval coreSubsidy (26 * halvingInterval) == 74
#eval coreSubsidy (27 * halvingInterval) == 37
#eval coreSubsidy (28 * halvingInterval) == 18
#eval coreSubsidy (29 * halvingInterval) == 9
#eval coreSubsidy (30 * halvingInterval) == 4
#eval coreSubsidy (31 * halvingInterval) == 2
#eval coreSubsidy (32 * halvingInterval) == 1
#eval coreSubsidy (33 * halvingInterval) == 0
-- halving 32 is the last non-zero one (one satoshi), halving 33 is already zero by truncation
#eval (List.range 64).map (fun k => coreSubsidy (k * halvingInterval) != 0) == [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]
-- total issuance: sum over all 33 non-zero intervals, each of 210000 blocks
#eval intervalSum 33 * halvingInterval == 2099999997690000
#eval intervalSum 64 * halvingInterval == 2099999997690000
#eval 2099999997690000 < MAX_MONEY
#eval MAX_MONEY - 2099999997690000 == 2310000
-- issuedBelow on small prefixes (brute-force sums from the reference)
#eval issuedBelow 0 == 0
#eval issuedBelow 1 == 5000000000
#eval issuedBelow 2 == 10000000000
#eval issuedBelow 1000 == 5000000000000
