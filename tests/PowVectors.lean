import Definitions.Def_BitcoinPow
import Definitions.Def_BitcoinBlockV2
open BitcoinPow
/-! Spot 15 vectors (`REVIEW_SPOT15.md`): `arith_uint256::SetCompact` / `GetCompact`, `DeriveTarget`,
`CheckProofOfWorkImpl`, `CalculateNextWorkRequired`, `GetNextWorkRequired`, `PermittedDifficultyTransition`
and `GetBitsProof` at mainnet parameters. Expectations computed by `tests/reference/pow_reference.py`,
an independent Python model with 256-bit wraparound. Every line prints `true`. -/
-- constants
#eval powLimit == 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff
#eval targetTimespan == 1209600
#eval targetSpacing == 600
#eval difficultyAdjustmentInterval == 2016
#eval getCompact powLimit == (0x1d00ffff : BitVec 32)
-- SetCompact: value, fNegative, fOverflow
#eval setCompact (0x00000000 : BitVec 32) == 0x0
#eval compactNegative (0x00000000 : BitVec 32) == false
#eval compactOverflow (0x00000000 : BitVec 32) == false
#eval setCompact (0x00123456 : BitVec 32) == 0x0
#eval compactNegative (0x00123456 : BitVec 32) == false
#eval compactOverflow (0x00123456 : BitVec 32) == false
#eval setCompact (0x01003456 : BitVec 32) == 0x0
#eval compactNegative (0x01003456 : BitVec 32) == false
#eval compactOverflow (0x01003456 : BitVec 32) == false
#eval setCompact (0x01123456 : BitVec 32) == 0x12
#eval compactNegative (0x01123456 : BitVec 32) == false
#eval compactOverflow (0x01123456 : BitVec 32) == false
#eval setCompact (0x02123456 : BitVec 32) == 0x1234
#eval compactNegative (0x02123456 : BitVec 32) == false
#eval compactOverflow (0x02123456 : BitVec 32) == false
#eval setCompact (0x03123456 : BitVec 32) == 0x123456
#eval compactNegative (0x03123456 : BitVec 32) == false
#eval compactOverflow (0x03123456 : BitVec 32) == false
#eval setCompact (0x04123456 : BitVec 32) == 0x12345600
#eval compactNegative (0x04123456 : BitVec 32) == false
#eval compactOverflow (0x04123456 : BitVec 32) == false
#eval setCompact (0x02008000 : BitVec 32) == 0x80
#eval compactNegative (0x02008000 : BitVec 32) == false
#eval compactOverflow (0x02008000 : BitVec 32) == false
#eval setCompact (0x05009234 : BitVec 32) == 0x92340000
#eval compactNegative (0x05009234 : BitVec 32) == false
#eval compactOverflow (0x05009234 : BitVec 32) == false
#eval setCompact (0x20123456 : BitVec 32) == 0x1234560000000000000000000000000000000000000000000000000000000000
#eval compactNegative (0x20123456 : BitVec 32) == false
#eval compactOverflow (0x20123456 : BitVec 32) == false
#eval setCompact (0x1d00ffff : BitVec 32) == 0xffff0000000000000000000000000000000000000000000000000000
#eval compactNegative (0x1d00ffff : BitVec 32) == false
#eval compactOverflow (0x1d00ffff : BitVec 32) == false
#eval setCompact (0x1e00ffff : BitVec 32) == 0xffff000000000000000000000000000000000000000000000000000000
#eval compactNegative (0x1e00ffff : BitVec 32) == false
#eval compactOverflow (0x1e00ffff : BitVec 32) == false
#eval setCompact (0x207fffff : BitVec 32) == 0x7fffff0000000000000000000000000000000000000000000000000000000000
#eval compactNegative (0x207fffff : BitVec 32) == false
#eval compactOverflow (0x207fffff : BitVec 32) == false
#eval setCompact (0x2100ffff : BitVec 32) == 0xffff000000000000000000000000000000000000000000000000000000000000
#eval compactNegative (0x2100ffff : BitVec 32) == false
#eval compactOverflow (0x2100ffff : BitVec 32) == false
#eval setCompact (0x21010000 : BitVec 32) == 0x0
#eval compactNegative (0x21010000 : BitVec 32) == false
#eval compactOverflow (0x21010000 : BitVec 32) == true
#eval setCompact (0x21000001 : BitVec 32) == 0x1000000000000000000000000000000000000000000000000000000000000
#eval compactNegative (0x21000001 : BitVec 32) == false
#eval compactOverflow (0x21000001 : BitVec 32) == false
#eval setCompact (0x220000ff : BitVec 32) == 0xff00000000000000000000000000000000000000000000000000000000000000
#eval compactNegative (0x220000ff : BitVec 32) == false
#eval compactOverflow (0x220000ff : BitVec 32) == false
#eval setCompact (0x22000100 : BitVec 32) == 0x0
#eval compactNegative (0x22000100 : BitVec 32) == false
#eval compactOverflow (0x22000100 : BitVec 32) == true
#eval setCompact (0x22000001 : BitVec 32) == 0x100000000000000000000000000000000000000000000000000000000000000
#eval compactNegative (0x22000001 : BitVec 32) == false
#eval compactOverflow (0x22000001 : BitVec 32) == false
#eval setCompact (0x23000000 : BitVec 32) == 0x0
#eval compactNegative (0x23000000 : BitVec 32) == false
#eval compactOverflow (0x23000000 : BitVec 32) == false
#eval setCompact (0x23000001 : BitVec 32) == 0x0
#eval compactNegative (0x23000001 : BitVec 32) == false
#eval compactOverflow (0x23000001 : BitVec 32) == true
#eval setCompact (0x04923456 : BitVec 32) == 0x12345600
#eval compactNegative (0x04923456 : BitVec 32) == true
#eval compactOverflow (0x04923456 : BitVec 32) == false
#eval setCompact (0x20800000 : BitVec 32) == 0x0
#eval compactNegative (0x20800000 : BitVec 32) == false
#eval compactOverflow (0x20800000 : BitVec 32) == false
#eval setCompact (0xff123456 : BitVec 32) == 0x0
#eval compactNegative (0xff123456 : BitVec 32) == false
#eval compactOverflow (0xff123456 : BitVec 32) == true
#eval setCompact (0xff000000 : BitVec 32) == 0x0
#eval compactNegative (0xff000000 : BitVec 32) == false
#eval compactOverflow (0xff000000 : BitVec 32) == false
#eval setCompact (0x1b0404cb : BitVec 32) == 0x404cb000000000000000000000000000000000000000000000000
#eval compactNegative (0x1b0404cb : BitVec 32) == false
#eval compactOverflow (0x1b0404cb : BitVec 32) == false
#eval setCompact (0x1d00d86a : BitVec 32) == 0xd86a0000000000000000000000000000000000000000000000000000
#eval compactNegative (0x1d00d86a : BitVec 32) == false
#eval compactOverflow (0x1d00d86a : BitVec 32) == false
#eval setCompact (0x01803456 : BitVec 32) == 0
#eval deriveTarget (0x01803456 : BitVec 32) == none
#eval BitcoinBlockV2.blockProof 0x01803456 == 0
#eval setCompact (0x02800012 : BitVec 32) == 0
#eval deriveTarget (0x02800012 : BitVec 32) == none
#eval BitcoinBlockV2.blockProof 0x02800012 == 0
#eval setCompact (0x00800001 : BitVec 32) == 0
#eval deriveTarget (0x00800001 : BitVec 32) == none
#eval BitcoinBlockV2.blockProof 0x00800001 == 0
-- GetCompact (fNegative = false), including the 0x00800000 rounding
#eval getCompact 0x0 == (0x00000000 : BitVec 32)
#eval getCompact 0x1 == (0x01010000 : BitVec 32)
#eval getCompact 0x80 == (0x02008000 : BitVec 32)
#eval getCompact 0x1234 == (0x02123400 : BitVec 32)
#eval getCompact 0x8000 == (0x03008000 : BitVec 32)
#eval getCompact 0x123456 == (0x03123456 : BitVec 32)
#eval getCompact 0x7fffff == (0x037fffff : BitVec 32)
#eval getCompact 0x800000 == (0x04008000 : BitVec 32)
#eval getCompact 0xffffff == (0x0400ffff : BitVec 32)
#eval getCompact 0x12345678 == (0x04123456 : BitVec 32)
#eval getCompact 0x80000000 == (0x05008000 : BitVec 32)
#eval getCompact 0x8000000000000000000000000000000000000000000000000000000000000000 == (0x21008000 : BitVec 32)
#eval getCompact 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff == (0x2100ffff : BitVec 32)
#eval getCompact 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff == (0x1d00ffff : BitVec 32)
#eval getCompact 0xffff0000000000000000000000000000000000000000000000000000 == (0x1d00ffff : BitVec 32)
#eval getCompact 0x3fffc000000000000000000000000000000000000000000000000000 == (0x1c3fffc0 : BitVec 32)
#eval getCompact 0x404cb00000000000000000000000000000000000000000000000000 == (0x1c0404cb : BitVec 32)
#eval setCompact (getCompact powLimit) == 0xffff0000000000000000000000000000000000000000000000000000
#eval getCompact (setCompact (0x1d00ffff : BitVec 32)) == (0x1d00ffff : BitVec 32)
-- DeriveTarget / CheckProofOfWork
#eval deriveTarget (0x1d00ffff : BitVec 32) == some 0xffff0000000000000000000000000000000000000000000000000000
#eval deriveTarget (0x1e00ffff : BitVec 32) == none
#eval deriveTarget (0x1d01ffff : BitVec 32) == none
#eval deriveTarget (0x04923456 : BitVec 32) == none
#eval deriveTarget (0x00000000 : BitVec 32) == none
#eval deriveTarget (0x23000000 : BitVec 32) == none
#eval deriveTarget (0x21000001 : BitVec 32) == none
#eval deriveTarget (0x2100ffff : BitVec 32) == none
#eval deriveTarget (0x1b0404cb : BitVec 32) == some 0x404cb000000000000000000000000000000000000000000000000
#eval checkProofOfWork 0xffff0000000000000000000000000000000000000000000000000000 (0x1d00ffff : BitVec 32) == true
#eval checkProofOfWork 0xfffeffffffffffffffffffffffffffffffffffffffffffffffffffff (0x1d00ffff : BitVec 32) == true
#eval checkProofOfWork 0xffff0000000000000000000000000000000000000000000000000001 (0x1d00ffff : BitVec 32) == false
#eval checkProofOfWork 0x0 (0x1d00ffff : BitVec 32) == true
#eval checkProofOfWork 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff (0x1d00ffff : BitVec 32) == false
#eval checkProofOfWork 0x0 (0x1e00ffff : BitVec 32) == false
#eval checkProofOfWork 0x0 (0x04923456 : BitVec 32) == false
#eval checkProofOfWork 0x0 (0x00000000 : BitVec 32) == false
#eval checkProofOfWork 0x0 (0x21000001 : BitVec 32) == false
#eval checkProofOfWork 0x0 (0x2100ffff : BitVec 32) == false
#eval checkProofOfWork 0x404cb000000000000000000000000000000000000000000000000 (0x1b0404cb : BitVec 32) == true
#eval checkProofOfWork 0x404cb000000000000000000000000000000000000000000000001 (0x1b0404cb : BitVec 32) == false
#eval checkProofOfWork 0x404caffffffffffffffffffffffffffffffffffffffffffffffff (0x1b0404cb : BitVec 32) == true
#eval checkProofOfWork 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff (0x1d00ffff : BitVec 32) == false
-- clampTimespan
#eval clampTimespan (-5) == 302400
#eval clampTimespan (0) == 302400
#eval clampTimespan (302399) == 302400
#eval clampTimespan (302400) == 302400
#eval clampTimespan (302401) == 302401
#eval clampTimespan (1209600) == 1209600
#eval clampTimespan (4838399) == 4838399
#eval clampTimespan (4838400) == 4838400
#eval clampTimespan (4838401) == 4838400
#eval clampTimespan (1000000000000) == 4838400
-- CalculateNextWorkRequired (lastBits, lastTime, firstTime)
#eval calculateNextWork (0x1d00ffff : BitVec 32) 1233061996 1231006505 == (0x1d00ffff : BitVec 32)
#eval calculateNextWork (0x1d00ffff : BitVec 32) 1262152739 1261130161 == (0x1d00d86a : BitVec 32)
#eval calculateNextWork (0x1c05a3f4 : BitVec 32) 1279297671 1279008237 == (0x1c0168fd : BitVec 32)
#eval calculateNextWork (0x1c387f6f : BitVec 32) 1269211443 1263163443 == (0x1d00e1fd : BitVec 32)
#eval calculateNextWork (0x1b0404cb : BitVec 32) 1000100 1000000 == (0x1b010132 : BitVec 32)
#eval calculateNextWork (0x1b0404cb : BitVec 32) 1000000 1000100 == (0x1b010132 : BitVec 32)
#eval calculateNextWork (0x1b0404cb : BitVec 32) 1302399 1000000 == (0x1b010132 : BitVec 32)
#eval calculateNextWork (0x1b0404cb : BitVec 32) 1302400 1000000 == (0x1b010132 : BitVec 32)
#eval calculateNextWork (0x1b0404cb : BitVec 32) 1302401 1000000 == (0x1b010132 : BitVec 32)
#eval calculateNextWork (0x1b0404cb : BitVec 32) 2209600 1000000 == (0x1b0404cb : BitVec 32)
#eval calculateNextWork (0x1b0404cb : BitVec 32) 5838399 1000000 == (0x1b10132b : BitVec 32)
#eval calculateNextWork (0x1b0404cb : BitVec 32) 5838400 1000000 == (0x1b10132c : BitVec 32)
#eval calculateNextWork (0x1b0404cb : BitVec 32) 5838401 1000000 == (0x1b10132c : BitVec 32)
#eval calculateNextWork (0x1b0404cb : BitVec 32) 1001000000 1000000 == (0x1b10132c : BitVec 32)
#eval calculateNextWork (0x1d00ffff : BitVec 32) 5838400 1000000 == (0x1d00ffff : BitVec 32)
#eval calculateNextWork (0x1d00ffff : BitVec 32) 2209601 1000000 == (0x1d00ffff : BitVec 32)
#eval calculateNextWork (0x1c3fffc0 : BitVec 32) 5838400 1000000 == (0x1d00ffff : BitVec 32)
#eval calculateNextWork (0x1c3fffc1 : BitVec 32) 5838400 1000000 == (0x1d00ffff : BitVec 32)
#eval calculateNextWork (0x1c7fffff : BitVec 32) 5838400 1000000 == (0x1d00ffff : BitVec 32)
#eval calculateNextWork (0x21008000 : BitVec 32) 5838400 1000000 == (0x00000000 : BitVec 32)
#eval calculateNextWork (0x21008000 : BitVec 32) 1302401 1000000 == (0x1d00ffff : BitVec 32)
#eval calculateNextWork (0x2100ffff : BitVec 32) 5838400 1000000 == (0x1d00ffff : BitVec 32)
#eval calculateNextWork (0x2100ffff : BitVec 32) 2209600 1000000 == (0x1d00ffff : BitVec 32)
#eval calculateNextWork (0x2000ffff : BitVec 32) 5838400 1000000 == (0x1d00ffff : BitVec 32)
#eval calculateNextWork (0x20ffffff : BitVec 32) 1302400 1000000 == (0x1d00ffff : BitVec 32)
#eval calculateNextWork (0x00000000 : BitVec 32) 2209600 1000000 == (0x00000000 : BitVec 32)
#eval calculateNextWork (0x04923456 : BitVec 32) 2209600 1000000 == (0x04123456 : BitVec 32)
-- GetNextWorkRequired (lastHeight, lastBits, lastTime, firstTime)
#eval nextWorkRequired 2015 (0x1d00ffff : BitVec 32) 1233061996 1231006505 == (0x1d00ffff : BitVec 32)
#eval nextWorkRequired 32255 (0x1d00ffff : BitVec 32) 1262152739 1261130161 == (0x1d00d86a : BitVec 32)
#eval nextWorkRequired 32254 (0x1d00ffff : BitVec 32) 1262152739 1261130161 == (0x1d00ffff : BitVec 32)
#eval nextWorkRequired 32256 (0x1d00d86a : BitVec 32) 1262152739 1261130161 == (0x1d00d86a : BitVec 32)
#eval nextWorkRequired 0 (0x1d00ffff : BitVec 32) 0 0 == (0x1d00ffff : BitVec 32)
#eval nextWorkRequired 2014 (0x1d00ffff : BitVec 32) 1233061996 1231006505 == (0x1d00ffff : BitVec 32)
#eval nextWorkRequired 4031 (0x1b0404cb : BitVec 32) 1000100 1000000 == (0x1b010132 : BitVec 32)
#eval nextWorkRequired 100 (0x04923456 : BitVec 32) 5 0 == (0x04923456 : BitVec 32)
-- PermittedDifficultyTransition (height, oldBits, newBits)
#eval permittedTransition 32256 (0x1d00ffff : BitVec 32) (0x1d00d86a : BitVec 32) == true
#eval permittedTransition 2016 (0x1d00ffff : BitVec 32) (0x1d00ffff : BitVec 32) == true
#eval permittedTransition 2016 (0x1d00ffff : BitVec 32) (0x1e00ffff : BitVec 32) == false
#eval permittedTransition 2016 (0x1d00ffff : BitVec 32) (0x1c3fffc0 : BitVec 32) == true
#eval permittedTransition 2016 (0x1d00ffff : BitVec 32) (0x1c3fffbf : BitVec 32) == false
#eval permittedTransition 2016 (0x1d00ffff : BitVec 32) (0x1c3fffc1 : BitVec 32) == true
#eval permittedTransition 0 (0x1d00ffff : BitVec 32) (0x1d00ffff : BitVec 32) == true
#eval permittedTransition 2016 (0x1b0404cb : BitVec 32) (0x1b010132 : BitVec 32) == true
#eval permittedTransition 2016 (0x1b0404cb : BitVec 32) (0x1b010131 : BitVec 32) == false
#eval permittedTransition 2016 (0x1b0404cb : BitVec 32) (0x1b10132c : BitVec 32) == true
#eval permittedTransition 2016 (0x1b0404cb : BitVec 32) (0x1b10132d : BitVec 32) == false
#eval permittedTransition 2017 (0x1d00ffff : BitVec 32) (0x1d00ffff : BitVec 32) == true
#eval permittedTransition 2017 (0x1d00ffff : BitVec 32) (0x1d00d86a : BitVec 32) == false
#eval permittedTransition 1 (0x04923456 : BitVec 32) (0x04923456 : BitVec 32) == true
-- GetBitsProof / blockProof (bits as Nat)
#eval BitcoinBlockV2.blockProof 0x1d00ffff == 0x100010001
#eval BitcoinBlockV2.blockProof 0x1b0404cb == 0x3fb3ab764c00
#eval BitcoinBlockV2.blockProof 0x1d00d86a == 0x12ed3afd2
#eval BitcoinBlockV2.blockProof 0x03000001 == 0x8000000000000000000000000000000000000000000000000000000000000000
#eval BitcoinBlockV2.blockProof 0x00000000 == 0x0
#eval BitcoinBlockV2.blockProof 0x04923456 == 0x0
#eval BitcoinBlockV2.blockProof 0x21010000 == 0x0
#eval BitcoinBlockV2.blockProof 0xff123456 == 0x0
#eval BitcoinBlockV2.blockProof 0x01803456 == 0x0
-- #eval BitcoinBlockV2.blockProof 0x1e00ffff == 0x1000100   -- Core; the Lean gives 0
-- #eval BitcoinBlockV2.blockProof 0x2000ffff == 0x100   -- Core; the Lean gives 0
-- #eval BitcoinBlockV2.blockProof 0x21000001 == 0xffff   -- Core; the Lean gives 0
