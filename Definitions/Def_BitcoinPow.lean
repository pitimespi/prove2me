import Std

namespace BitcoinPow

/-! Transcription of the mainnet proof-of-work arithmetic of Bitcoin Core at revision
`a773e1e33b349dc819b5a0edc1c7a4839dc73b48`: `arith_uint256::SetCompact` / `GetCompact`
(`arith_uint256.cpp`), and `DeriveTarget`, `CheckProofOfWorkImpl`, `CalculateNextWorkRequired`,
`PermittedDifficultyTransition`, `GetNextWorkRequired` (`pow.cpp`), with `CMainParams`
(`kernel/chainparams.cpp`): `fPowAllowMinDifficultyBlocks = false`, `fPowNoRetargeting = false`,
`enforce_BIP94 = false`.

An `arith_uint256` is modelled by its value, a natural number below `2 ^ 256`. Its left shift and
its multiplications discard carries out of the top word, i.e. they reduce modulo `2 ^ 256`; its
division is exact integer division. -/

/-- `2 ^ 256`, the modulus of `arith_uint256` arithmetic. -/
def width : Nat := 2 ^ 256

/-- `consensus.powLimit = uint256{"00000000ffff…ff"}`: `2 ^ 224 - 1`. -/
def powLimit : Nat := 2 ^ 224 - 1

/-- `consensus.nPowTargetTimespan = 14 * 24 * 60 * 60`. -/
def targetTimespan : Nat := 14 * 24 * 60 * 60

/-- `consensus.nPowTargetSpacing = 10 * 60`. -/
def targetSpacing : Nat := 10 * 60

/-- `Consensus::Params::DifficultyAdjustmentInterval() = nPowTargetTimespan / nPowTargetSpacing`. -/
def difficultyAdjustmentInterval : Nat := targetTimespan / targetSpacing

/-- `int nSize = nCompact >> 24`. -/
def compactSize (c : BitVec 32) : Nat := (c >>> 24).toNat

/-- `uint32_t nWord = nCompact & 0x007fffff`. -/
def compactWord (c : BitVec 32) : Nat := (c &&& 0x007fffff).toNat

/-- The value produced by `SetCompact`: the mantissa shifted right by `8 * (3 - nSize)` bytes when
`nSize <= 3`, otherwise shifted left by `8 * (nSize - 3)` bytes inside 256 bits. -/
def setCompact (c : BitVec 32) : Nat :=
  let nSize := compactSize c
  let nWord := compactWord c
  if nSize ≤ 3 then nWord >>> (8 * (3 - nSize)) else (nWord <<< (8 * (nSize - 3))) % width

/-- `*pfNegative = nWord != 0 && (nCompact & 0x00800000) != 0`. -/
def compactNegative (c : BitVec 32) : Bool :=
  compactWord c != 0 && (c &&& 0x00800000) != 0

/-- `*pfOverflow = nWord != 0 && ((nSize > 34) || (nWord > 0xff && nSize > 33) || (nWord > 0xffff && nSize > 32))`. -/
def compactOverflow (c : BitVec 32) : Bool :=
  let nSize := compactSize c
  let nWord := compactWord c
  nWord != 0 && (decide (34 < nSize) || (decide (0xff < nWord) && decide (33 < nSize)) ||
    (decide (0xffff < nWord) && decide (32 < nSize)))

/-- The exact mathematical value `mantissa * 256 ^ (nSize - 3)` encoded by a compact word, with no
256-bit truncation (and floor division for `nSize <= 3`). -/
def specTarget (c : BitVec 32) : Nat :=
  let nSize := compactSize c
  let nWord := compactWord c
  if nSize ≤ 3 then nWord / 256 ^ (3 - nSize) else nWord * 256 ^ (nSize - 3)

/-- `base_uint::bits()`: the bit length, `0` for `0`. -/
def bitLength (v : Nat) : Nat := if v = 0 then 0 else Nat.log2 v + 1

/-- `GetCompact(fNegative = false)` on a value below `2 ^ 256`. `GetLow64()` is the value modulo
`2 ^ 64`; the assignment to the `uint32_t nCompact` reduces modulo `2 ^ 32`; when bit `0x00800000`
of the mantissa is set, the mantissa is divided by 256 and the exponent incremented. -/
def getCompact (v : Nat) : BitVec 32 :=
  let nSize := (bitLength v + 7) / 8
  let nCompact :=
    if nSize ≤ 3 then ((v % 2 ^ 64) <<< (8 * (3 - nSize))) % 2 ^ 32
    else ((v >>> (8 * (nSize - 3))) % 2 ^ 64) % 2 ^ 32
  let adjust := nCompact &&& 0x00800000 != 0
  let nCompact' := if adjust then nCompact >>> 8 else nCompact
  let nSize' := if adjust then nSize + 1 else nSize
  BitVec.ofNat 32 (nCompact' ||| (nSize' <<< 24))

/-- `DeriveTarget`: the target, unless negative, zero, overflowing, or above `powLimit`. -/
def deriveTarget (nBits : BitVec 32) : Option Nat :=
  let t := setCompact nBits
  if compactNegative nBits || decide (t = 0) || compactOverflow nBits || decide (powLimit < t) then none
  else some t

/-- `CheckProofOfWorkImpl`: the header hash, read as a 256-bit number, is at most the derived target. -/
def checkProofOfWork (hash : Nat) (nBits : BitVec 32) : Bool :=
  match deriveTarget nBits with
  | none => false
  | some t => decide (hash ≤ t)

/-- The timespan clamp of `CalculateNextWorkRequired`: `nActualTimespan` (a signed difference of
block times) is raised to `nPowTargetTimespan / 4` and lowered to `nPowTargetTimespan * 4`. -/
def clampTimespan (actual : Int) : Int :=
  let lo : Int := (targetTimespan / 4 : Nat)
  let hi : Int := (targetTimespan * 4 : Nat)
  if actual < lo then lo else if hi < actual then hi else actual

/-- `CalculateNextWorkRequired(pindexLast, nFirstBlockTime)` at mainnet parameters: decode the last
target, multiply by the clamped timespan (modulo `2 ^ 256`), divide by the target timespan, cap at
`powLimit`, and re-encode. -/
def calculateNextWork (lastBits : BitVec 32) (lastTime firstTime : Int) : BitVec 32 :=
  let ts := (clampTimespan (lastTime - firstTime)).toNat
  let bn := (setCompact lastBits * ts) % width
  let bn := bn / targetTimespan
  let bn := if powLimit < bn then powLimit else bn
  getCompact bn

/-- `PermittedDifficultyTransition(params, height, old_nbits, new_nbits)` at mainnet parameters. -/
def permittedTransition (height : Nat) (oldBits newBits : BitVec 32) : Bool :=
  if height % difficultyAdjustmentInterval = 0 then
    let observed := setCompact newBits
    let largest := (setCompact oldBits * (targetTimespan * 4)) % width / targetTimespan
    let largest := if powLimit < largest then powLimit else largest
    let maximum := setCompact (getCompact largest)
    let smallest := (setCompact oldBits * (targetTimespan / 4)) % width / targetTimespan
    let smallest := if powLimit < smallest then powLimit else smallest
    let minimum := setCompact (getCompact smallest)
    !(decide (maximum < observed)) && !(decide (minimum > observed))
  else
    decide (oldBits = newBits)

/-- `GetNextWorkRequired` at mainnet parameters, with the first block time of the period supplied
by the caller. -/
def nextWorkRequired (lastHeight : Nat) (lastBits : BitVec 32) (lastTime firstTime : Int) : BitVec 32 :=
  if (lastHeight + 1) % difficultyAdjustmentInterval ≠ 0 then lastBits
  else calculateNextWork lastBits lastTime firstTime

end BitcoinPow
