import Std

namespace BitcoinSubsidy

/-- `consensus/amount.h`: `COIN{100'000'000}`, the number of satoshis in one bitcoin. -/
def COIN : Nat := 100000000

/-- `consensus/amount.h`: `MAX_MONEY{21'000'000 * COIN}`, the consensus sanity bound on amounts. -/
def MAX_MONEY : Nat := 21000000 * COIN

/-- `kernel/chainparams.cpp`, `CMainParams`: `consensus.nSubsidyHalvingInterval = 210000`. -/
def halvingInterval : Nat := 210000

/-- Transcription of `GetBlockSubsidy` (`validation.cpp`) at mainnet parameters.
Block heights are nonnegative, and the `CAmount` right shift `nSubsidy >>= halvings` acts on the
nonnegative value `50 * COIN`, so it is division by `2 ^ halvings`; the source returns `0`
outright once `halvings >= 64`, where the C++ shift would be undefined. -/
def coreSubsidy (height : Nat) : Nat :=
  let halvings := height / halvingInterval
  if 64 ≤ halvings then 0 else (50 * COIN) >>> halvings

/-- Declarative issuance schedule: fifty bitcoin, halved once per `halvingInterval` blocks. -/
def specSubsidy (height : Nat) : Nat := (50 * COIN) / 2 ^ (height / halvingInterval)

/-- Total subsidy of all blocks at heights `0, 1, …, n - 1`, as `GetBlockSubsidy` computes it. -/
def issuedBelow : Nat → Nat
  | 0 => 0
  | n + 1 => issuedBelow n + coreSubsidy n

/-- Sum of the per-interval subsidies for the first `m` intervals. -/
def intervalSum : Nat → Nat
  | 0 => 0
  | m + 1 => intervalSum m + (50 * COIN) / 2 ^ m

/-- The first height whose subsidy is zero: thirty-three halvings. -/
def zeroHeight : Nat := 33 * halvingInterval

end BitcoinSubsidy
