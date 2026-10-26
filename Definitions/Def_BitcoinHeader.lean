import Std

namespace BitcoinHeader

/-! Transcription of the contextual block-header rules of Bitcoin Core at revision
`a773e1e33b349dc819b5a0edc1c7a4839dc73b48`: `CBlockIndex::GetMedianTimePast` (`chain.h`),
`ContextualCheckBlockHeader` (`validation.cpp`), `DeploymentActiveAfter` for buried deployments
(`deploymentstatus.h`), `MAX_FUTURE_BLOCK_TIME` (`chain.h`), and the mainnet activation heights
of BIP34, BIP66 and BIP65 (`kernel/chainparams.cpp`), with `enforce_BIP94 = false` as on mainnet.

A chain of ancestors is represented by the list of its block times, most recent first
(`pindex`, `pindex->pprev`, …). The required `nBits` is supplied by the caller, as it is computed
by `GetNextWorkRequired` in the proof-of-work development. -/

/-- `chain.h`: `MAX_FUTURE_BLOCK_TIME = 2 * 60 * 60`. -/
def MAX_FUTURE_BLOCK_TIME : Int := 2 * 60 * 60

/-- `CBlockIndex::nMedianTimeSpan = 11`. -/
def nMedianTimeSpan : Nat := 11

/-- `CMainParams`: `BIP34Height = 227931` (`DEPLOYMENT_HEIGHTINCB`). -/
def BIP34Height : Nat := 227931

/-- `CMainParams`: `BIP66Height = 363725` (`DEPLOYMENT_DERSIG`). -/
def BIP66Height : Nat := 363725

/-- `CMainParams`: `BIP65Height = 388381` (`DEPLOYMENT_CLTV`). -/
def BIP65Height : Nat := 388381

/-- The window `GetMedianTimePast` sorts: the times of the block and its ancestors, at most
`nMedianTimeSpan` of them. -/
def timeWindow (times : List Int) : List Int := times.take nMedianTimeSpan

/-- `GetMedianTimePast`: sort the window and take the element at index `size / 2`. The result is
`0` for an empty chain, which the source never queries. -/
def medianTimePast (times : List Int) : Int :=
  let w := timeWindow times
  (w.mergeSort fun a b => decide (a ≤ b)).getD (w.length / 2) 0

/-- A block header, reduced to the fields the contextual rules read. -/
structure Header where
  version : Int
  time : Int
  bits : BitVec 32

/-- `DeploymentActiveAfter(pindexPrev, dep)` for a buried deployment:
`pindexPrev->nHeight + 1 >= DeploymentHeight(dep)`. -/
def activeAfter (prevHeight : Nat) (deploymentHeight : Nat) : Bool :=
  decide (deploymentHeight ≤ prevHeight + 1)

/-- The version floor of `ContextualCheckBlockHeader`: rejected when the version is below 2, 3
or 4 while BIP34, BIP66 or BIP65 respectively is active for the next block. -/
def versionOutdated (version : Int) (prevHeight : Nat) : Bool :=
  (decide (version < 2) && activeAfter prevHeight BIP34Height) ||
  (decide (version < 3) && activeAfter prevHeight BIP66Height) ||
  (decide (version < 4) && activeAfter prevHeight BIP65Height)

/-- `ContextualCheckBlockHeader` at mainnet parameters: `nBits` equals the required work, the time
exceeds the previous block's median time past, the time is at most the local clock plus
`MAX_FUTURE_BLOCK_TIME`, and the version is not outdated. `prevTimes` lists the times of the
previous block and its ancestors, most recent first. -/
def contextualCheck (h : Header) (prevHeight : Nat) (prevTimes : List Int) (required : BitVec 32)
    (now : Int) : Bool :=
  decide (h.bits = required) &&
  decide (medianTimePast prevTimes < h.time) &&
  decide (h.time ≤ now + MAX_FUTURE_BLOCK_TIME) &&
  !versionOutdated h.version prevHeight

end BitcoinHeader
