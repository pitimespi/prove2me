import Definitions.Def_BitcoinPenalty

/-! Concrete checks of the penalty witnesses against a stub oracle (the one of
`tests/AnchorsVectors.lean`): the signature check accepts a signature exactly when it equals the
key's "expected" byte string, rejects `[0xff]` outright, `hash160` tags its input with a leading
`0xa9` byte (keeping the first three bytes), `checkLockTime` accepts expiries up to 600 and
`checkSequence` accepts delays up to a configurable bound. Stacks are written top first (the
reverse of BOLT #3's `CScriptWitness` order): the penalty witness `<revocation_sig> 1` is the
stack `[[1], sigR]`, `<revocation_sig> <revocationpubkey>` is `[revPk, sigR]`. -/

open BitcoinScript BitcoinPenalty BitcoinToLocal

def revKey : Bytes := [0x02, 0xaa, 0xbb]
def delKey : Bytes := [0x03, 0x11, 0x22]
def remKey : Bytes := [0x03, 0xcc, 0xdd]
def locKey : Bytes := [0x02, 0xee, 0xff]
def toRemKey : Bytes := [0x02, 0x55, 0x66]
def funLocal : Bytes := [0x03, 0x12, 0x34]
def funRemote : Bytes := [0x02, 0x43, 0x21]
def sigFor (pk : Bytes) : Bytes := 0x30 :: pk
def stubH (b : Bytes) : Bytes := 0xa9 :: b.take 3
def pre32 : Bytes := List.replicate 32 0x11
def payH : Bytes := stubH pre32

def K : CommitmentKeys :=
  { revPk := revKey, revHash := stubH revKey, localDelayedPk := delKey, remoteKey := toRemKey,
    localHtlcKey := locKey, remoteHtlcKey := remKey, fundingKeyLocal := funLocal, fundingKeyRemote := funRemote,
    toSelfDelay := 144 }

def H : Htlc := { payHash := payH, expiry := 500 }

/-- The stub oracle, accepting `OP_CHECKSEQUENCEVERIFY` operands up to `maxSeq`. -/
def mkOracle (maxSeq : Int) : Oracle where
  ripemd160 := id
  sha1 := id
  sha256 := id
  hash160 := stubH
  hash256 := id
  checkSig := fun sig pk => if sig = [0xff] then none else some (decide (sig = sigFor pk))
  checkLockTime := fun n => decide (n ≤ 600)
  checkSequence := fun n => decide (n ≤ maxSeq)

def o0 : Oracle := mkOracle 0        -- the commitment was just confirmed
def o1 : Oracle := mkOracle 1        -- one block later
def o143 : Oracle := mkOracle 143    -- one block short of `to_self_delay`
def o144 : Oracle := mkOracle 144    -- `to_self_delay` blocks later

def flagsOn : Flags := ⟨true, true, true⟩
def flagsNoCsv : Flags := ⟨true, false, true⟩

/-! ### The honest party's side: `HoldsRevocation` holds for the stub oracle -/

example : HoldsRevocation o0 K := ⟨⟨sigFor revKey, by decide, by decide⟩, by decide⟩
example : NoRevHashPreimage o0 K → False := fun h => by
  have := h [0x02, 0xaa, 0xbb, 0x99] (by decide)   -- the stub hash is not second-preimage resistant
  exact absurd this (by decide)

/-! ### `to_local`: `OP_IF <revPk> OP_ELSE 144 OP_CSV OP_DROP <delKey> OP_ENDIF OP_CHECKSIG` -/

def TL : Script := toLocalScript revKey 144 delKey

-- the penalty `<revocation_sig> 1`: accepted at once, no blocks needed
example : evalScript flagsOn o0 [[1], sigFor revKey] TL = some [[1]] := by decide +kernel
-- the penalty witness in `CScriptWitness` order is `[sigR, [1], script]`
example : toLocalPenaltyWitness K (sigFor revKey) = [sigFor revKey, [1], toLocalBytes K] := rfl
-- the cheater's delayed path `<local_delayedsig> 0`: rejected until `to_self_delay` blocks have passed
example : evalScript flagsOn o0 [[], sigFor delKey] TL = none := by decide +kernel
example : evalScript flagsOn o143 [[], sigFor delKey] TL = none := by decide +kernel
example : evalScript flagsOn o144 [[], sigFor delKey] TL = some [[1]] := by decide +kernel
-- the cheater cannot use the `OP_IF` branch: its delayed-key signature is not a revocation signature
example : evalScript flagsOn o144 [[1], sigFor delKey] TL = some [[]] := by decide +kernel
-- nor the `OP_ELSE` branch with a revocation signature in place of the delayed one
example : evalScript flagsOn o144 [[], sigFor revKey] TL = some [[]] := by decide +kernel
-- without the CSV flag the delay is not enforced (pre-BIP 112 semantics)
example : evalScript flagsNoCsv o0 [[], sigFor delKey] TL = some [[1]] := by decide +kernel
-- the spend predicates
example : SpendCondition flagsOn o0 revKey 144 delKey [1] (sigFor revKey) := Or.inl ⟨by decide, by decide⟩
example : DelayedSpend flagsOn o144 K [] (sigFor delKey) := ⟨by decide, by decide, by decide⟩
example : ¬ DelayedSpend flagsOn o0 K [] (sigFor delKey) := fun ⟨_, h, _⟩ => by
  revert h; decide
-- the byte form parses back to the script
example : BitcoinSig.parseScript (toLocalBytes K) = some TL := by decide +kernel

/-! ### Offered HTLC, non-anchor form -/

def OF : Script := BitcoinHtlc.offeredScript (stubH revKey) remKey locKey payH

-- the penalty `<revocation_sig> <revocationpubkey>`: accepted at once
example : evalScript flagsOn o0 [revKey, sigFor revKey] OF = some [[1]] := by decide +kernel
example : htlcPenaltyWitness K (sigFor revKey) (offeredBytes K H) = [sigFor revKey, revKey, offeredBytes K H] := rfl
-- the revocation branch with a wrong signature: a clean false, not a spend
example : evalScript flagsOn o0 [revKey, sigFor remKey] OF = some [[]] := by decide +kernel
-- the cheater's paths: preimage (remote) and timeout (2-of-2)
example : evalScript flagsOn o0 [pre32, sigFor remKey] OF = some [[1]] := by decide +kernel
example : evalScript flagsOn o0 [[], sigFor locKey, sigFor remKey, []] OF = some [[1]] := by decide +kernel
example : OfferedNonRevocation flagsOn o0 K H [pre32, sigFor remKey] :=
  Or.inl ⟨pre32, sigFor remKey, rfl, by decide, by decide, by decide, by decide⟩
example : BitcoinSig.parseScript (offeredBytes K H) = some OF := by decide +kernel

/-! ### Received HTLC, non-anchor form -/

def RC : Script := BitcoinHtlc.receivedScript (stubH revKey) remKey locKey payH 500

example : evalScript flagsOn o0 [revKey, sigFor revKey] RC = some [[1]] := by decide +kernel
example : evalScript flagsOn o0 [revKey, sigFor remKey] RC = some [[]] := by decide +kernel
-- the cheater's paths: success (preimage + 2-of-2) and timeout (CLTV 500 + remote)
example : evalScript flagsOn o0 [pre32, sigFor locKey, sigFor remKey, []] RC = some [[1]] := by decide +kernel
example : evalScript flagsOn o0 [[], sigFor remKey] RC = some [[1]] := by decide +kernel
example : ReceivedNonRevocation flagsOn o0 K H [[], sigFor remKey] :=
  Or.inr ⟨[], sigFor remKey, rfl, by decide, by decide, Or.inr ⟨by decide, by decide⟩, by decide⟩
example : BitcoinSig.parseScript (receivedBytes K H) = some RC := by decide +kernel

/-! ### HTLCs with `option_anchors`: the penalty skips `1 OP_CHECKSEQUENCEVERIFY`, the cheater does not -/

def OFA : Script := BitcoinAnchors.offeredScript (stubH revKey) remKey locKey payH
def RCA : Script := BitcoinAnchors.receivedScript (stubH revKey) remKey locKey payH 500

example : evalScript flagsOn o0 [revKey, sigFor revKey] OFA = some [[1]] := by decide +kernel
example : evalScript flagsOn o0 [revKey, sigFor revKey] RCA = some [[1]] := by decide +kernel
-- the cheater's preimage / success / timeout paths wait one block
example : evalScript flagsOn o0 [pre32, sigFor remKey] OFA = none := by decide +kernel
example : evalScript flagsOn o1 [pre32, sigFor remKey] OFA = some [[1]] := by decide +kernel
example : evalScript flagsOn o0 [pre32, sigFor locKey, sigFor remKey, []] RCA = none := by decide +kernel
example : evalScript flagsOn o1 [pre32, sigFor locKey, sigFor remKey, []] RCA = some [[1]] := by decide +kernel
example : evalScript flagsOn o0 [[], sigFor remKey] RCA = none := by decide +kernel
example : evalScript flagsOn o1 [[], sigFor remKey] RCA = some [[1]] := by decide +kernel
example : OfferedNonRevocationAnchors flagsOn o1 K H [pre32, sigFor remKey] :=
  ⟨Or.inl ⟨pre32, sigFor remKey, rfl, by decide, by decide, by decide, by decide⟩, Or.inr ⟨by decide, Or.inr (by decide)⟩⟩
example : BitcoinSig.parseScript (offeredBytesAnchors K H) = some OFA := by decide +kernel
example : BitcoinSig.parseScript (receivedBytesAnchors K H) = some RCA := by decide +kernel

/-! ### `to_remote` and anchors: no revocation path -/

def TR : Script := BitcoinAnchors.toRemoteScript toRemKey
def AL : Script := BitcoinAnchors.anchorScript funLocal

-- `to_remote` is the counterparty's balance: only its key spends, after one block
example : evalScript flagsOn o1 [sigFor toRemKey] TR = some [[1]] := by decide +kernel
example : evalScript flagsOn o1 [sigFor revKey] TR = none := by decide +kernel
-- the broadcaster's anchor: its funding key at once, anyone (`<>`) after 16 blocks
example : evalScript flagsOn o0 [sigFor funLocal] AL = some [[1]] := by decide +kernel
example : evalScript flagsOn (mkOracle 16) [[]] AL = some [[16]] := by decide +kernel
example : evalScript flagsOn o1 [[]] AL = none := by decide +kernel
example : BitcoinSig.parseScript (anchorLocalBytes K) = some AL := by decide +kernel
