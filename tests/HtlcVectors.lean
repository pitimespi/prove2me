import Definitions.Def_BitcoinHtlc

/-! Concrete checks of the two BOLT #3 HTLC scripts against a stub oracle: the signature check
accepts a signature exactly when it equals the key's "expected" byte string, `hash160` tags its input
with a leading `0xa9` byte (keeping the first three bytes), and `checkLockTime` accepts expiries up
to 600. Witness stacks are written top first (the reverse of BOLT #3's `CScriptWitness` order). -/

open BitcoinScript BitcoinHtlc BitcoinToLocal

def revKey : Bytes := [0x02, 0xaa, 0xbb]
def remKey : Bytes := [0x03, 0xcc, 0xdd]
def locKey : Bytes := [0x02, 0xee, 0xff]
def sigFor (pk : Bytes) : Bytes := 0x30 :: pk
def stubH (b : Bytes) : Bytes := 0xa9 :: b.take 3
def pre32 : Bytes := List.replicate 32 0x11
def other32 : Bytes := List.replicate 32 0x22
def revHash : Bytes := stubH revKey
def payHash : Bytes := stubH pre32

def stubOracle : Oracle where
  ripemd160 := id
  sha1 := id
  sha256 := id
  hash160 := stubH
  hash256 := id
  checkSig := fun sig pk => some (decide (sig = sigFor pk))
  checkLockTime := fun n => decide (n ≤ 600)
  checkSequence := fun _ => true

def flagsOn : Flags := ⟨true, true, true⟩
def flagsNoDummy : Flags := ⟨true, true, false⟩
def flagsNoCltv : Flags := ⟨false, true, true⟩

def O : Script := offeredScript revHash remKey locKey payHash
def R (e : Int) : Script := receivedScript revHash remKey locKey payHash e

/-! ### Offered HTLC -/

-- revocation: `<revocation_sig> <revocationpubkey>`
example : evalScript flagsOn stubOracle [revKey, sigFor revKey] O = some [[1]] := by decide +kernel
-- revocation key with the wrong signature: a clean false
example : evalScript flagsOn stubOracle [revKey, sigFor remKey] O = some [[]] := by decide +kernel
-- preimage: `<remotehtlcsig> <payment_preimage>`
example : evalScript flagsOn stubOracle [pre32, sigFor remKey] O = some [[1]] := by decide +kernel
-- preimage with the local signature instead: false
example : evalScript flagsOn stubOracle [pre32, sigFor locKey] O = some [[]] := by decide +kernel
-- a 32-byte element that is not the preimage: OP_EQUALVERIFY fails the script
example : evalScript flagsOn stubOracle [other32, sigFor remKey] O = none := by decide +kernel
-- timeout: `0 <remotehtlcsig> <localhtlcsig> <>` (top first: selector, local sig, remote sig, dummy)
example : evalScript flagsOn stubOracle [[], sigFor locKey, sigFor remKey, []] O = some [[1]] := by decide +kernel
-- timeout with the two signatures swapped: false (each signature must match its own key)
example : evalScript flagsOn stubOracle [[], sigFor remKey, sigFor locKey, []] O = some [[]] := by decide +kernel
-- timeout with a non-empty dummy: fails under NULLDUMMY, passes without it
example : evalScript flagsOn stubOracle [[], sigFor locKey, sigFor remKey, [1]] O = none := by decide +kernel
example : evalScript flagsNoDummy stubOracle [[], sigFor locKey, sigFor remKey, [1]] O = some [[1]] := by decide +kernel
-- timeout with a 31-byte selector still takes the NOTIF branch
example : evalScript flagsOn stubOracle [List.replicate 31 0, sigFor locKey, sigFor remKey, []] O = some [[1]] := by decide +kernel
-- wrong shapes
example : evalScript flagsOn stubOracle [] O = none := by decide +kernel
example : evalScript flagsOn stubOracle [revKey] O = none := by decide +kernel
example : evalScript flagsOn stubOracle [[], sigFor locKey, sigFor remKey] O = none := by decide +kernel
example : evalScript flagsOn stubOracle [[], sigFor locKey] O = none := by decide +kernel
example : evalScript flagsOn stubOracle [revKey, sigFor revKey, [9]] O = some [[1], [9]] := by decide +kernel

/-! ### Received HTLC -/

-- revocation
example : evalScript flagsOn stubOracle [revKey, sigFor revKey] (R 500) = some [[1]] := by decide +kernel
-- success: `0 <remotehtlcsig> <localhtlcsig> <payment_preimage>`
example : evalScript flagsOn stubOracle [pre32, sigFor locKey, sigFor remKey, []] (R 500) = some [[1]] := by decide +kernel
-- success with swapped signatures: false
example : evalScript flagsOn stubOracle [pre32, sigFor remKey, sigFor locKey, []] (R 500) = some [[]] := by decide +kernel
-- success with a non-empty dummy under NULLDUMMY: fails
example : evalScript flagsOn stubOracle [pre32, sigFor locKey, sigFor remKey, [1]] (R 500) = none := by decide +kernel
-- a 32-byte element that is not the preimage: OP_EQUALVERIFY fails the script
example : evalScript flagsOn stubOracle [other32, sigFor locKey, sigFor remKey, []] (R 500) = none := by decide +kernel
-- timeout: `<remotehtlcsig> <>`, expiry accepted by the stub checker
example : evalScript flagsOn stubOracle [[], sigFor remKey] (R 500) = some [[1]] := by decide +kernel
-- expiry rejected by the stub checker: CLTV fails the script
example : evalScript flagsOn stubOracle [[], sigFor remKey] (R 601) = none := by decide +kernel
-- CLTV flag off: the opcode is a NOP and the timeout path opens regardless
example : evalScript flagsNoCltv stubOracle [[], sigFor remKey] (R 601) = some [[1]] := by decide +kernel
-- negative expiry with CLTV on: fails
example : evalScript flagsOn stubOracle [[], sigFor remKey] (R (-1)) = none := by decide +kernel
-- timeout with the local signature: false
example : evalScript flagsOn stubOracle [[], sigFor locKey] (R 500) = some [[]] := by decide +kernel
-- wrong shapes
example : evalScript flagsOn stubOracle [] (R 500) = none := by decide +kernel
example : evalScript flagsOn stubOracle [[]] (R 500) = none := by decide +kernel
example : evalScript flagsOn stubOracle [[], sigFor remKey, [9]] (R 500) = some [[1], [9]] := by decide +kernel

/-! ### Byte forms -/

example : BitcoinSig.parseScript (offeredBytes revHash remKey locKey payHash) = some O := by decide +kernel
example : BitcoinSig.parseScript (receivedBytes revHash remKey locKey payHash 500) = some (R 500) := by decide +kernel
example : BitcoinSig.parseScript (receivedBytes revHash remKey locKey payHash 16) = some (R 16) := by decide +kernel
-- `2` is `OP_2 = 0x52`, `32` is the script-number push `01 20`, the expiry 500 is `02 f4 01`
example : offeredBytes revHash remKey locKey payHash =
    [0x76, 0xa9, 0x04, 0xa9, 0x02, 0xaa, 0xbb, 0x87, 0x63, 0xac, 0x67, 0x03, 0x03, 0xcc, 0xdd, 0x7c, 0x82,
     0x01, 0x20, 0x87, 0x64, 0x75, 0x52, 0x7c, 0x03, 0x02, 0xee, 0xff, 0x52, 0xae, 0x67, 0xa9, 0x04, 0xa9,
     0x11, 0x11, 0x11, 0x88, 0xac, 0x68, 0x68] := by decide +kernel
example : receivedBytes revHash remKey locKey payHash 500 =
    [0x76, 0xa9, 0x04, 0xa9, 0x02, 0xaa, 0xbb, 0x87, 0x63, 0xac, 0x67, 0x03, 0x03, 0xcc, 0xdd, 0x7c, 0x82,
     0x01, 0x20, 0x87, 0x63, 0xa9, 0x04, 0xa9, 0x11, 0x11, 0x11, 0x88, 0x52, 0x7c, 0x03, 0x02, 0xee, 0xff,
     0x52, 0xae, 0x67, 0x75, 0x02, 0xf4, 0x01, 0xb1, 0x75, 0xac, 0x68, 0x68] := by decide +kernel

/-! ### The spend predicates hold on the five BOLT #3 witnesses (witnessed explicitly: they are existentials) -/

example : OfferedSpend flagsOn stubOracle revHash remKey locKey payHash [revKey, sigFor revKey] :=
  Or.inl ⟨_, _, rfl, by decide +kernel, by decide +kernel⟩
example : OfferedSpend flagsOn stubOracle revHash remKey locKey payHash [pre32, sigFor remKey] :=
  Or.inr (Or.inl ⟨_, _, rfl, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩)
example : OfferedSpend flagsOn stubOracle revHash remKey locKey payHash [[], sigFor locKey, sigFor remKey, []] :=
  Or.inr (Or.inr ⟨_, _, _, _, rfl, by decide +kernel, by decide +kernel, by decide +kernel, fun _ => rfl⟩)
example : ReceivedSpend flagsOn stubOracle revHash remKey locKey payHash 500 [revKey, sigFor revKey] :=
  Or.inl ⟨_, _, rfl, by decide +kernel, by decide +kernel⟩
example : ReceivedSpend flagsOn stubOracle revHash remKey locKey payHash 500 [pre32, sigFor locKey, sigFor remKey, []] :=
  Or.inr (Or.inl ⟨_, _, _, _, rfl, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, fun _ => rfl⟩)
example : ReceivedSpend flagsOn stubOracle revHash remKey locKey payHash 500 [[], sigFor remKey] :=
  Or.inr (Or.inr ⟨_, _, rfl, by decide +kernel, by decide +kernel, Or.inr ⟨by decide, by decide +kernel⟩, by decide +kernel⟩)
