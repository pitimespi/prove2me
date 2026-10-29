import Definitions.Def_BitcoinAnchors

/-! Concrete checks of the four BOLT #3 `option_anchors` scripts against a stub oracle: the signature
check accepts a signature exactly when it equals the key's "expected" byte string, rejects the
signature `[0xff]` outright (`none`, as a bad encoding would), `hash160` tags its input with a
leading `0xa9` byte (keeping the first three bytes), `checkLockTime` accepts expiries up to 600, and
`checkSequence` accepts delays up to a configurable bound. Witness stacks are written top first
(the reverse of BOLT #3's `CScriptWitness` order). -/

open BitcoinScript BitcoinAnchors BitcoinToLocal

def revKey : Bytes := [0x02, 0xaa, 0xbb]
def remKey : Bytes := [0x03, 0xcc, 0xdd]
def locKey : Bytes := [0x02, 0xee, 0xff]
def funKey : Bytes := [0x03, 0x12, 0x34]
def sigFor (pk : Bytes) : Bytes := 0x30 :: pk
def stubH (b : Bytes) : Bytes := 0xa9 :: b.take 3
def pre32 : Bytes := List.replicate 32 0x11
def other32 : Bytes := List.replicate 32 0x22
def revHash : Bytes := stubH revKey
def payHash : Bytes := stubH pre32

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

def oSeq16 : Oracle := mkOracle 16   -- 16 blocks have passed
def oSeq1 : Oracle := mkOracle 1     -- one block has passed
def oSeq0 : Oracle := mkOracle 0     -- nothing has passed

def flagsOn : Flags := ⟨true, true, true⟩
def flagsNoCsv : Flags := ⟨true, false, true⟩
def flagsNoDummy : Flags := ⟨true, true, false⟩

/-! ### `to_remote` -/

def T : Script := toRemoteScript remKey

-- `<remote_sig>` after one block: the pushed `1` is left
example : evalScript flagsOn oSeq1 [sigFor remKey] T = some [[1]] := by decide +kernel
-- before the block: CSV fails the script
example : evalScript flagsOn oSeq0 [sigFor remKey] T = none := by decide +kernel
-- CSV flag off: no delay enforced
example : evalScript flagsNoCsv oSeq0 [sigFor remKey] T = some [[1]] := by decide +kernel
-- wrong signature: OP_CHECKSIGVERIFY fails the script (no false value left)
example : evalScript flagsOn oSeq1 [sigFor locKey] T = none := by decide +kernel
-- rejected signature encoding: fails
example : evalScript flagsOn oSeq1 [[0xff]] T = none := by decide +kernel
-- wrong shapes
example : evalScript flagsOn oSeq1 [] T = none := by decide +kernel
example : evalScript flagsOn oSeq1 [sigFor remKey, [9]] T = some [[1], [9]] := by decide +kernel

/-! ### Anchor -/

def A : Script := anchorScript funKey

-- the key holder's `<sig>`: spends at once (no delay needed)
example : evalScript flagsOn oSeq0 [sigFor funKey] A = some [[1]] := by decide +kernel
-- anyone's `<>` after 16 blocks: the `16` of the delay check is left
example : evalScript flagsOn oSeq16 [[]] A = some [[16]] := by decide +kernel
-- anyone's `<>` before 16 blocks: fails
example : evalScript flagsOn oSeq1 [[]] A = none := by decide +kernel
-- CSV flag off: `<>` spends regardless
example : evalScript flagsNoCsv oSeq0 [[]] A = some [[16]] := by decide +kernel
-- a wrong (but cleanly rejected) signature behaves like `<>`
example : evalScript flagsOn oSeq16 [sigFor remKey] A = some [[16]] := by decide +kernel
example : evalScript flagsOn oSeq1 [sigFor remKey] A = none := by decide +kernel
-- a signature the checker rejects outright: fails even after the delay
example : evalScript flagsOn oSeq16 [[0xff]] A = none := by decide +kernel
-- wrong shapes
example : evalScript flagsOn oSeq16 [] A = none := by decide +kernel
example : evalScript flagsOn oSeq16 [[], [9]] A = some [[16], [9]] := by decide +kernel
example : evalScript flagsOn oSeq0 [sigFor funKey, [9]] A = some [[1], [9]] := by decide +kernel

/-! ### Offered HTLC (`option_anchors`) -/

def O : Script := offeredScript revHash remKey locKey payHash

-- revocation: no delay needed
example : evalScript flagsOn oSeq0 [revKey, sigFor revKey] O = some [[1]] := by decide +kernel
example : evalScript flagsOn oSeq0 [revKey, sigFor remKey] O = some [[]] := by decide +kernel
-- preimage: needs the one-block delay
example : evalScript flagsOn oSeq1 [pre32, sigFor remKey] O = some [[1]] := by decide +kernel
example : evalScript flagsOn oSeq0 [pre32, sigFor remKey] O = none := by decide +kernel
example : evalScript flagsNoCsv oSeq0 [pre32, sigFor remKey] O = some [[1]] := by decide +kernel
-- preimage with the local signature: a clean false (after the delay)
example : evalScript flagsOn oSeq1 [pre32, sigFor locKey] O = some [[]] := by decide +kernel
-- wrong 32-byte element: OP_EQUALVERIFY fails
example : evalScript flagsOn oSeq1 [other32, sigFor remKey] O = none := by decide +kernel
-- timeout: needs the one-block delay
example : evalScript flagsOn oSeq1 [[], sigFor locKey, sigFor remKey, []] O = some [[1]] := by decide +kernel
example : evalScript flagsOn oSeq0 [[], sigFor locKey, sigFor remKey, []] O = none := by decide +kernel
example : evalScript flagsOn oSeq1 [[], sigFor remKey, sigFor locKey, []] O = some [[]] := by decide +kernel
example : evalScript flagsOn oSeq1 [[], sigFor locKey, sigFor remKey, [1]] O = none := by decide +kernel
example : evalScript flagsNoDummy oSeq1 [[], sigFor locKey, sigFor remKey, [1]] O = some [[1]] := by decide +kernel
-- wrong shapes
example : evalScript flagsOn oSeq1 [] O = none := by decide +kernel
example : evalScript flagsOn oSeq1 [[], sigFor locKey, sigFor remKey] O = none := by decide +kernel

/-! ### Received HTLC (`option_anchors`) -/

def R (e : Int) : Script := receivedScript revHash remKey locKey payHash e

-- revocation: no delay needed
example : evalScript flagsOn oSeq0 [revKey, sigFor revKey] (R 500) = some [[1]] := by decide +kernel
-- success: needs the one-block delay
example : evalScript flagsOn oSeq1 [pre32, sigFor locKey, sigFor remKey, []] (R 500) = some [[1]] := by decide +kernel
example : evalScript flagsOn oSeq0 [pre32, sigFor locKey, sigFor remKey, []] (R 500) = none := by decide +kernel
example : evalScript flagsOn oSeq1 [pre32, sigFor remKey, sigFor locKey, []] (R 500) = some [[]] := by decide +kernel
example : evalScript flagsOn oSeq1 [pre32, sigFor locKey, sigFor remKey, [1]] (R 500) = none := by decide +kernel
example : evalScript flagsOn oSeq1 [other32, sigFor locKey, sigFor remKey, []] (R 500) = none := by decide +kernel
-- timeout: lock time, then the one-block delay
example : evalScript flagsOn oSeq1 [[], sigFor remKey] (R 500) = some [[1]] := by decide +kernel
example : evalScript flagsOn oSeq0 [[], sigFor remKey] (R 500) = none := by decide +kernel
example : evalScript flagsOn oSeq1 [[], sigFor remKey] (R 601) = none := by decide +kernel
example : evalScript flagsOn oSeq1 [[], sigFor remKey] (R (-1)) = none := by decide +kernel
example : evalScript flagsOn oSeq1 [[], sigFor locKey] (R 500) = some [[]] := by decide +kernel
-- wrong shapes
example : evalScript flagsOn oSeq1 [] (R 500) = none := by decide +kernel
example : evalScript flagsOn oSeq1 [[]] (R 500) = none := by decide +kernel

/-! ### Byte forms -/

-- `1` is `OP_1 = 0x51`, `16` is `OP_16 = 0x60`
example : toRemoteBytes remKey = [0x03, 0x03, 0xcc, 0xdd, 0xad, 0x51, 0xb2] := by decide +kernel
example : anchorBytes funKey = [0x03, 0x03, 0x12, 0x34, 0xac, 0x73, 0x64, 0x60, 0xb2, 0x68] := by decide +kernel
example : offeredBytes revHash remKey locKey payHash =
    [0x76, 0xa9, 0x04, 0xa9, 0x02, 0xaa, 0xbb, 0x87, 0x63, 0xac, 0x67, 0x03, 0x03, 0xcc, 0xdd, 0x7c, 0x82,
     0x01, 0x20, 0x87, 0x64, 0x75, 0x52, 0x7c, 0x03, 0x02, 0xee, 0xff, 0x52, 0xae, 0x67, 0xa9, 0x04, 0xa9,
     0x11, 0x11, 0x11, 0x88, 0xac, 0x68, 0x51, 0xb2, 0x75, 0x68] := by decide +kernel
example : receivedBytes revHash remKey locKey payHash 500 =
    [0x76, 0xa9, 0x04, 0xa9, 0x02, 0xaa, 0xbb, 0x87, 0x63, 0xac, 0x67, 0x03, 0x03, 0xcc, 0xdd, 0x7c, 0x82,
     0x01, 0x20, 0x87, 0x63, 0xa9, 0x04, 0xa9, 0x11, 0x11, 0x11, 0x88, 0x52, 0x7c, 0x03, 0x02, 0xee, 0xff,
     0x52, 0xae, 0x67, 0x75, 0x02, 0xf4, 0x01, 0xb1, 0x75, 0xac, 0x68, 0x51, 0xb2, 0x75, 0x68] := by decide +kernel
example : BitcoinSig.parseScript (toRemoteBytes remKey) = some T := by decide +kernel
example : BitcoinSig.parseScript (anchorBytes funKey) = some A := by decide +kernel
example : BitcoinSig.parseScript (offeredBytes revHash remKey locKey payHash) = some O := by decide +kernel
example : BitcoinSig.parseScript (receivedBytes revHash remKey locKey payHash 500) = some (R 500) := by decide +kernel

/-! ### The spend predicates hold on the BOLT #3 witnesses (witnessed explicitly: they are existentials) -/

example : ToRemoteSpend flagsOn oSeq1 remKey [sigFor remKey] :=
  ⟨_, rfl, by decide +kernel, Or.inr ⟨by decide, Or.inr (by decide +kernel)⟩⟩
example : AnchorSpend flagsOn oSeq0 funKey [sigFor funKey] :=
  ⟨_, rfl, Or.inl (by decide +kernel)⟩
example : AnchorSpend flagsOn oSeq16 funKey [[]] :=
  ⟨_, rfl, Or.inr ⟨by decide +kernel, Or.inr ⟨by decide, Or.inr (by decide +kernel)⟩⟩⟩
example : OfferedSpend flagsOn oSeq1 revHash remKey locKey payHash [pre32, sigFor remKey] :=
  Or.inr (Or.inl ⟨_, _, rfl, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    Or.inr ⟨by decide, Or.inr (by decide +kernel)⟩⟩)
example : OfferedSpend flagsOn oSeq1 revHash remKey locKey payHash [[], sigFor locKey, sigFor remKey, []] :=
  Or.inr (Or.inr ⟨_, _, _, _, rfl, by decide +kernel, by decide +kernel, by decide +kernel, fun _ => rfl,
    Or.inr ⟨by decide, Or.inr (by decide +kernel)⟩⟩)
example : ReceivedSpend flagsOn oSeq1 revHash remKey locKey payHash 500 [pre32, sigFor locKey, sigFor remKey, []] :=
  Or.inr (Or.inl ⟨_, _, _, _, rfl, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, fun _ => rfl,
    Or.inr ⟨by decide, Or.inr (by decide +kernel)⟩⟩)
example : ReceivedSpend flagsOn oSeq1 revHash remKey locKey payHash 500 [[], sigFor remKey] :=
  Or.inr (Or.inr ⟨_, _, rfl, by decide +kernel, by decide +kernel, Or.inr ⟨by decide, by decide +kernel⟩, by decide +kernel,
    Or.inr ⟨by decide, Or.inr (by decide +kernel)⟩⟩)
