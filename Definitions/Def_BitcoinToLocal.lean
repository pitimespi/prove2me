import Definitions.Def_BitcoinVerify

/-!
# The Lightning `to_local` output under Bitcoin's script interpreter

BOLT #3 (Lightning Network specification, *Bitcoin Transaction and Script Formats*) gives the
`to_local` output of a commitment transaction the witness script

```
OP_IF
    <revocationpubkey>
OP_ELSE
    `to_self_delay`
    OP_CHECKSEQUENCEVERIFY
    OP_DROP
    <local_delayedpubkey>
OP_ENDIF
OP_CHECKSIG
```

paid to as pay-to-witness-script-hash. The intent is that the output can be spent either by the
counterparty with the revocation key at any time, or by the local node with its delayed key once
`to_self_delay` blocks have passed. This file states that script as the script and verification
missions model it, so that the two spending conditions can be proved to be exactly what the
interpreter enforces.
-/

namespace BitcoinToLocal

open BitcoinScript BitcoinSig BitcoinVerify

/-- `CScript::operator<<(int64_t n)`: `OP_1NEGATE` for `-1`, `OP_1` … `OP_16` for `1` … `16`, and the
`CScriptNum` push otherwise (`OP_0`, the empty push, for `0`). -/
def numInstr (n : Int) : Instr :=
  if n = -1 ∨ (1 ≤ n ∧ n ≤ 16) then .op (BitVec.ofNat 8 (n + (OP_1.toNat - 1)).toNat)
  else .push (serialize n)

/-- The bytes `CScript::operator<<(int64_t n)` appends. -/
def numBytes (n : Int) : Bytes :=
  if n = -1 ∨ (1 ≤ n ∧ n ≤ 16) then [BitVec.ofNat 8 (n + (OP_1.toNat - 1)).toNat]
  else pushBytes (serialize n)

/-- The BOLT #3 `to_local` witness script, parsed. -/
def toLocalScript (revocationPubkey : Bytes) (toSelfDelay : Int) (localDelayedPubkey : Bytes) : Script :=
  [.op OP_IF, .push revocationPubkey, .op OP_ELSE, numInstr toSelfDelay, .op OP_CHECKSEQUENCEVERIFY,
   .op OP_DROP, .push localDelayedPubkey, .op OP_ENDIF, .op OP_CHECKSIG]

/-- The BOLT #3 `to_local` witness script, as `CScript` serializes it. -/
def toLocalBytes (revocationPubkey : Bytes) (toSelfDelay : Int) (localDelayedPubkey : Bytes) : Bytes :=
  [OP_IF] ++ pushBytes revocationPubkey ++ [OP_ELSE] ++ numBytes toSelfDelay ++
    [OP_CHECKSEQUENCEVERIFY, OP_DROP] ++ pushBytes localDelayedPubkey ++ [OP_ENDIF, OP_CHECKSIG]

/-- What `OP_CHECKSEQUENCEVERIFY` lets through for the operand `delay`: nothing is checked when the
`CHECKSEQUENCEVERIFY` flag is off; otherwise the operand must be non-negative and either carry the
disable flag (bit 31) or satisfy the checker's `CheckSequence`. -/
def CsvPasses (f : Flags) (o : Oracle) (delay : Int) : Prop :=
  f.csv = false ∨ (0 ≤ delay ∧ ((delay.toNat &&& BitcoinScript.SEQUENCE_LOCKTIME_DISABLE_FLAG) ≠ 0 ∨ o.checkSequence delay = true))

instance (f : Flags) (o : Oracle) (delay : Int) : Decidable (CsvPasses f o delay) := by
  unfold CsvPasses; infer_instance

/-- The two ways of satisfying the `to_local` script with the witness stack `[b, sig]` (top first):
the revocation path, `b` true and `sig` valid for the revocation key; or the delayed path, `b` false,
the delay check passing, and `sig` valid for the delayed key. -/
def SpendCondition (f : Flags) (o : Oracle) (revocationPubkey : Bytes) (toSelfDelay : Int)
    (localDelayedPubkey : Bytes) (b sig : Bytes) : Prop :=
  (castToBool b = true ∧ o.checkSig sig revocationPubkey = some true) ∨
  (castToBool b = false ∧ CsvPasses f o toSelfDelay ∧ o.checkSig sig localDelayedPubkey = some true)

/-- The `nSequence` of input `nIn` of a transaction (an empty input when out of range). -/
def inputSequence (tx : BitcoinSer.Tx) (nIn : Nat) : Nat := (tx.vin.getD nIn ⟨⟨[], 0⟩, [], 0, []⟩).nSequence

end BitcoinToLocal
