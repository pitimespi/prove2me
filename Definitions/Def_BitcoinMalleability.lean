import Definitions.Def_BitcoinBlockV2
import Definitions.Def_BitcoinVerify

/-!
# Transaction identifiers under SegWit

The txid of a transaction hashes its witness-stripped serialization, which still contains every
`scriptSig`. Before SegWit a third party could alter a signature's encoding inside a `scriptSig`
and change the txid of a valid transaction without invalidating it. For an input that spends a
native witness program, `VerifyScript` requires the `scriptSig` to be empty
(`SCRIPT_ERR_WITNESS_MALLEATED`), so nothing a signer or a third party chooses remains in the
hashed bytes. This file names the sender's intent, the part of a transaction that is not a
signature, so that the theorems can say: for such spends the txid is a function of the intent.
-/

namespace BitcoinMalleability

open BitcoinSer BitcoinBlockV2

/-- What the sender decides: the version, the outpoint and sequence number of every input, the
outputs, and the lock time. The `scriptSig`s and witnesses are not part of it. -/
structure Intent where
  version : Nat
  inputs : List (OutPoint × Nat)
  vout : List TxOut
  nLockTime : Nat
  deriving DecidableEq, Repr

/-- The intent of a transaction. -/
def intentOf (tx : Tx) : Intent :=
  ⟨tx.version, tx.vin.map fun i => (i.prevout, i.nSequence), tx.vout, tx.nLockTime⟩

/-- The canonical transaction of an intent: empty `scriptSig`s and empty witnesses. -/
def ofIntent (t : Intent) : Tx :=
  ⟨t.version, t.inputs.map fun p => ⟨p.1, [], p.2, []⟩, t.vout, t.nLockTime⟩

/-- Every input of `tx` spends, in the ledger `u`, an output whose script is a native witness
program (`CScript::IsWitnessProgram`). -/
def SpendsWitnessPrograms (u : Ledger) (tx : Tx) : Prop :=
  ∀ i ∈ tx.vin, BitcoinVerify.isWitnessProgram (accessCoin u i.prevout).out.scriptPubKey ≠ none

end BitcoinMalleability
