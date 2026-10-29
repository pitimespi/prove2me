import Definitions.Def_BitcoinHtlc

/-!
# The Lightning funding output

A channel's funds sit in the funding transaction's output, a pay-to-witness-script-hash of the
2-of-2 script `2 <pubkey1> <pubkey2> 2 OP_CHECKMULTISIG` (BOLT #3, with the keys in lexicographic
order). Every commitment transaction spends it with the witness `0 <sig1> <sig2>`. This file states
the script and its single spending condition as the script and verification missions model them.
-/

namespace BitcoinFunding

open BitcoinScript BitcoinSig BitcoinVerify BitcoinToLocal

/-- The BOLT #3 funding witness script, parsed: `2 <pubkey1> <pubkey2> 2 OP_CHECKMULTISIG`. -/
def fundingScript (pubkey1 pubkey2 : Bytes) : Script :=
  [numInstr 2, .push pubkey1, .push pubkey2, numInstr 2, .op OP_CHECKMULTISIG]

/-- The funding witness script as `CScript` serializes it. -/
def fundingBytes (pubkey1 pubkey2 : Bytes) : Bytes :=
  numBytes 2 ++ pushBytes pubkey1 ++ pushBytes pubkey2 ++ numBytes 2 ++ [OP_CHECKMULTISIG]

/-- The only way to satisfy the funding script with a witness stack `st` (top first): three
elements `[sig2, sig1, dummy]`, `sig1` valid for `pubkey1`, `sig2` valid for `pubkey2`, and an empty
dummy when `NULLDUMMY` is enforced. (In `CScriptWitness` order the witness is `dummy sig1 sig2`.) -/
def FundingSpend (f : Flags) (o : Oracle) (pubkey1 pubkey2 : Bytes) (st : List Bytes) : Prop :=
  ∃ sig1 sig2 dummy, st = [sig2, sig1, dummy] ∧
    o.checkSig sig1 pubkey1 = some true ∧ o.checkSig sig2 pubkey2 = some true ∧
    (f.nulldummy = true → dummy = [])

end BitcoinFunding
