# BitcoinHtlc: the BOLT #3 HTLC witness scripts under Core's script interpreter

Files: `Definitions/Def_BitcoinHtlc.lean`, `Solutions/Sol_BitcoinHtlc_all.lean`,
`tests/HtlcVectors.lean`. Sibling mission (same style, reused lemmas): `BitcoinToLocal`.

## The model

Both scripts (non-anchor form) are stated as `Script`s of the `BitcoinScript` interpreter and as
`CScript` byte strings, with four byte-string parameters and, for the received script, an `Int`
expiry:

- `offeredScript revHash remoteKey localKey payHash`, `offeredBytes …` (26 instructions)
- `receivedScript revHash remoteKey localKey payHash expiry`, `receivedBytes …` (29 instructions)

`revHash` stands for `RIPEMD160(SHA256(revocationpubkey))` and `payHash` for
`RIPEMD160(payment_hash)`; they are arbitrary bytes, not tied to any hash function (the hash the
interpreter applies is the oracle's `hash160`). `2` is `CScript << 2`, i.e. `OP_2` (`0x52`), `32`
is `CScript << 32`, i.e. the script-number push `01 20`, and the expiry is `CScript << int64`; all
three are `BitcoinToLocal.numInstr` / `numBytes`. `CltvPasses f o expiry` mirrors `CsvPasses` for
`OP_CHECKLOCKTIMEVERIFY`: the flag is off, or `0 ≤ expiry ∧ o.checkLockTime expiry = true` (there is
no disable bit for lock times).

Witness stacks are top first, as `evalScript` takes them: the reverse of BOLT #3's `CScriptWitness`
listing. In `p2wsh_spend` the witness `ws` is in `CScriptWitness` order and the condition is stated
on `ws.reverse`.

## The exact spend conditions (derived from the interpreter, checked with `#eval` and `decide +kernel`)

`OfferedSpend f o revHash remoteKey localKey payHash st` is the disjunction of

1. revocation: `st = [pk, sig]`, `o.hash160 pk = revHash`, `o.checkSig sig pk = some true`;
2. preimage: `st = [preimage, sig]`, `o.hash160 preimage ≠ revHash`, `preimage.length = 32`,
   `o.hash160 preimage = payHash`, `o.checkSig sig remoteKey = some true`;
3. timeout: `st = [x, localSig, remoteSig, dummy]`, `o.hash160 x ≠ revHash`, `x.length ≠ 32`,
   `multisigLoop o [localSig, remoteSig] [localKey, remoteKey] = some true`,
   `f.nulldummy = true → dummy = []`.

`ReceivedSpend f o revHash remoteKey localKey payHash expiry st` is the disjunction of

1. revocation: as above;
2. success: `st = [preimage, localSig, remoteSig, dummy]`, `o.hash160 preimage ≠ revHash`,
   `preimage.length = 32`, `o.hash160 preimage = payHash`,
   `multisigLoop o [localSig, remoteSig] [localKey, remoteKey] = some true`,
   `f.nulldummy = true → dummy = []`;
3. timeout: `st = [x, sig]`, `o.hash160 x ≠ revHash`, `x.length ≠ 32`, `CltvPasses f o expiry`,
   `o.checkSig sig remoteKey = some true`.

Points worth noting, all forced by the interpreter and not by the BOLT prose:

- The revocation test is `OP_DUP OP_HASH160 <revHash> OP_EQUAL OP_IF`: whichever element is on top
  is hashed, so *every* path first requires `o.hash160 x ≠ revHash` for its top element (`x` is the
  empty selector `<>` on the timeout paths, the preimage on the preimage/success paths). With the
  concrete `hash160` this is automatic; with an abstract oracle it is a genuine side condition.
- The branch selector on the inner `OP_NOTIF`/`OP_IF` is `OP_SIZE 32 OP_EQUAL`: the condition is
  exactly `x.length = 32` (via `serialize ↑x.length = serialize 32 ↔ x.length = 32`, proved from
  `serialize_roundtrip`); any element that is not 32 bytes long selects the multisig (offered) or
  the CLTV (received) branch, not only the empty one.
- `OP_CHECKMULTISIG` reads the keys top down: after `2 OP_SWAP <localKey> 2` the key list is
  `[localKey, remoteKey]`, and the signatures are consumed top down as `[localSig, remoteSig]`, so
  BOLT #3's `0 <remotehtlcsig> <localhtlcsig> …` (which puts `localhtlcsig` nearer the top) matches
  `localSig` with `localKey` first. `multisig_two` unfolds the loop to
  `o.checkSig localSig localKey = some true ∧ o.checkSig remoteSig remoteKey = some true`.
- The dummy is the element *below* the two signatures (the witness's leading `0`); with
  `NULLDUMMY` it must be empty, without the flag it is unconstrained.
- On the preimage/success paths a 32-byte element with the wrong hash fails the script
  (`OP_EQUALVERIFY`) rather than leaving a false value; on the revocation path a wrong signature
  leaves a clean false. The closed-form theorems (`offered_revocation`, …) record this.

## Public theorems (all in `Sol_BitcoinHtlc_all.lean`, names `BitcoinHtlc.*`)

- `cltv_step`: `execOp f o true OP_CHECKLOCKTIMEVERIFY s = if CltvPasses f o expiry then some s else none`
  when the top of the stack is `serialize expiry`, `expiry.natAbs < 2^32`.
- `multisig_two`: `multisigLoop o [s1, s2] [k1, k2] = some true ↔ o.checkSig s1 k1 = some true ∧ o.checkSig s2 k2 = some true`.
- `offered_spends_iff`, `received_spends_iff`: for an arbitrary stack `st`,
  `(∃ res, evalScript f o st script = some res ∧ res.length = 1 ∧ topTrue res = true) ↔ …Spend … st`.
  Hypotheses: the four pushed byte strings are within 520 bytes (and `expiry.natAbs < 2^32`).
  Nothing is assumed about the stack elements or about the length of the oracle's `hash160` output.
- `offered_revocation`, `offered_preimage`, `offered_timeout`, `received_revocation`,
  `received_success`, `received_timeout`: closed-form `evalScript` equations on the exact BOLT #3
  witness shapes (including the false and failing outcomes).
- `parseScript_offered`, `parseScript_received`: the `CScript` byte forms parse to the instruction forms.
- `offered_p2wsh_spend`, `received_p2wsh_spend`: via `BitcoinVerify.p2wsh_correct`, for a P2WSH
  output and a witness `ws ++ [script]`, `verifyScript … = true ↔ castToBool (sha256 script) = true ∧
  (∀ e ∈ ws, e.length ≤ 520) ∧ …Spend (scriptFlagsOf c.flags) (legacyOracle … .witnessV0 script) … ws.reverse`.
- `cltv_concrete`: with `f.cltv = true` and `0 ≤ expiry`,
  `CltvPasses f (legacyOracle …) expiry ↔ checkLockTime tx nIn expiry = true`.
- `checkLockTime_iff`: for `0 ≤ expiry < 500000000`,
  `checkLockTime tx nIn expiry = true ↔ tx.nLockTime < 500000000 ∧ expiry ≤ tx.nLockTime ∧ inputSequence tx nIn ≠ 0xffffffff`.

## Proof structure

- Per-opcode `execOp_*` equations by `rfl` (`OP_DUP`, `OP_SWAP`, `OP_SIZE`, `OP_HASH160`,
  `OP_EQUAL`, `OP_EQUALVERIFY`, `OP_NOTIF`, `OP_CHECKLOCKTIMEVERIFY`, `OP_CHECKMULTISIG`, plus
  the ones copied from `to_local`), the `step_op_exec/skip/cond`, `step_push_exec/skip`,
  `numInstr_exec/skip` lemmas copied verbatim from `Sol_BitcoinToLocal_all.lean`, and three new
  `run_*_skip` lemmas on explicit state literals that fold a skipped instruction into one rewrite.
- `cms_two`: `OP_CHECKMULTISIG` on `2 k1 k2 2 r` in closed form (two keys, then `r` must start with
  two signatures and a dummy), derived from the `rfl` equation `execOp_cms`.
- The walk is modular: one lemma per branch over the *explicit tail* of the script
  (`offered_tailA` revocation, `offered_tailB1` timeout, `offered_tailB2` preimage, `offered_tailB`
  joining the last two after `OP_SIZE 32 OP_EQUAL OP_NOTIF`; likewise `received_tail*`), each
  stated as `(run f o ⟨stack, [], vfExec, k⟩ tail).map State.stack = closed form` with a general
  op count `k`, then `offered_eval` / `received_eval` run the common prefix
  `OP_DUP OP_HASH160 <revHash> OP_EQUAL OP_IF` and rewrite with the branch lemma. The closed forms
  use two private helper functions (`sigResult`, `msResult`) instead of `match` expressions so that
  the statements do not capture the stack-length hypothesis.
- Stack-size bookkeeping: the main lemmas assume `rest.length + 3 ≤ MAX_STACK_SIZE` (the stack
  never exceeds `n + 2` before the inner branch) and carry the one remaining `MAX_STACK_SIZE <
  rest.length + 4` guard (the push of `32` at depth `n + 3`) inside the closed form; larger stacks
  are handled by `*_eval_large` (the script fails at `OP_DUP` or at the push of `revHash`).
- `*_spends_iff` then case-splits the closed form; `sigResult_one` / `msResult_one` extract the
  witness shape from "exactly one element left, and it true".
- Parsing and `p2wsh_spend` follow the `to_local` proofs step for step (26 and 29
  `parseScriptAux_step` rewrites; `offeredBytes_length`/`receivedBytes_length ≤ MAX_SCRIPT_SIZE`).

## Checks

- `lake build Solutions.Sol_BitcoinHtlc_all`: succeeds; the only `sorry` warnings are the
  pre-existing `Thm_BitcoinScript_serialize_roundtrip` and `Thm_BitcoinVerify_p2wsh_correct`
  stubs the mission imports (as `to_local` does).
- `pipeline.py stubs BitcoinHtlc …`: 16 stubs, build errors 0. `pipeline.py split …`: every split
  file `errors=0`.
- `tests/HtlcVectors.lean`: `decide +kernel` on a stub oracle for the five BOLT #3 witnesses,
  swapped signatures, non-empty dummies with and without `NULLDUMMY`, a wrong 32-byte element,
  expiry accepted/rejected/negative, the CLTV flag off, wrong stack shapes, the byte forms
  (`0x52`, `01 20`, `02 f4 01`) and their parse, and explicit witnesses of the spend predicates.

## Honest limits

- The hashes are parameters, not `hash160` of anything; nothing relates `revHash` to a key.
- The oracle is abstract in `spends_iff`; `p2wsh_spend` instantiates it with `legacyOracle` but
  the signature checks remain `checkSigPreTapscript … = some true`, not statements about ECDSA.
- `cltv_concrete` needs `0 ≤ expiry` (for a negative operand `OP_CHECKLOCKTIMEVERIFY` fails while
  `CheckLockTime` alone could pass); `checkLockTime_iff` covers block-height expiries only.
- The `*_eval` closed forms are private; the public interface is `spends_iff`, the six BOLT-shape
  equations and `p2wsh_spend`.
- The 520-byte bounds on `revHash`, `remoteKey`, `localKey`, `payHash` are hypotheses (a push
  above `MAX_SCRIPT_ELEMENT_SIZE` fails the script even when skipped); the oracle's `hash160`
  output is unconstrained, as the interpreter does not size-check opcode results.
- Anchor-output variants (`OP_1 OP_CHECKSEQUENCEVERIFY OP_DROP` suffix) are not modeled.
