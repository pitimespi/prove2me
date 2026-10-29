# BitcoinAnchors: the BOLT #3 `option_anchors` commitment scripts under Core's script interpreter

Files: `Definitions/Def_BitcoinAnchors.lean`, `Solutions/Sol_BitcoinAnchors_all.lean`,
`tests/AnchorsVectors.lean`. Sibling missions (same style, imported public theorems, copied private
lemmas): `BitcoinHtlc` (non-anchor HTLC scripts) and `BitcoinToLocal` (`to_local`, CSV).

## The model

Four scripts, each as a `Script` of the `BitcoinScript` interpreter and as a `CScript` byte string:

- `toRemoteScript remoteKey` / `toRemoteBytes`: `<remote_pubkey> OP_CHECKSIGVERIFY 1 OP_CHECKSEQUENCEVERIFY`
  (4 instructions; `1` is `OP_1 = 0x51`).
- `anchorScript fundingKey` / `anchorBytes`: `<funding_pubkey> OP_CHECKSIG OP_IFDUP OP_NOTIF 16
  OP_CHECKSEQUENCEVERIFY OP_ENDIF` (7 instructions; `16` is `OP_16 = 0x60`).
- `offeredScript revHash remoteKey localKey payHash` / `offeredBytes`: `BitcoinHtlc.offeredScript` with
  `1 OP_CHECKSEQUENCEVERIFY OP_DROP` after the inner `OP_ENDIF`, inside the outer `OP_ELSE` (29 instructions).
- `receivedScript … expiry` / `receivedBytes`: likewise from `BitcoinHtlc.receivedScript` (32 instructions).

`1`, `16`, `2`, `32` and the expiry are `BitcoinToLocal.numInstr` / `numBytes` (`CScript << int64`).
The hashes and keys are arbitrary byte strings. The delay checks reuse `BitcoinToLocal.CsvPasses f o n`
(`f.csv = false ∨ (0 ≤ n ∧ (disable bit set ∨ o.checkSequence n = true))`) and the lock-time check
`BitcoinHtlc.CltvPasses`. Witness stacks are top first (the reverse of BOLT #3's `CScriptWitness`
order); the `*_p2wsh_spend` theorems take `ws` in `CScriptWitness` order and state the condition on
`ws.reverse`.

## The exact spend conditions (derived from the interpreter, checked with `#eval` and `decide +kernel`)

- `ToRemoteSpend f o remoteKey st` := `∃ sig, st = [sig] ∧ o.checkSig sig remoteKey = some true ∧ CsvPasses f o 1`.
  `OP_CHECKSIGVERIFY` fails the script on `none` *and* on `some false` (it never pushes), so the only
  value the script can leave is the pushed `1` (`serialize 1 = [1]`), and the witness must be exactly
  one element.
- `AnchorSpend f o fundingKey st` := `∃ sig, st = [sig] ∧ (o.checkSig sig fundingKey = some true ∨
  (o.checkSig sig fundingKey = some false ∧ CsvPasses f o 16))`.
  * `some true`: `OP_CHECKSIG` pushes `[1]`, `OP_IFDUP` duplicates it, `OP_NOTIF` consumes one copy and
    skips the branch; `[1]` is left (`anchor_holder`).
  * `some false`: `OP_CHECKSIG` pushes `[]`, `OP_IFDUP` does *not* duplicate, `OP_NOTIF` consumes it and
    runs `16 OP_CHECKSEQUENCEVERIFY`; the value left is the operand `16` (`serialize 16 = [16]`,
    `anchor_anyone`). The empty signature `<>` is such a clean false under the concrete checker
    (`BitcoinSig.checkSig_empty`), which is the BOLT "anyone can spend after 16 blocks" path.
  * `none` (an encoding the checker rejects outright, e.g. a non-DER signature under `DERSIG`): the
    script fails, delay or not.
- `OfferedSpend` / `ReceivedSpend`: exactly `BitcoinHtlc.OfferedSpend` / `ReceivedSpend` with
  `CsvPasses f o 1` conjoined to the two non-revocation paths (preimage/timeout, success/timeout).
  The revocation path (`OP_IF` branch) skips the suffix, so it needs no delay. On the other paths the
  suffix runs *after* the path's own checks: a failing signature on the preimage path leaves a clean
  false only if CSV 1 passes; otherwise the script fails (`offered_preimage`, `received_timeout`).

## Public theorems (24, names `BitcoinAnchors.*`)

- `to_remote_spends_iff`, `anchor_spends_iff`, `offered_spends_iff`, `received_spends_iff`: for an
  arbitrary stack `st`, `(∃ res, evalScript f o st script = some res ∧ res.length = 1 ∧ topTrue res = true)
  ↔ …Spend … st`; hypotheses are the 520-byte bounds on the pushed strings and `expiry.natAbs < 2^32`.
- Closed forms on the BOLT witness shapes: `to_remote_eval` (`[sig]` ↦ `if checkSig = some true ∧
  CsvPasses 1 then some [[1]] else none`), `anchor_eval` (`[sig]` ↦ `match checkSig with none ↦ none |
  some true ↦ some [[1]] | some false ↦ if CsvPasses 16 then some [[16]] else none`), `anchor_holder`,
  `anchor_anyone`, `offered_revocation`, `offered_preimage`, `offered_timeout`, `received_revocation`,
  `received_success`, `received_timeout` (each showing the extra `CsvPasses f o 1` condition where it applies).
- `parseScript_toRemote`, `parseScript_anchor`, `parseScript_offered`, `parseScript_received`.
- `to_remote_p2wsh_spend`, `anchor_p2wsh_spend`, `offered_p2wsh_spend`, `received_p2wsh_spend`: via
  `BitcoinVerify.p2wsh_correct`, `verifyScript tap c [] (witnessBytes 0 (sha256 bytes)) (ws ++ [bytes]) = true ↔
  castToBool (sha256 bytes) = true ∧ (∀ e ∈ ws, e.length ≤ 520) ∧ …Spend (scriptFlagsOf c.flags)
  (legacyOracle (sigFlagsOf c.flags) c.tx c.nIn c.amount .witnessV0 bytes) … ws.reverse`.
- `anchor_anyone_concrete`: with `c.flags.witness = true`, `c.flags.csv = true`, the witness
  `[[], anchorBytes fundingKey]` verifies iff `castToBool (sha256 (anchorBytes fundingKey)) = true ∧
  checkSequence c.tx c.nIn 16 = true`. No hypothesis on the key: `sigFlagsOf` has neither `STRICTENC`
  nor `WITNESS_PUBKEYTYPE`, so `checkPubKeyEncoding (sigFlagsOf _) v pk = true` for every `pk`
  (`checkPubKeyEncoding_consensus`), which discharges `checkSig_empty`'s hypothesis.
- `anchor_anyone_delay`: additionally with `inputSequence c.tx c.nIn < 2^16`, the same witness verifies
  iff `castToBool (sha256 …) = true ∧ 2 ≤ c.tx.version ∧ 16 ≤ inputSequence c.tx c.nIn`
  (via `BitcoinToLocal.lightning_delay`).

Imported public theorems (stubs with `sorry` locally): `BitcoinScript.serialize_roundtrip`,
`BitcoinVerify.p2wsh_correct`, `BitcoinToLocal.csv_step`, `csv_concrete`, `lightning_delay`,
`BitcoinHtlc.cltv_step`, `BitcoinSig.checkSig_empty`.

## Proof structure

- Private machinery copied from `Sol_BitcoinHtlc_all.lean` (script numbers, `step_op_exec/skip/cond`,
  `step_push_*`, `execOp_*` by `rfl`, `numInstr_exec/skip`, `run_*_skip`, `cms_two`, `sigResult`,
  `msResult`), plus `execOp_checksigverify` and `execOp_ifdup` (`rfl`) and `serialize_one/16`.
- `to_remote` and anchor: one walk each (`toRemote_run`, `anchor_run`) on `sig :: rest` with
  `rest.length + 2 ≤ MAX_STACK_SIZE` (the push of the key is the deepest point), `*_run_nil` and
  `*_run_large` for the other stacks; `OP_CHECKSEQUENCEVERIFY` is handled by the imported `csv_step`
  (the operand on top is `serialize 1` / `serialize 16`).
- HTLCs: the `BitcoinHtlc` modular walks (`*_tailA`, `*_tailB1`, `*_tailB2`, `*_tailB`, `*_eval`) with
  the three extra instructions: skipped (`run_num_skip`/`run_op_skip` with `vfExec = [false]`) on the
  revocation tail, executed (`numInstr_exec 1`, `csv_step`, `execOp_drop` with `vfExec = [true]` after the
  inner `OP_ENDIF`) on the others. The closed forms gate the branch result with
  `if CsvPasses f o 1 then … else none`; where the walk fails before the CSV the goal
  `none = if _ then none else none` is closed by `ite_self`. Op-count budgets were raised from 20/30 to 25/35.
- `*_spends_iff` case-split the closed forms (`sigResult_one`, `msResult_one`); the `*_p2wsh_spend`
  theorems share one private lemma `executeWitnessScriptV0_iff` (size bound + parse + `spends_iff`).
- Parsing: 4/7/29/32 `parseScriptAux_step` rewrites; `*Bytes_length ≤ MAX_SCRIPT_SIZE` by `omega`.

## Checks

- `lake build Solutions.Sol_BitcoinAnchors_all`: succeeds; the only `sorry` warnings are the seven
  imported stubs listed above.
- `pipeline.py stubs BitcoinAnchors …`: 24 stubs, build errors 0. `pipeline.py split …`: all 24 split
  files `errors=0` (axioms: `propext, Quot.sound` for the four `parseScript_*`; `sorryAx` elsewhere comes
  from the imported stubs only).
- `tests/AnchorsVectors.lean` (`decide +kernel`, stub oracle with a configurable `checkSequence`
  bound): `to_remote` before/after one block, CSV flag off, wrong signature (script failure, not false),
  rejected encoding; anchor by the key holder at once, by `<>` after 16 / before 16 blocks, by a wrong
  but clean signature, by a rejected encoding (fails even after the delay), wrong shapes; the six HTLC
  paths with and without the one-block delay, swapped signatures, dummies, wrong 32-byte element,
  expiry accepted/rejected/negative; the byte forms (`0x51`, `0x60`, suffix `51 b2 75 68`) and their
  parse; explicit witnesses of the four spend predicates.

## Honest limits

- As in `BitcoinHtlc`: the hashes are parameters, the oracle is abstract in `spends_iff`, and under
  `legacyOracle` the signature checks stay `checkSigPreTapscript … = some true`, not ECDSA statements.
- `anchor_anyone_concrete` says `checkSig [] fundingKey = some false` for *any* `fundingKey` because
  `sigFlagsOf` disables the pubkey-encoding checks (consensus flags); under policy flags
  (`WITNESS_PUBKEYTYPE`) an uncompressed key would make the empty-signature path fail, which this
  model does not cover.
- `anchor_anyone_delay` assumes a flag-free `nSequence < 2^16`; `csv_concrete` needs `f.csv = true`
  (without the flag CSV is a NOP and the anchor is spendable by anyone at once, as `anchor_anyone`
  with `CsvPasses` shows).
- The `*_run` / `*_eval` closed forms are private; the public interface is `spends_iff`, the
  witness-shape equations, `parseScript_*`, `*_p2wsh_spend` and the two concrete anchor theorems.
- The 520-byte bounds on pushed strings are hypotheses; the oracle's `hash160` output is unconstrained.
