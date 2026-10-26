# prove2me — Bitcoin consensus rules in Lean 4

Formal verification of Bitcoin Core's mainnet consensus rules, pinned at revision
`a773e1e33b349dc819b5a0edc1c7a4839dc73b48`, developed as missions on [Prove2me](https://prove2.me).

Lean toolchain: `leanprover/lean4:v4.33.1` (Prove2me environment `0df444a3…`). No Mathlib: every
definition imports only `Std`.

## Layout

- `Definitions/Def_*.lean` — source-linked transcriptions of the consensus functions (one file per mission).
- `Theorems/Thm_*.lean` — theorem statements as published on the platform (`:= by sorry` stubs mirroring the server's modules).
- `Solutions/Sol_<theorem>.lean` — accepted proofs, one per theorem, each a top-level `theorem solution`.
  `Sol_*_all.lean` are the development files from which the per-theorem files are split.
- `missions/` — mission descriptions, prose statements (`items/*.py`), proof explanations as submitted, and the blind
  read-backs attached to the Script proposal (`readbacks/script/`), written by an independent agent from the Lean code alone.
- `tools/pipeline.py` — stubs / split / audit staging / proposal / submission helper used for each mission.
- `tests/TaprootVectors.lean` — BIP341 wallet test vectors (script trees, tweaks, control blocks, key-path sighashes).
- `tests/SigVectors.lean`, `tests/VerifyVectors.lean` — signature-layer and VerifyScript vectors (BIP340, BIP143, generated ECDSA).
- `tests/SerVectors.lean` — hash test vectors and genesis checks.
- `tests/ScriptVectors.lean` — `#eval` sanity vectors for the Script interpreter (run with `lake env lean tests/ScriptVectors.lean`).
- `STATUS.md` — mission inventory, proposal IDs, and what remains open.

## Build

```
lake build Definitions.Def_BitcoinPow Solutions.Sol_BitcoinPow_nextWork_permitted
```

The `Theorems/` stubs carry `sorry` by design: on the server each resolves to the published,
proved theorem; locally they let the reduction proofs type-check.

## Missions

| Mission | Goal theorem | Theorems |
|---|---|---|
| BIP68 relative lock-time | `BitcoinBIP68.core_correct` | 5 |
| Block subsidy and the 21M bound | `BitcoinSubsidy.issuance_bound` | 8 |
| Proof of work: compact targets and retargeting | `BitcoinPow.nextWork_permitted` | 10 |
| Merkle root and CVE-2012-2459 | `BitcoinMerkle.dup_block` | 9 |
| UTXO accounting and the ledger supply bound | `BitcoinUtxo.ledger_bound` | 10 |
| Headers: median time past and contextual rules | `BitcoinHeader.mtp_mono_chain` | 9 |
| Soft-fork activation: script flags by height | `BitcoinActivation.flags_mono` | 10 |
| Script: CScriptNum, the legacy interpreter, and P2PKH | `BitcoinScript.p2pkh_correct` | 10 |
| Serialization, SHA-256d, weights, genesis block | `BitcoinSer.block_roundtrip` | 17 |
| Signatures: DER, sighash, ECDSA/Schnorr, concrete P2PKH | `BitcoinSig.derEncode_complete` | 14 |
| VerifyScript: P2SH, SegWit v0, witness dispatch | `BitcoinVerify.p2wpkh_correct` | 11 |
| Taproot: key path, script path, Tapscript | `BitcoinTaproot.keypath_correct` | 15 |

All 71 theorems are proved on the platform. See `STATUS.md` for the open areas.
