# Status report — all open areas formalized

## Proposals awaiting your Submit (Draft, read-backs attached, all theorems proved locally)

| # | Mission | Proposal id | Goal | Theorems |
|---|---|---|---|---|
| 9 | Serialization, CompactSize, SHA-256d/Hash160, weights, genesis | `de803721-663b-4dc5-9b2c-57573424cb33` | `BitcoinSer.block_roundtrip` | 17 |
| 10 | Signatures: DER, sighash, secp256k1 ECDSA/Schnorr, concrete P2PKH | `64726a79-22e3-4530-9da0-f77dd4f58fc9` | `BitcoinSig.derEncode_complete` | 14 |
| 11 | VerifyScript: P2SH, SegWit v0, witness dispatch | `b7297a23-212b-4d31-95ce-c235e82f9037` | `BitcoinVerify.p2wpkh_correct` | 11 |
| 12 | Taproot: key path, script path, Tapscript | `a2e08bc2-73c6-4c97-9d55-9ee2df86fec5` | `BitcoinTaproot.keypath_correct` | 15 |
| 13 | Block validation composed, ApplySpec, DisconnectBlock, umbrella goal (revision 2, `BitcoinBlockV2`; the original `BitcoinBlock` nodes of proposal `e0d2bee0-9471-4c84-91de-f76e81852e33` are deprecated) | `7e2ce9c7-3a82-42ff-9c54-22755fbd7fb1` | `BitcoinBlockV2.acceptance` | 19 |

Submit them in order 9, 10, 11, 12, 13 (each definition imports the earlier ones). After each is published, run
`python3 tools/pipeline.py submit <NS> <proposal>.json <out>.json` from the repo to submit the proofs
(NS = BitcoinSer, BitcoinSig, BitcoinVerify, BitcoinTaproot, BitcoinBlockV2).

## Umbrella `c416e514-a450-41cc-8dd7-bef33d605a8e`
Description updated with components 9–13; the main theorem to select once mission 13 is published is
`BitcoinBlockV2.acceptance` (R(S) ⟹ (C(S,B,t) accepts ⟺ V(S,B,t))), with `BitcoinBlockV2.apply_spec` the
state-transition contract. The 80 existing references are the eight published missions; the published items
of missions 9–13 should be added as references then.

## Repository: github.com/pitimespi/prove2me (main)
Definitions, theorem stubs, per-theorem solutions, prose, explanations, blind read-backs (Taproot; block
mission read-backs to follow), and tests, including `tests/Block170Test.lean` validating real mainnet block
170 end to end.
