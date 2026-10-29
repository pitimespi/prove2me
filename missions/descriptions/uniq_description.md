## The claim

`ConnectBlock` guards against a block creating coins at an outpoint that already holds some (BIP30) by scanning the UTXO set — except when the BIP34 activation block is an ancestor, until height 1,983,702. The justification, a comment in Core, is that BIP34 forces every coinbase to begin with a push of its height, so no two coinbases are the same transaction, and therefore (barring a hash collision) no two coinbases share a txid; non-coinbase duplicates are impossible without duplicate parents. The height 1,983,702 is where a height push could first coincide with the prefix of some pre-BIP34 coinbase's `scriptSig`, a fact established by scanning the historical chain.

This mission proves the parts of that argument that follow from the rules, and names precisely the two parts that do not.

## What is proved

- Where the scan runs (`scan_freshness`, `scan_runs_late`, `scan_runs_early`): an accepted block's outputs are fresh against the ledger it is connected to; the scan runs at every height from 1,983,702 and, before the BIP34 block can be an ancestor, at every block but the two historical repeats.
- Height pushes are prefix-free (`pushBytes_prefix`, `heightScript_prefix`): `CScript() << nHeight` for one height is never a prefix of the push for another, for heights in the `int` range.
- Post-BIP34 coinbases are distinct (`coinbase_height_prefix`, `coinbases_distinct`, `chain_coinbases_distinct`, the goal): an accepted block at a BIP34-enforced height has its height push as a coinbase prefix, so blocks at different heights have different coinbase `scriptSig`s, and along any chain connected to a reachable post-BIP34 state the coinbase `scriptSig`s are pairwise distinct.

## What is not proved, and why

Two steps of Core's argument are not consequences of the rules. First, distinct transactions may in principle share a txid: that they do not is collision resistance of SHA-256d, an assumption, not a theorem. Second, that no coinbase before BIP34 begins with a height push of some height below 1,983,702 is a property of the actual mainnet chain's bytes; the model quantifies over all chains, including ones where it fails, which is exactly why the scan is re-enabled from that height. Both are stated as the hypotheses they are in the reorganization mission's `FreshChain`. ([`validation.cpp`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp), [BIP30](https://github.com/bitcoin/bips/blob/master/bip-0030.mediawiki), [BIP34](https://github.com/bitcoin/bips/blob/master/bip-0034.mediawiki))
