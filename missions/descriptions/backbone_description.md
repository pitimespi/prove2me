## The claim

"Bitcoin is secure as long as honest miners hold the majority of the hashrate" is the informal reading of Garay, Kiayias and Leonardos's backbone analysis: in a synchronous network, if the adversary finds fewer blocks than there are uniquely successful honest rounds over every long enough window, then honest chains grow (chain growth), agree on all but their last blocks (common prefix), and contain honest blocks regularly (chain quality). This mission states the synchronous model and proves these three properties from that combinatorial hypothesis.

## What is proved

- **The model**: executions with honest parties, a rushing adversary, `maxvalid` adoption, and valid chains in which every block sits on exactly the chain its creator extended (the hash-chain abstraction).
- **Chain growth** (`chain_growth`, `chain_growth_self`): between rounds $r$ and $s$ every honest chain grows by at least the number of successful rounds in between.
- **Common prefix** (`uniquely_successful_height`, `common_prefix_private`, `common_prefix_rounds`, `common_prefix`, the goal): a uniquely successful round pins the honest block at its height; a private fork that stays adversarial for a window loses; hence the chains of any two honest parties agree once the last $2λ$ blocks are dropped.
- **Chain quality** (`chain_quality`): any $λ$ consecutive blocks of an honest chain contain an honest block.
- **The bridge to Core** (`chainWork_const_bits`): at constant difficulty the block mission's `chainWork` is the block count times one block's proof, so "longest" and "most work" coincide in this regime.

## What this rests on and what it does not say

Nothing probabilistic is proved: `Typical` (adversarial blocks in every window of length $≥ λ$ strictly fewer than the uniquely successful rounds strictly inside it) is assumed, where the paper derives it from Chernoff bounds and honest majority. The constants are $k = 2λ$ and $ℓ = λ$ rather than the paper's $2λf$; only the weak form of chain quality is proved. The model is synchronous with one honest block per party per round, no explicit message layer, and static difficulty. ([ePrint 2014/765](https://eprint.iacr.org/2014/765))
