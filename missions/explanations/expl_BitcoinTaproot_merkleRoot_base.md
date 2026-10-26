Unfold `taprootMerkleRoot` and `controlNodes`; with the length 33 the node count is `(33 - 33) / 32 = 0`, so `controlNodes.go 0 _ = []` and the fold returns the leaf.
