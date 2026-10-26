We prove that off a retarget boundary — when $h + 1 \not\equiv 0 \pmod{2016}$ — `GetNextWorkRequired` returns the last word unchanged, and that `PermittedDifficultyTransition` accepts an unchanged word at that height.

On mainnet minimum-difficulty blocks are disabled, so the first function's non-boundary branch returns `pindexLast->nBits`; the transcription is the same `if`. The second function's non-boundary branch requires `old_nbits == new_nbits`, which holds for equal words. Both are direct from the definitions.
