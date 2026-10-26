The same induction as `parseScript_pushes` on `isPushOnlyAux`: each `getOp` yields a `push` instruction, which the predicate accepts, and the fuel bound is the number of pushes.
