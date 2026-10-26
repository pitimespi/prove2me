Induction on the width $k$: `leBytes 0 n = []` has length $0$, and `leBytes (k+1) n` is one byte followed by `leBytes k (n/256)`, of length $k$ by the hypothesis.
