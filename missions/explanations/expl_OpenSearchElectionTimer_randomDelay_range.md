Unfold `randomDelay` and `toPositiveLongAtMost`: the delay is `nonNegative (toLong x) % M + 1`. The remainder is below `M` because `M > 0` (`Nat.mod_lt`), and both inequalities follow by `omega`.
