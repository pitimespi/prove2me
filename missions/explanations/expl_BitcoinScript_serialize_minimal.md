We prove $\mathrm{nonMinimal}(\mathrm{serialize}(n)) = \mathtt{false}$ for every integer $n$.

`nonMinimal` matches on the reversed list: it is `false` for `[]`, and for last byte $b$ it is `true` exactly when $b \,\&\, \mathtt{7f} = 0$ and either there is no previous byte or the previous byte $p$ has $p \,\&\, \mathtt{80} = 0$. So it suffices to show that the serializer's last byte has a value bit, or has none but is preceded by a byte with the top bit set.

For $n = 0$ the output is empty. Otherwise `natBytes |n| = L ++ [b]` with $b \ne 0$ (`natBytes_last_ne_zero`: the loop stops exactly when the remaining quotient is zero, so the most significant byte produced is the last nonzero quotient modulo 256, which is nonzero).

*$128 \le b$*: a sign byte `0x80` or `0x00` is appended. Its value bits are zero, but the previous byte is $b$ with the top bit set, so the second conjunct of `nonMinimal` fails (`topbit_iff`).

*$b < 128$, $n<0$*: the last byte becomes $b \,|\, \mathtt{80}$ whose low seven bits are those of $b$ (`and7f_toNat`, `or80_toNat`), nonzero since $0 < b < 128$.

*$b < 128$, $n>0$*: the last byte is $b$ itself, with $b \,\&\, \mathtt{7f} = b \ne 0$.

In every case the `key` lemma — "if the last byte has a nonzero low seven bits, `nonMinimal` is false" — closes the goal, stated once with `List.reverse_append` to expose the last byte.
