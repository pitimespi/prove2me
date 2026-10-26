We prove $\mathrm{setVch}(\mathrm{serialize}(n)) = n$ for every integer $n$.

For $n = 0$ the serializer emits `[]` and `setVch [] = 0` by definition. Otherwise let $m = |n|$ and write the magnitude bytes as `natBytes m`, which is non-empty (`natBytes_ne_nil`) and whose little-endian value is $m$ (`leNat_natBytes`, by strong induction with `Nat.div_lt_self`). Split `natBytes m = L ++ [b]` (`concat_of_ne_nil`) and read the three branches of `serialize` through the lemmas `leNat_append`, `topBit_append`, `clearTop_append`, `setTop_append`, which describe the reader on a list with its last byte exposed.

*Top bit of $b$ already set* ($128 \le b$): a sign byte `0x80` or `0x00` is appended. The reader sees top bit $= 1$ or $0$ on that byte, `clearTop` turns it into `0x00`, and `leNat (L ++ [b] ++ [0]) = m`; so the result is $-m$ or $m$ as required. The bit facts are `and7f_toNat` ($(b \,\&\, \mathtt{7f}).\mathrm{toNat} = b.\mathrm{toNat} \bmod 128$) and `topbit_iff` ($(b \,\&\, \mathtt{80}) \ne 0 \iff 128 \le b$), proved through `BitVec.toNat_and` and `Nat.and_two_pow_sub_one_eq_mod` / `Nat.and_div_two_pow`.

*Top bit clear, $n < 0$*: `setTop` replaces $b$ by $b \,|\, \mathtt{80}$, whose value is $b + 128$ (`or80_toNat`); the reader sees the top bit, clears it back to $b$ (`and7f_toNat` with $b < 128$) and returns $-\mathrm{leNat}(L ++ [b]) = -m = n$.

*Top bit clear, $n > 0$*: nothing is changed, the reader sees no top bit and returns $m = n$.

The final step `Int.natAbs` versus the sign is discharged by `omega` after `Int.natAbs_of_nonneg` / `Int.ofNat_natAbs_of_nonpos`.
