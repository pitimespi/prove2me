We prove that a successful `checkTxInputs` returns exactly $f = \mathrm{valueIn}(U, I) - \mathrm{valueOut}(tx)$ with $0 \le f \le \mathrm{MAX\_MONEY}$ and every input present, where $I$ is the input list.

**Idea.** The function first runs the input loop, which threads an accumulator through the inputs; then it compares the accumulated `nValueIn` with the output total, subtracts, and tests the result with `MoneyRange`. The proof characterizes the loop and then reads the identity and the range off the final tests.

**Step 1 (the input loop).** By induction on $I$: if the loop started at $a$ returns $v$, then $v = a + \mathrm{valueIn}(U, I)$ and every input is present. At each step the coin is looked up (failure if absent), and the accumulator advances by its value; `valueIn` is defined by the same recursion with the looked-up coin.

**Step 2.** With $a = 0$, `nValueIn` $= \mathrm{valueIn}(U, I)$. The function then rejects if `nValueIn` $<$ `valueOut` and otherwise forms the difference; the final `MoneyRange` test, read back as a proposition, is $0 \le f \le \mathrm{MAX\_MONEY}$.
