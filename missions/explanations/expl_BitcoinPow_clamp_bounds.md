We prove that the clamped timespan lies in $[T/4, 4T]$ for every signed input $a$, with $T = 1{,}209{,}600$.

The clamp is two comparisons: if $a < T/4$ the result is $T/4$; otherwise if $4T < a$ the result is $4T$; otherwise it is $a$ itself, which then satisfies $T/4 \le a \le 4T$. In each of the three cases both bounds hold. Negative inputs, which occur when timestamps decrease, fall in the first case.
