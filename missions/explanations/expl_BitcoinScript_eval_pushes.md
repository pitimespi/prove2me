We prove that from the empty stack a push-only script $\langle p_1\rangle \cdots \langle p_n\rangle$ with every $|p_i| \le 520$ and $n \le 1000$ evaluates to the stack $[p_n, \dots, p_1]$.

The auxiliary `run_pushes` generalizes to an arbitrary initial state $\langle st, [], [], k\rangle$ with $|st| + n \le 1000$: by induction on the push list, each `step` on `.push p` passes the element-size test ($|p| \le 520$), pushes since `allTrue [] = true`, and passes the stack-size test because $|p :: st| + 0 \le 1000$ follows from the length hypothesis; the recursive call is on `p :: st` with the remaining pushes, and `List.reverse_cons` / `List.append_assoc` reassemble $\mathrm{reverse}(ps) ++ st$. The empty script returns `some s` because `vfExec = []` is empty.

`eval_pushes` instantiates $st = []$, $k = 0$ and reads off the main stack.
