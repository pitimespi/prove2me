We prove that a script containing a disabled opcode fails from every state.

By induction on the script. The head instruction is either the disabled `.op c` itself or not. If it is, `step` on an opcode first applies the operation-count test (for opcodes above `OP_16`), then tests `isDisabled c`; with `hc : isDisabled c = true` the result is `none` regardless of `vfExec` (the test precedes the execute-or-skip decision), so `run` returns `none`. Otherwise `run` steps the head: if the step fails the result is `none` already; if it yields `s'`, the induction hypothesis applied to `s'` and the tail (which still contains `.op c`) gives `none`.

Nothing about the stack or the condition stack is needed: this is the CVE-2010-5137 rule as implemented — disabled opcodes fail even inside unexecuted branches.
