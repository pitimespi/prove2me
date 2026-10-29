## The claim

Miniscript is the structured subset of Bitcoin Script that wallets use to write and analyse spending policies: each fragment has a fixed translation to Script, a type that says what it does to the stack, and a satisfaction table that says which witnesses make it succeed. The claim that makes it trustworthy is compiler correctness: a well-typed Miniscript compiles to a script that the consensus interpreter accepts on exactly the witnesses the satisfaction table describes. This mission proves the soundness half of that claim against the script interpreter transcribed from Bitcoin Core.

## What is proved

- **Sequential execution** (`runSeq_append`, `run_eq_runSeq`, `evalScript_eq_runSeq`, `compile_skip`): the interpreter's loop composes, and a well-typed fragment inside a non-executing branch is inert.
- **The type system** (`sem_consumes`, `goodVal_of_sem`, `goodVal_of_semW`, `sem_V_nil`, `sem_K_shape`, `typeOf_sound`): the semantics respects the types and the `z`/`o` modifiers, `B` and `W` fragments leave valid script numbers, and the decidable checker is sound.
- **Compiler soundness** (`sem_sound`, `semW_sound`, `sat_sound`, `dsat_sound`, `satV_sound`, `sat_spends`, the goal): for every well-typed fragment over 23 constructors (all hash and time-lock leaves, `pk_k`, `pk_h`, `multi`, the and/or combinators, the seven wrappers), a satisfying witness makes the compiled script leave a true value above the untouched stack, a dissatisfaction leaves the empty element, a `V` satisfaction leaves nothing; and a satisfaction of a top-level `B` spends.
- **Resources** (`compile_length`, `opsIn_compile_le`): script size and counted opcodes are bounded by syntactic measures, which carry the theorems' operation and stack hypotheses.

## What this rests on and what it does not say

Soundness only: the converse ("nothing else succeeds") and the malleability analysis (the `s`, `f`, `e` properties, non-malleable satisfactions) are not proved. `thresh` is not in the fragment set, and `v:` appends an explicit `OP_VERIFY` instead of folding into a preceding `*VERIFY` opcode, which changes script bytes but not behaviour. The signature checks are the abstract oracle's. ([Miniscript](https://bitcoin.sipa.be/miniscript/), [`miniscript.h`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/miniscript.h))
