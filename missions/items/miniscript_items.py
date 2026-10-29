SRC = ("Miniscript reference (P. Wuille, A. Poelstra, S. Kanjalkar): translation table, type system and correctness/malleability properties, "
       "https://bitcoin.sipa.be/miniscript/; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: src/script/miniscript.h, src/script/miniscript.cpp "
       "(https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/miniscript.h); EvalScript (src/script/interpreter.cpp)")
TAGS = ["bitcoin", "miniscript", "script", "compiler-correctness", "type-system", "policy", "formal-verification", "bitcoin-mainnet"]

DEFINITION = {
    "definition_name": "BitcoinMiniscript",
    "definition_title": "Miniscript fragments, their translation to Script, the type system, and a satisfaction semantics",
    "natural_language_statement": r"""A Miniscript core over the script mission's interpreter.

**`Ms`** — 23 fragments: `pk_k`, `pk_h`, `older`, `after`, `sha256`, `hash256`, `ripemd160`, `hash160`, `and_v`, `and_b`, `or_b`, `or_c`, `or_d`, `or_i`, `andor`, `multi`, and the wrappers `a:`, `s:`, `c:`, `d:`, `v:`, `j:`, `n:`. **`compile`** — the reference's translation table into the script mission's instruction lists (numbers through `CScript << int64`; `v:` appends an explicit `OP_VERIFY`, the reference's folding into a preceding `*VERIFY` opcode is not modelled). **`size`**, **`opsMax`** — the instruction count and an upper bound on counted opcodes.

**`Ty`** — the basic types `B`, `V`, `K`, `W`; **`Props`**, **`props`** — the modifiers `z`, `o`, `n`, `d`, `u` computed by the reference's table; **`HasType`** — the typing rules (with size bounds on pushed data, `1 ≤ n < 2^31` for time locks, `1 ≤ k ≤ |keys| ≤ 20` for `multi`); **`typeOf`** — a decidable type checker.

**`Sem f o m w out`** — the witness `w` (top first) drives `m` to the output `out` left above the untouched stack: `[v]` for `B`/`W` (nonzero for a satisfaction, empty for a dissatisfaction), `[]` for `V`, `[key, sig]` for `K`. It follows the reference's satisfaction and dissatisfaction tables and includes the non-canonical combinations the script also accepts. **`Sat`**, **`Dsat`**, **`SatV`** — satisfaction (a true output), dissatisfaction (the empty output), and `V` satisfaction (no output). **`GoodVal v`** — `v` is the script number of some $0 \le n < 2^{31}$. **`runSeq`** — the interpreter's instruction loop without the final unbalanced-conditional check, so that it composes.

**Formalization Note.** `numInstr`, `CsvPasses` are the `to_local` mission's; `CltvPasses` the HTLC mission's; the interpreter, `Oracle` and `Flags` the script mission's. Only `Std` is imported.""",
}

T = {}
T["runSeq_append"] = ("Sequential execution composes", r"""`runSeq f o s (a ++ b)` runs `a`, then `b` from the result (or fails if `a` fails).""")
T["run_eq_runSeq"] = ("The interpreter's loop is runSeq followed by the balance check", r"""`run f o s sc` is `runSeq f o s sc` followed by the test that the condition stack is empty.""")
T["evalScript_eq_runSeq"] = ("evalScript through runSeq", r"""`evalScript f o st sc` is the stack of `runSeq` from the initial state when the condition stack ends empty, `none` otherwise.""")
T["sem_consumes"] = ("The z and o modifiers are respected", r"""If `Sem f o m w out` then `props m`'s `z` forces `w = []` and its `o` forces `w` to have one element.""")
T["compile_skip"] = ("A typed fragment in a non-executing branch is skipped", r"""For a well-typed fragment and a state whose condition stack is not all true, with room for its operations: `runSeq` over `compile m` leaves the stacks and condition stack unchanged and adds at most `opsMax m` to the operation count.""")
T["goodVal_of_sem"] = ("B fragments leave a valid script number", r"""For `m : B`, `Sem f o m w [v]` implies `GoodVal v`.""")
T["goodVal_of_semW"] = ("W fragments leave a valid script number", r"""As `goodVal_of_sem` for `m : W`.""")
T["sem_V_nil"] = ("V fragments leave nothing", r"""For `m : V`, `Sem f o m w out` implies `out = []`.""")
T["sem_K_shape"] = ("K fragments leave a key and a signature", r"""For `m : K`, `Sem f o m w out` implies `out = [key, sig]` for some `key`, `sig`.""")
T["sem_sound"] = ("Compiler soundness for B, V and K: the script leaves exactly the semantic output", r"""For a well-typed `m` of type other than `W`, with operation and stack bounds: `Sem f o m w out` implies `evalScript f o (w ++ rest) (compile m) = some (out ++ rest)`. The stack below the witness is untouched.""")
T["semW_sound"] = ("Compiler soundness for W: the output lands next to the top element", r"""For `m : W` and `Sem f o m w [v]`: running `compile m` on `x :: (w ++ rest)` leaves `v :: x :: rest` or `x :: v :: rest` (the `a:` and `s:` wrappers' two placements).""")
T["sat_sound"] = ("A satisfaction makes the compiled script leave a true value", r"""For `m : B` and `Sat f o m w`, with bounds: some `v` with `castToBool v = true` and `evalScript f o (w ++ rest) (compile m) = some (v :: rest)`.""")
T["dsat_sound"] = ("A dissatisfaction makes the compiled script leave the empty element", r"""For `m : B` and `Dsat f o m w`, with bounds: `evalScript f o (w ++ rest) (compile m) = some ([] :: rest)`.""")
T["satV_sound"] = ("A V satisfaction leaves the stack below untouched", r"""For `m : V` and `SatV f o m w`, with bounds: `evalScript f o (w ++ rest) (compile m) = some rest`.""")
T["sat_spends"] = ("A satisfaction spends: one true element is left", r"""For `m : B` and `Sat f o m w` with bounds: `evalScript f o w (compile m)` leaves exactly one element, and it is true. This is the success condition of witness-v0 and tapscript execution.""")
T["compile_length"] = ("The compiled script has size m instructions", r"""`(compile m).length = size m`.""")
T["opsIn_compile_le"] = ("The counted opcodes are bounded by opsMax", r"""`opsIn (compile m) ≤ opsMax m`.""")
T["typeOf_sound"] = ("The type checker is sound", r"""`typeOf m = some ty` implies `HasType m ty`.""")
THEOREMS = {f"BitcoinMiniscript.{k}": dict(title=v[0], nl=v[1], ms=None) for k, v in T.items()}
THEOREMS["BitcoinMiniscript.sem_sound"]["ms"] = ("Compiler soundness", "Structural induction on `HasType`, with `runSeq_append` for sequencing and `compile_skip` for unexecuted branches.")
ORDER = ["BitcoinMiniscript." + k for k in ["runSeq_append", "run_eq_runSeq", "evalScript_eq_runSeq", "sem_consumes", "compile_skip",
  "goodVal_of_sem", "goodVal_of_semW", "sem_V_nil", "sem_K_shape", "sem_sound", "semW_sound", "sat_sound", "dsat_sound", "satV_sound",
  "sat_spends", "compile_length", "opsIn_compile_le", "typeOf_sound"]]
