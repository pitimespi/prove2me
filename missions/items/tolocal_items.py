SRC = ("BOLT #3, Bitcoin Transaction and Script Formats, 'to_local Output': https://github.com/lightning/bolts/blob/master/03-transactions.md#to_local-output; "
       "Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (OP_IF/OP_ELSE/OP_ENDIF, OP_CHECKSEQUENCEVERIFY, OP_CHECKSIG), "
       "GenericTransactionSignatureChecker::CheckSequence, ExecuteWitnessScript, VerifyWitnessProgram (src/script/interpreter.cpp: "
       "https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); CScript::operator<<(int64_t) (script/script.h); BIP68, BIP112, BIP141")
TAGS = ["bitcoin", "lightning", "bolt3", "script", "csv", "bip112", "p2wsh", "formal-verification", "bitcoin-mainnet"]

DEFINITION = {
    "definition_name": "BitcoinToLocal",
    "definition_title": "The Lightning to_local witness script and its two spending conditions",
    "natural_language_statement": r"""Names over the script, signature and verification missions; nothing of Core is re-transcribed.

**`numInstr n`** / **`numBytes n`** — what `CScript::operator<<(int64_t)` emits for a small integer: `OP_1NEGATE` for $-1$, `OP_1` … `OP_16` for $1$ … $16$, and the `CScriptNum` push otherwise (the empty push for $0$), as an instruction and as bytes.

**`toLocalScript rev delay dpk`** — the BOLT #3 `to_local` witness script `OP_IF <rev> OP_ELSE <delay> OP_CHECKSEQUENCEVERIFY OP_DROP <dpk> OP_ENDIF OP_CHECKSIG`, parsed; **`toLocalBytes rev delay dpk`** — the same as `CScript` serializes it.

**`CsvPasses f o delay`** — what `OP_CHECKSEQUENCEVERIFY` lets through for the operand `delay` under flags $f$ and oracle $o$: the `CHECKSEQUENCEVERIFY` flag is off, or `delay` is non-negative and either carries the disable bit (bit 31) or satisfies the oracle's `checkSequence`.

**`SpendCondition f o rev delay dpk b sig`** — the revocation path ($b$ true and `o.checkSig sig rev = some true`) or the delayed path ($b$ false, `CsvPasses f o delay`, and `o.checkSig sig dpk = some true`), for the witness stack `[b, sig]` (top first).

**`inputSequence tx nIn`** — the `nSequence` of input `nIn` of a transaction (an empty input when out of range).

**Formalization Note.** `Flags`, `Oracle`, `evalScript`, `serialize`, `castToBool` are the script mission's; `legacyOracle`, `checkSequence`, `parseScript`, `pushBytes` the signature mission's; `verifyScript`, `executeWitnessScriptV0`, `topTrue`, `witnessBytes` the verification mission's. Only `Std` is imported. `MINIMALIF` is a policy flag and is off, so any true value selects the revocation branch under consensus.""",
}

THEOREMS = {
"BitcoinToLocal.serialize_length": dict(title="A script number below 2^(8k) in magnitude serializes to at most k + 1 bytes",
    nl=r"""For an integer $n$ and $k$ with $|n| < 256^k$: `(serialize n).length ≤ k + 1`. In particular a delay below $2^{32}$ fits the 5-byte limit of `OP_CHECKSEQUENCEVERIFY`.""", ms=None),
"BitcoinToLocal.csv_step": dict(title="OP_CHECKSEQUENCEVERIFY on a serialized number passes exactly when CsvPasses holds",
    nl=r"""For a state whose stack top is `serialize delay` with $|{\rm delay}| < 2^{32}$: `execOp f o true OP_CHECKSEQUENCEVERIFY s = if CsvPasses f o delay then some s else none`.""", ms=None),
"BitcoinToLocal.eval_cons": dict(title="The script on a stack b :: tl: it needs exactly one more element, and leaves the chosen signature check",
    nl=r"""For keys of at most 520 bytes, $|{\rm delay}| < 2^{32}$ and `tl.length + 1 ≤ 1000`: `evalScript f o (b :: tl) (toLocalScript rev delay dpk)` is `none` when `tl` is empty, and for `tl = sig :: rest` it is `(o.checkSig sig rev).map (fun ok => boolBytes ok :: rest)` when `castToBool b`, else `(o.checkSig sig dpk).map (…)` when `CsvPasses f o delay`, else `none`. The whole interpreter run, instruction by instruction, with the skipped branch's pushes and opcodes accounted for.""",
    ms=("Symbolic execution of the script", "Both branches of `OP_IF` walked through `run`/`step`, with the non-executing branch's instructions shown to leave the stack unchanged.")),
"BitcoinToLocal.spends_iff": dict(title="The two spending conditions, for any witness stack",
    nl=r"""For keys of at most 520 bytes and $|{\rm delay}| < 2^{32}$, and any stack `st`: there is a result of `evalScript f o st (toLocalScript rev delay dpk)` with exactly one element that is true, if and only if `st = [b, sig]` for some $b$, `sig` with `SpendCondition f o rev delay dpk b sig`. Stacks of any other shape fail: empty, one element, more than two (the extra elements remain below the result), or beyond the 1000-element limit.""",
    ms=("Soundness and completeness", "`eval_cons` for admissible stacks, and the empty and oversized stacks shown to fail outright.")),
"BitcoinToLocal.parseScript_toLocal": dict(title="The byte form parses to the instruction form",
    nl=r"""For keys of at most 520 bytes and $|{\rm delay}| < 2^{32}$: `parseScript (toLocalBytes rev delay dpk) = some (toLocalScript rev delay dpk)`, through `GetOp` on the canonical pushes and `CScript`'s small-integer encoding.""", ms=None),
"BitcoinToLocal.p2wsh_spend": dict(title="The to_local output under VerifyScript: a witness spends it iff it is a signature, a selector and the script, and the selected branch holds",
    nl=r"""For a context with the `WITNESS` flag, keys of at most 520 bytes, $|{\rm delay}| < 2^{32}$ and any witness `ws`: `verifyScript tap c [] (witnessBytes 0 (sha256 (toLocalBytes rev delay dpk))) (ws ++ [toLocalBytes rev delay dpk]) = true` if and only if `castToBool (sha256 (toLocalBytes rev delay dpk)) = true` and there are $b$, `sig` with `ws = [sig, b]`, both of at most 520 bytes, and `SpendCondition` for the flags of $c$ and the signature mission's `legacyOracle` of $c$'s transaction, input, amount and `SigVersion::WITNESS_V0` on the script. So the output is spent only by the revocation key, or by the delayed key after the sequence check; the first conjunct is `VerifyScript`'s requirement that the program be a true value.""",
    ms=None),
"BitcoinToLocal.csv_concrete": dict(title="With CSV active and a 16-bit delay, the operand check is the transaction's CheckSequence",
    nl=r"""For `f.csv = true` and $0 \le {\rm delay} < 2^{16}$: `CsvPasses f (legacyOracle sf tx nIn amount v sc) delay ↔ checkSequence tx nIn delay = true`. A 16-bit delay carries no disable bit.""", ms=None),
"BitcoinToLocal.checkSequence_iff": dict(title="CheckSequence for a 16-bit delay, in terms of the input's nSequence",
    nl=r"""For $0 \le {\rm delay} < 2^{16}$: `checkSequence tx nIn delay = true` iff the transaction version is at least 2, the input's `nSequence` has no disable bit, its masked value (type flag and low 16 bits) is below the type flag (block-based), and the delay is at most that masked value. `BIP68`/`BIP112` as `GenericTransactionSignatureChecker::CheckSequence` implements them, specialised to a block-count delay.""", ms=None),
"BitcoinToLocal.lightning_delay": dict(title="A commitment spend with nSequence = to_self_delay: the delayed path opens iff version ≥ 2 and nSequence ≥ delay",
    nl=r"""For $0 \le {\rm delay} < 2^{16}$ and an input whose `nSequence` is below $2^{16}$ (no flags, as Lightning sets it): `checkSequence tx nIn delay = true ↔ 2 ≤ tx.version ∧ delay ≤ inputSequence tx nIn`. Together with `p2wsh_spend` and `csv_concrete`: the local node's delayed spend is accepted exactly when its transaction is version 2 or later, sets the input's `nSequence` to at least `to_self_delay`, and carries a valid signature for the delayed key.""",
    ms=None),
}
ORDER = ["BitcoinToLocal.serialize_length", "BitcoinToLocal.csv_step", "BitcoinToLocal.eval_cons", "BitcoinToLocal.spends_iff",
         "BitcoinToLocal.parseScript_toLocal", "BitcoinToLocal.p2wsh_spend", "BitcoinToLocal.csv_concrete",
         "BitcoinToLocal.checkSequence_iff", "BitcoinToLocal.lightning_delay"]
