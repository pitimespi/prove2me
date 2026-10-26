# Read-back: `BitcoinScript.p2pk_correct`

**Binders and hypothesis.** Universally quantified: $f$, a flags record (`cltv`, `csv`, `nulldummy`, all arbitrary); $o$, an oracle (five arbitrary hash functions, a `checkSig` function from (signature, public key) byte lists to an optional Boolean, and two integer predicates); $\mathit{sig}$ and $\mathit{pubkey}$, byte lists. Two hypotheses:

- $\mathit{hsig}$: $|\mathit{sig}| \le 520$;
- $\mathit{hpk}$: $|\mathit{pubkey}| \le 520$.

Neither hypothesis says anything else about the contents of $\mathit{sig}$ or $\mathit{pubkey}$; both may be empty.

**Conclusion.** A biconditional:
$$\mathrm{verifyScriptPlain}\big(f, o, [\mathrm{push}(\mathit{sig})], \mathrm{p2pkScript}(\mathit{pubkey})\big) = \text{true}\quad\Longleftrightarrow\quad o.\mathrm{checkSig}(\mathit{sig}, \mathit{pubkey}) = \mathrm{some}(\text{true}).$$

**Unfolding the scripts.** $\mathrm{p2pkScript}(\mathit{pubkey}) = [\mathrm{push}(\mathit{pubkey}),\ \mathrm{op}(\mathrm{OP\_CHECKSIG})]$ with $\mathrm{OP\_CHECKSIG} = \mathtt{0xac}$. The first script (the "scriptSig") is the single push of $\mathit{sig}$.

**Unfolding `verifyScriptPlain`.** First, $\mathrm{evalScript}(f,o,[],[\mathrm{push}(\mathit{sig})])$ is computed: from the empty stack with empty condition stack, the push step checks $520 < |\mathit{sig}|$ (excluded by $\mathit{hsig}$), pushes, and checks the stack size ($1 \le 1000$); the result is $\mathrm{some}([\mathit{sig}])$. If this had been none, the verification result would be false. Second, $\mathrm{evalScript}(f,o,[\mathit{sig}],\mathrm{p2pkScript}(\mathit{pubkey}))$ is computed from the fresh state $\langle [\mathit{sig}], [], [], 0\rangle$:
- $\mathrm{push}(\mathit{pubkey})$: size check passes by $\mathit{hpk}$; stack becomes $[\mathit{pubkey}, \mathit{sig}]$ (public key on top); size $2 \le 1000$.
- $\mathrm{op}(\mathtt{0xac})$: it is counted ($\mathtt{0xac} > \mathtt{0x60}$), $201 < 0 + 1$ is false, count becomes $1$; it is not disabled; the branch is executing ($\mathrm{allTrue}([]) = \text{true}$); `execOp`'s CHECKSIG branch matches the stack $\mathit{pubkey} :: \mathit{sig} :: []$ and evaluates $o.\mathrm{checkSig}(\mathit{sig}, \mathit{pubkey})$. If that is none, the step fails and verification is false. If it is $\mathrm{some}(\mathit{ok})$, the stack becomes $[\mathrm{boolBytes}(\mathit{ok})]$, i.e. $[[\mathtt{0x01}]]$ when $\mathit{ok}$ is true and $[[]]$ when false; the size check passes.
- End of script: the condition stack is empty, so the run succeeds with stack $[\mathrm{boolBytes}(\mathit{ok})]$.
Finally `verifyScriptPlain` returns $\mathrm{castToBool}$ of the top element: $\mathrm{castToBool}([\mathtt{0x01}]) = \text{true}$ and $\mathrm{castToBool}([]) = \text{false}$.

**The claim, in words.** Under the two length hypotheses, the plain verification of "push $\mathit{sig}$" against "push $\mathit{pubkey}$; CHECKSIG" is true exactly when the oracle's signature check on $(\mathit{sig}, \mathit{pubkey})$ returns $\mathrm{some}(\text{true})$. Both directions: if the oracle answers $\mathrm{some}(\text{true})$ the verification is true; if the oracle answers $\mathrm{some}(\text{false})$ or none, the verification is false. The flags $f$ never enter the computation; all three flag settings give the same answer.

**What is not said.** The theorem does not interpret `checkSig`: it does not say the oracle performs ECDSA verification, hashes any transaction, or depends on a script code; whatever function the oracle holds, the statement relates verification to that function's output on exactly the pair $(\mathit{sig}, \mathit{pubkey})$ in that order. It says nothing when $|\mathit{sig}| > 520$ or $|\mathit{pubkey}| > 520$ (no claim that verification is then false). It does not consider any other scriptSig (e.g. two pushes, or a push followed by opcodes), nor any other scriptPubKey form (P2PKH, multisig, P2SH, witness). It does not say what the final stack is, only the Boolean result. It does not involve the `nulldummy`, `cltv` or `csv` flags, the hash oracle functions, or `opCount` beyond the implicit fact that one counted opcode does not exceed the limit. It does not assert uniqueness of the satisfying signature or anything about the relationship between $\mathit{sig}$ and $\mathit{pubkey}$.
