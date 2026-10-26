# Read-back: `BitcoinScript.p2pkh_correct`

**Binders and hypothesis.** Universally quantified: $f$, a flags record (three arbitrary Booleans); $o$, an oracle (hash functions `ripemd160`, `sha1`, `sha256`, `hash160`, `hash256` from byte lists to byte lists, `checkSig` from two byte lists to an optional Boolean, and two integer predicates — all arbitrary); and three byte lists $\mathit{sig}$, $\mathit{pubkey}$, $h$. (Here $h$ is a *byte list*, the hash value embedded in the output script, not a hypothesis.) Three hypotheses:

- $\mathit{hsig}$: $|\mathit{sig}| \le 520$;
- $\mathit{hpk}$: $|\mathit{pubkey}| \le 520$;
- $\mathit{hh}$: $|h| \le 520$.

No other constraint: any of the three may be empty, $h$ need not have any particular length such as $20$, and $\mathit{pubkey}$ need not be a well-formed key.

**Conclusion.** A biconditional:
$$\mathrm{verifyScriptPlain}\big(f, o, [\mathrm{push}(\mathit{sig}), \mathrm{push}(\mathit{pubkey})], \mathrm{p2pkhScript}(h)\big) = \text{true}\ \Longleftrightarrow\ \big(o.\mathrm{hash160}(\mathit{pubkey}) = h\ \wedge\ o.\mathrm{checkSig}(\mathit{sig}, \mathit{pubkey}) = \mathrm{some}(\text{true})\big).$$

**Unfolding the scripts.** $\mathrm{p2pkhScript}(h) = [\mathrm{op}(\mathrm{OP\_DUP}), \mathrm{op}(\mathrm{OP\_HASH160}), \mathrm{push}(h), \mathrm{op}(\mathrm{OP\_EQUALVERIFY}), \mathrm{op}(\mathrm{OP\_CHECKSIG})]$ with bytes $\mathtt{0x76}, \mathtt{0xa9}, -, \mathtt{0x88}, \mathtt{0xac}$. The scriptSig is the two pushes, $\mathit{sig}$ first then $\mathit{pubkey}$.

**Unfolding `verifyScriptPlain`, step by step.** First evaluation, from the empty stack: push $\mathit{sig}$ (size check passes by $\mathit{hsig}$), push $\mathit{pubkey}$ (by $\mathit{hpk}$); the condition stack is empty throughout; the result is $\mathrm{some}([\mathit{pubkey}, \mathit{sig}])$ (public key on top). Second evaluation, from the fresh state $\langle [\mathit{pubkey}, \mathit{sig}], [], [], 0\rangle$ with operation count reset to $0$:
1. $\mathrm{OP\_DUP}$ (counted; count $1$): stack $[\mathit{pubkey}, \mathit{pubkey}, \mathit{sig}]$.
2. $\mathrm{OP\_HASH160}$ (count $2$): top replaced by $o.\mathrm{hash160}(\mathit{pubkey})$; stack $[o.\mathrm{hash160}(\mathit{pubkey}), \mathit{pubkey}, \mathit{sig}]$. No size check on the hash output.
3. $\mathrm{push}(h)$: size check by $\mathit{hh}$; stack $[h, o.\mathrm{hash160}(\mathit{pubkey}), \mathit{pubkey}, \mathit{sig}]$ (4 elements $\le 1000$).
4. $\mathrm{OP\_EQUALVERIFY}$ (count $3$): with $a = h$ on top and $b = o.\mathrm{hash160}(\mathit{pubkey})$ second, $\mathit{eq} := (b = a)$, byte-list equality. If $\mathit{eq}$, both are removed, stack $[\mathit{pubkey}, \mathit{sig}]$; otherwise the step fails and verification is false.
5. $\mathrm{OP\_CHECKSIG}$ (count $4$): with $\mathit{pubkey}$ on top and $\mathit{sig}$ second, evaluate $o.\mathrm{checkSig}(\mathit{sig}, \mathit{pubkey})$; none $\Rightarrow$ failure, false; $\mathrm{some}(\mathit{ok}) \Rightarrow$ stack $[\mathrm{boolBytes}(\mathit{ok})]$.
6. End: condition stack empty, success; `verifyScriptPlain` returns $\mathrm{castToBool}(\mathrm{boolBytes}(\mathit{ok}))$, which is $\mathit{ok}$.

**The claim, in words.** Under the three length hypotheses, verification succeeds exactly when both (a) the oracle's `hash160` of $\mathit{pubkey}$ is, as a byte list, equal to $h$, and (b) the oracle's `checkSig` on $(\mathit{sig}, \mathit{pubkey})$ returns $\mathrm{some}(\text{true})$. In the forward direction, a true verification yields both facts; in the backward direction, both facts yield a true verification. Failure of (a) makes verification false regardless of (b); if (a) holds and `checkSig` returns $\mathrm{some}(\text{false})$ or none, verification is false. The flags $f$ play no role.

**What is not said.** Nothing is claimed if any of the three lengths exceeds $520$. The oracle is uninterpreted: the theorem does not say `hash160` is RIPEMD160∘SHA256, that its output has $20$ bytes, or that `checkSig` is ECDSA on a signature hash; it only relates verification to whatever these functions return on the given inputs. There is no claim about the order of evaluation of (a) and (b) beyond what the biconditional expresses (in particular the theorem does not say that `checkSig` is *not* called when the hash mismatches). The scriptSig is fixed to exactly two pushes in the order $\mathit{sig}$, $\mathit{pubkey}$; a scriptSig with extra elements, extra opcodes, or reversed order is not covered. No pay-to-script-hash, witness, CLEANSTACK, push-only, NULLFAIL, or minimal-encoding condition exists in the statement. The final stack contents and the operation count are not described. Nothing is said about whether $h$ determines $\mathit{pubkey}$ uniquely (collisions in the oracle's `hash160` are not excluded and would simply be covered by the "$=$" on the right-hand side).
