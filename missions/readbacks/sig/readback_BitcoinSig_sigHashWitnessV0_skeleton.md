# Read-back: `BitcoinSig.sigHashWitnessV0_skeleton`

**Binders and hypothesis.** Universally quantified over a byte string $scriptCode$, two transactions $tx$ and $tx'$, natural numbers $nIn$ and $hashType$ (unbounded), and an integer $amount$ (any integer, including negative). One hypothesis $h$: `sameSkeleton` $tx\,tx'$, i.e.
$$tx'.\text{version} = tx.\text{version},\quad tx'.\text{vout} = tx.\text{vout},\quad tx'.\text{nLockTime} = tx.\text{nLockTime},$$
and the list of pairs $(\text{prevout}, \text{nSequence})$ taken over $tx'.\text{vin}$ equals the same list taken over $tx.\text{vin}$ (so the input counts agree and prevouts and sequence numbers agree position-wise), while scriptSigs and witness stacks are unconstrained.

**Conclusion.**
$$\text{sigHashWitnessV0}\ scriptCode\ tx'\ nIn\ hashType\ amount = \text{sigHashWitnessV0}\ scriptCode\ tx\ nIn\ hashType\ amount .$$

**Unfolding.** With $acp$ := ($hashType \mathbin{\&} 128 \neq 0$), $single$ := ($hashType \mathbin{\&} 31 = 3$), $none$ := ($hashType \mathbin{\&} 31 = 2$) and $zero$ := 32 zero bytes, `sigHashWitnessV0` $sc\,t\,nIn\,ht\,a$ is the double SHA-256 of the concatenation, in this order, of:
1. the 4-byte little-endian $t.\text{version}$;
2. $hashPrevouts$: if not $acp$, the double SHA-256 of the concatenation over **all** inputs of `serOutPoint` (prevout hash bytes then 4-byte index); else $zero$;
3. $hashSequence$: if not $acp$ and not $single$ and not $none$, the double SHA-256 of the concatenation over all inputs of the 4-byte sequence; else $zero$;
4. `serOutPoint` of the prevout of input $nIn$ (or of the default input with empty hash and index 0, giving just 4 zero bytes, if out of range);
5. `serBytes` $sc$ — the script code verbatim with a compact-size prefix (no `OP_CODESEPARATOR` removal);
6. the 8-byte two's-complement little-endian $a$;
7. the 4-byte sequence of input $nIn$ (or $0$ for the default);
8. $hashOutputs$: if neither $single$ nor $none$, the double SHA-256 of the concatenation of `serTxOut` over all outputs; else if $single$ and $nIn < |t.\text{vout}|$ (strict), the double SHA-256 of `serTxOut` of output $nIn$; else $zero$;
9. the 4-byte $t.\text{nLockTime}$;
10. the 4-byte little-endian $ht \bmod 2^{32}$.
Every transaction field consulted — version, all prevouts, all sequences, the output list, the lock time — is equated by $h$, position by position, and $sc$, $nIn$, $ht$, $a$ are shared; so the preimages and the hashes coincide.

**What is not said.** The statement does not say the converse. It does not say the hash depends on $amount$ in any particular way, only that an equal $amount$ is used on both sides; a negative $amount$ is not excluded by this statement (the rejection of negative amounts lives elsewhere, in the checker). It does not assert the number of inputs is the same (it follows from $h$ but is not stated separately). It does not say anything about which differences between $tx$ and $tx'$ are tolerated beyond "anything outside the skeleton". It does not mention any flag, encoding check, or verification. It does not compare the witness-v0 hash with the legacy hash.
