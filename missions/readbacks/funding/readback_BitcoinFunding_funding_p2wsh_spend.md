# Read-back: `BitcoinFunding.funding_p2wsh_spend`

A **byte** is an 8-bit word; a **byte string** ($\mathsf{Bytes}$) is a finite list of bytes; a **stack** is a finite list of byte strings whose first entry is the top, except where a list is explicitly said to be in "witness order" (last entry on top).

## The quantified data and hypotheses

The theorem quantifies over:

- $tap$: an arbitrary function $\mathrm{Ctx}\times(\text{list of byte strings})\times\mathsf{Bytes}\to\mathrm{Bool}$ (a "Taproot handler"); nothing is assumed about it;
- $c$: a verification context, a record with fields
  - $c.\mathrm{flags}$: a record of seven booleans $\mathrm{p2sh},\ \mathrm{witness},\ \mathrm{taproot},\ \mathrm{dersig},\ \mathrm{cltv},\ \mathrm{csv},\ \mathrm{nulldummy}$;
  - $c.\mathrm{tx}$: a transaction, a record $(\mathrm{version}\in\mathbb{N},\ \mathrm{vin},\ \mathrm{vout},\ \mathrm{nLockTime}\in\mathbb{N})$ where $\mathrm{vin}$ is a list of inputs, each $(\mathrm{prevout}=(\mathrm{hash}\in\mathsf{Bytes},\ n\in\mathbb{N}),\ \mathrm{scriptSig}\in\mathsf{Bytes},\ \mathrm{nSequence}\in\mathbb{N},\ \mathrm{witness}:\text{list of byte strings})$, and $\mathrm{vout}$ is a list of outputs, each $(\mathrm{nValue}\in\mathbb{Z},\ \mathrm{scriptPubKey}\in\mathsf{Bytes})$;
  - $c.\mathrm{nIn}\in\mathbb{N}$ (an input index; it may exceed the number of inputs);
  - $c.\mathrm{amount}\in\mathbb{Z}$ (it may be negative);
- the hypothesis $hf$: $c.\mathrm{flags}.\mathrm{witness}=\mathrm{true}$ (the other six flags are unconstrained);
- two byte strings $k_1,k_2$ (`pubkey1`, `pubkey2`), unconstrained in content, with the hypotheses $|k_1|\le520$ and $|k_2|\le520$;
- $ws$: an arbitrary list of byte strings (possibly empty; element sizes are **not** bounded by any hypothesis).

Write $B:=\mathrm{fundingBytes}(k_1,k_2)$, $H:=\mathrm{SHA256}(B)$, and $P:=\mathrm{witnessBytes}(0,H)$.

## Statement

$$
\mathrm{verifyScript}\big(tap,\ c,\ [\,],\ P,\ ws\,\|\,[B]\big)=\mathrm{true}
\;\Longleftrightarrow\;
\mathrm{castToBool}(H)=\mathrm{true}\ \wedge\ \big(\forall e\in ws,\ |e|\le520\big)\ \wedge\ \mathrm{FundingSpend}\big(F,\ O,\ k_1,\ k_2,\ \mathrm{reverse}(ws)\big),
$$

where

- $[\,]$ in the third argument is the empty scriptSig (an empty byte string), $P$ is the scriptPubKey, and $ws\,\|\,[B]$ is the witness: the list $ws$ with $B$ appended as its last element (so the witness is never empty, even when $ws$ is);
- $F:=\mathrm{scriptFlagsOf}(c.\mathrm{flags}) = (\mathrm{cltv}:=c.\mathrm{flags}.\mathrm{cltv},\ \mathrm{csv}:=c.\mathrm{flags}.\mathrm{csv},\ \mathrm{nulldummy}:=c.\mathrm{flags}.\mathrm{nulldummy})$;
- $O:=\mathrm{legacyOracle}\big(\mathrm{sigFlagsOf}(c.\mathrm{flags}),\ c.\mathrm{tx},\ c.\mathrm{nIn},\ c.\mathrm{amount},\ \mathrm{witnessV0},\ B\big)$ with $\mathrm{sigFlagsOf}(c.\mathrm{flags}) = (\mathrm{dersig}:=c.\mathrm{flags}.\mathrm{dersig},\ \mathrm{lowS}:=\mathrm{false},\ \mathrm{strictenc}:=\mathrm{false},\ \mathrm{witnessPubkeyType}:=\mathrm{false})$;
- $\mathrm{reverse}(ws)$ is $ws$ in reverse order.

Each piece is unfolded below.

## The byte strings $B$, $H$, $P$

$B=\mathrm{fundingBytes}(k_1,k_2)=[\mathtt{0x52}]\ \|\ \mathrm{pushBytes}(k_1)\ \|\ \mathrm{pushBytes}(k_2)\ \|\ [\mathtt{0x52},\mathtt{0xae}]$, where $\mathrm{pushBytes}(d)$ for $\ell=|d|$ is: $[\ell]\|d$ if $\ell<76$; $[\mathtt{0x4c},\ell]\|d$ if $\ell\le255$; $[\mathtt{0x4d}]\|(\ell\text{ as 2 LE bytes})\|d$ if $\ell\le65535$; else $[\mathtt{0x4e}]\|(\ell\text{ as 4 LE bytes})\|d$.

$\mathrm{SHA256}$ is the serialization file's own transcription of SHA-256 (Merkle–Damgård padding with a big-endian 64-bit bit-length, 64-round compression with the standard constants, output the eight 32-bit state words big-endian); its output always has 32 bytes.

$\mathrm{witnessBytes}(v,\mathit{prog})$ is the byte $\mathtt{0x00}$ if $v=0$ (else $\mathtt{0x50}+v$) followed by $\mathrm{pushBytes}(\mathit{prog})$. Hence $P=[\mathtt{0x00},\mathtt{0x20}]\,\|\,H$, a 34-byte string.

## Right-hand side, first conjunct: $\mathrm{castToBool}(H)=\mathrm{true}$

$\mathrm{castToBool}(b)$: $\mathrm{false}$ for $b=[\,]$; for one byte $[x]$, true iff $x\ne\mathtt{0x00}$ and $x\ne\mathtt{0x80}$; for $x::\mathit{rest}$ with $\mathit{rest}\ne[\,]$, true iff $x\ne\mathtt{0x00}$ or $\mathrm{castToBool}(\mathit{rest})$. For the 32-byte $H$: true iff one of its first 31 bytes is non-zero, or its last byte is neither $\mathtt{0x00}$ nor $\mathtt{0x80}$.

## Right-hand side, second conjunct

Every element of $ws$ has length at most $520$. This is vacuously true when $ws=[\,]$. (Note this is a conjunct of the right-hand side, not a hypothesis of the theorem.)

## Right-hand side, third conjunct: $\mathrm{FundingSpend}(F,O,k_1,k_2,\mathrm{reverse}(ws))$

By definition this is
$$
\exists\, s_1,s_2,d\in\mathsf{Bytes}:\ \mathrm{reverse}(ws)=[\,s_2,\,s_1,\,d\,]\ \wedge\ O.\mathrm{checkSig}(s_1,k_1)=\mathrm{some}\,\mathrm{true}\ \wedge\ O.\mathrm{checkSig}(s_2,k_2)=\mathrm{some}\,\mathrm{true}\ \wedge\ \big(F.\mathrm{nulldummy}=\mathrm{true}\Rightarrow d=[\,]\big).
$$
Since $\mathrm{reverse}(ws)=[s_2,s_1,d]$ iff $ws=[d,s_1,s_2]$: $ws$ must have exactly three elements, in the order $d$ (first), $s_1$, $s_2$ (last); if $ws$ has any other length (including $0$) the conjunct is false. $F.\mathrm{nulldummy}$ is $c.\mathrm{flags}.\mathrm{nulldummy}$; when it is true, $d$ must be empty; otherwise $d$ is arbitrary. The sizes of $s_1,s_2,d$ are constrained only by the second conjunct.

**The oracle $O$.** $\mathrm{legacyOracle}(sf,tx,nIn,amt,v,sc)$ is the oracle whose hash fields are the concrete RIPEMD-160, SHA-1, SHA-256, $\mathrm{Hash160}=\mathrm{RIPEMD160}\circ\mathrm{SHA256}$ and $\mathrm{Hash256}=\mathrm{SHA256}\circ\mathrm{SHA256}$ of the serialization file; whose lock-time fields are the transaction lock-time/sequence checks for $(tx,nIn)$ (not consulted by $\mathrm{FundingSpend}$); and whose $\mathrm{checkSig}(\sigma,\pi)$ is $\mathrm{checkSigPreTapscript}(sf,tx,nIn,amt,v,sc,\sigma,\pi)$. Here $sf=\mathrm{sigFlagsOf}(c.\mathrm{flags})$, $tx=c.\mathrm{tx}$, $nIn=c.\mathrm{nIn}$, $amt=c.\mathrm{amount}$, $v=\mathrm{witnessV0}$, $sc=B$.

**$\mathrm{checkSigPreTapscript}(sf,tx,nIn,amt,v,sc,\sigma,\pi)$.** Since $v=\mathrm{witnessV0}$, the script code used is $sc=B$ itself (no FindAndDelete). The result is $\mathrm{none}$ if $\mathrm{checkSignatureEncoding}(sf,\sigma)$ is false or $\mathrm{checkPubKeyEncoding}(sf,v,\pi)$ is false; otherwise $\mathrm{some}\big(\mathrm{checkECDSASignature}(tx,nIn,amt,v,\sigma,\pi,sc)\big)$.

- $\mathrm{checkSignatureEncoding}(sf,\sigma)$: true if $\sigma=[\,]$; else false if $(sf.\mathrm{dersig}\vee sf.\mathrm{lowS}\vee sf.\mathrm{strictenc})$ and $\neg\mathrm{isValidSignatureEncoding}(\sigma)$; else false if $sf.\mathrm{lowS}$ and not low-S DER; else false if $sf.\mathrm{strictenc}$ and the hash type is not defined; else true. With $sf=\mathrm{sigFlagsOf}(c.\mathrm{flags})$ this reduces to: true if $\sigma=[\,]$; false if $c.\mathrm{flags}.\mathrm{dersig}=\mathrm{true}$ and $\neg\mathrm{isValidSignatureEncoding}(\sigma)$; true otherwise.
- $\mathrm{isValidSignatureEncoding}(\sigma)$, with $\ell=|\sigma|$ and out-of-range indices reading as $0$: false if $\ell<9$ or $\ell>73$; requires $\sigma[0]=\mathtt{0x30}$, $\sigma[1]=\ell-3$; let $\ell_R=\sigma[3]$, require $\ell>5+\ell_R$; let $\ell_S=\sigma[5+\ell_R]$, require $\ell_R+\ell_S+7=\ell$; $\sigma[2]=\mathtt{0x02}$; $\ell_R\ne0$; $\sigma[4]<\mathtt{0x80}$; not ($\ell_R>1$ and $\sigma[4]=0$ and $\sigma[5]<\mathtt{0x80}$); $\sigma[\ell_R+4]=\mathtt{0x02}$; $\ell_S\ne0$; $\sigma[\ell_R+6]<\mathtt{0x80}$; not ($\ell_S>1$ and $\sigma[\ell_R+6]=0$ and $\sigma[\ell_R+7]<\mathtt{0x80}$); true if all hold.
- $\mathrm{checkPubKeyEncoding}(sf,v,\pi)$: false if $sf.\mathrm{strictenc}$ and $\pi$ is not a 33-byte ($\mathtt{02}/\mathtt{03}$) or 65-byte ($\mathtt{04}$) key; false if $sf.\mathrm{witnessPubkeyType}$ and $v=\mathrm{witnessV0}$ and $\pi$ is not a 33-byte compressed key; else true. With $sf=\mathrm{sigFlagsOf}(c.\mathrm{flags})$ both flags are false, so this is **always true**: no public-key string is rejected at this stage.

Consequently, in this theorem, $O.\mathrm{checkSig}(\sigma,\pi)=\mathrm{none}$ iff $c.\mathrm{flags}.\mathrm{dersig}=\mathrm{true}$, $\sigma\ne[\,]$ and $\sigma$ fails $\mathrm{isValidSignatureEncoding}$; and $O.\mathrm{checkSig}(\sigma,\pi)=\mathrm{some}\,\mathrm{true}$ iff that is not the case and $\mathrm{checkECDSASignature}(c.\mathrm{tx},c.\mathrm{nIn},c.\mathrm{amount},\mathrm{witnessV0},\sigma,\pi,B)=\mathrm{true}$.

**$\mathrm{checkECDSASignature}(tx,nIn,amt,v,\sigma,\pi,sc)$.** False if $\neg\mathrm{pubkeyValid}(\pi)$, where $\mathrm{pubkeyValid}(\pi)$ holds iff $\pi\ne[\,]$ and $|\pi|$ equals $33$ when the first byte is $2$ or $3$, $65$ when it is $4$, $6$ or $7$, and $0$ otherwise (so any other first byte gives false). False if $\sigma=[\,]$. Otherwise let $ht$ be the last byte of $\sigma$ (as a natural number, the hash type) and $\sigma'$ be $\sigma$ without its last byte; let $\mathit{digest}=\mathrm{sigHashWitnessV0}(sc,tx,nIn,ht,amt)$ (since $v=\mathrm{witnessV0}$); false if $amt<0$; otherwise $\mathrm{pubkeyVerify}(\pi,\mathit{digest},\sigma')$.

**$\mathrm{sigHashWitnessV0}(sc,tx,nIn,ht,amt)$.** Let $\mathit{acp}:=(ht\,\&\,\mathtt{0x80}\ne0)$, $\mathit{single}:=(ht\,\&\,\mathtt{0x1f}=3)$, $\mathit{none}:=(ht\,\&\,\mathtt{0x1f}=2)$; $\mathbf{0}$ the 32-byte zero string; $\mathrm{ser32}(x)$ the 4 little-endian bytes of $x$ modulo $2^{32}$; $\mathrm{serInt64}(x)$ the 8 little-endian bytes of $x \bmod 2^{64}$; $\mathrm{serBytes}(b)$ a CompactSize encoding of $|b|$ followed by $b$; $\mathrm{serOutPoint}(h,n)=h\,\|\,\mathrm{ser32}(n)$; $\mathrm{serTxOut}(o)=\mathrm{serInt64}(o.\mathrm{nValue})\,\|\,\mathrm{serBytes}(o.\mathrm{scriptPubKey})$; $\mathrm{Hash256}=\mathrm{SHA256}\circ\mathrm{SHA256}$.

- $\mathit{hashPrevouts}:=\mathrm{Hash256}$ of the concatenation over all inputs of $\mathrm{serOutPoint}(\mathrm{prevout})$ if $\neg\mathit{acp}$, else $\mathbf{0}$;
- $\mathit{hashSequence}:=\mathrm{Hash256}$ of the concatenation over all inputs of $\mathrm{ser32}(\mathrm{nSequence})$ if $\neg\mathit{acp}\wedge\neg\mathit{single}\wedge\neg\mathit{none}$, else $\mathbf{0}$;
- $\mathit{hashOutputs}:=\mathrm{Hash256}$ of the concatenation of $\mathrm{serTxOut}$ over all outputs if $\neg\mathit{single}\wedge\neg\mathit{none}$; else $\mathrm{Hash256}(\mathrm{serTxOut}(\mathrm{vout}[nIn]))$ if $\mathit{single}$ and $nIn<|\mathrm{vout}|$; else $\mathbf{0}$;
- $i:=\mathrm{vin}[nIn]$, or the default input $(\mathrm{prevout}=([\,],0),\ \mathrm{scriptSig}=[\,],\ \mathrm{nSequence}=0,\ \mathrm{witness}=[\,])$ when $nIn\ge|\mathrm{vin}|$;
- the digest is $\mathrm{Hash256}\big(\mathrm{ser32}(\mathrm{version})\,\|\,\mathit{hashPrevouts}\,\|\,\mathit{hashSequence}\,\|\,\mathrm{serOutPoint}(i.\mathrm{prevout})\,\|\,\mathrm{serBytes}(sc)\,\|\,\mathrm{serInt64}(amt)\,\|\,\mathrm{ser32}(i.\mathrm{nSequence})\,\|\,\mathit{hashOutputs}\,\|\,\mathrm{ser32}(\mathrm{nLockTime})\,\|\,\mathrm{ser32}(ht)\big)$.

**$\mathrm{pubkeyVerify}(\pi,h,\sigma')$.** False if $\neg\mathrm{pubkeyValid}(\pi)$. Let $Q:=\mathrm{parsePubkey}(\pi)$; false if $\mathrm{none}$. Let $(r,s):=\mathrm{parseDerLax}(\sigma')$; false if $\mathrm{none}$. Otherwise $\mathrm{ecdsaVerifyRaw}(Q,\ \mathrm{beVal}(h)\bmod n,\ r,\ \mathrm{normalizeS}(s))$, where $\mathrm{beVal}$ is the big-endian value of a byte string and $n$ is the secp256k1 group order.

- $\mathrm{parsePubkey}(\pi)$: for a 33-byte string with first byte $2$ or $3$, $x:=$ big-endian value of the remaining 32 bytes; $\mathrm{none}$ if $x\ge p$ (the field prime $2^{256}-2^{32}-977$); else, with $y_0:=(x^3+7)^{(p+1)/4}\bmod p$, the point $(x,y)$ with $y\in\{y_0,p-y_0\}$ chosen so that $y$ is odd iff the first byte is $3$, provided $y_0^2\equiv x^3+7\pmod p$, else $\mathrm{none}$. For a 65-byte string with first byte $4$, $6$ or $7$: $x,y:=$ big-endian values of bytes $1$–$32$ and $33$–$64$; the point $(x,y)$ iff $x<p$, $y<p$, $y^2\equiv x^3+7\pmod p$, and (if the first byte is $6$ or $7$) $y$ is odd iff the byte is $7$; else $\mathrm{none}$. Any other string: $\mathrm{none}$.
- $\mathrm{parseDerLax}(\sigma')$: a lax DER parse (sequence tag $\mathtt{0x30}$, length byte possibly long-form, two integers each with tag $\mathtt{0x02}$ and short- or long-form length with leading zero length bytes stripped and at most 3 length bytes); $\mathrm{none}$ where the parser fails (empty input, wrong tags, lengths overrunning the input); after stripping leading zero bytes of each integer, the pair $(0,0)$ if either integer has more than 32 significant bytes or if $r\ge n$ or $s\ge n$; otherwise $(r,s)$. Bytes after the second integer are ignored.
- $\mathrm{normalizeS}(s)=n-s$ if $s>\lfloor n/2\rfloor$, else $s$.
- $\mathrm{ecdsaVerifyRaw}(Q,e,r,s)$: false if $r=0$ or $s=0$ or $r\ge n$ or $s\ge n$; else with $w:=s^{\,n-2}\bmod n$, $u_1:=e\,w\bmod n$, $u_2:=r\,w\bmod n$, and $R:=u_1G+u_2Q$ computed by the file's affine secp256k1 formulas (double-and-add with 257 iterations of fuel, field inversion by Fermat exponentiation with $0\mapsto0$), false if $R$ is the point at infinity, and otherwise true iff $x(R)\bmod n=r$. $G$ is the standard secp256k1 generator given by its coordinates.

## Left-hand side: `verifyScript`

$\mathrm{verifyScript}(tap,c,\mathit{scriptSig},\mathit{scriptPubKey},\mathit{witness})$, in general:

1. $st_1:=\mathrm{evalBytes}(c,\mathrm{base},[\,],\mathit{scriptSig})$; result $\mathrm{false}$ if $\mathrm{none}$.
2. $st_2:=\mathrm{evalBytes}(c,\mathrm{base},st_1,\mathit{scriptPubKey})$; $\mathrm{false}$ if $\mathrm{none}$.
3. $\mathrm{false}$ if $\neg\mathrm{topTrue}(st_2)$, where $\mathrm{topTrue}$ of an empty stack is false and otherwise is $\mathrm{castToBool}$ of the top element.
4. If $c.\mathrm{flags}.\mathrm{witness}$ (true here by $hf$): compute $\mathrm{isWitnessProgram}(\mathit{scriptPubKey})$; if it is $\mathrm{some}(v,\mathit{prog})$ then the result is $\mathrm{false}$ if $\mathit{scriptSig}\ne[\,]$, else $\mathrm{verifyWitnessProgram}(tap,c,\mathit{witness},v,\mathit{prog},\mathrm{false})$; if it is $\mathrm{none}$, continue.
5. (Only reached when the scriptPubKey is not a witness program.) If $c.\mathrm{flags}.\mathrm{p2sh}$ and $\mathit{scriptPubKey}$ is 23 bytes of the form $\mathtt{0xa9},\mathtt{0x14},\ldots,\mathtt{0x87}$: the pay-to-script-hash branch (push-only scriptSig, redeem script taken from the top of $st_1$, re-evaluation, a nested witness-program check); otherwise $\mathrm{false}$ if $c.\mathrm{flags}.\mathrm{witness}$ and $\mathit{witness}\ne[\,]$, else $\mathrm{true}$.

$\mathrm{evalBytes}(c,v,st,s)$: $\mathrm{none}$ if $|s|>10000$; $\mathrm{none}$ if $\mathrm{parseScript}(s)=\mathrm{none}$; otherwise $\mathrm{evalScript}\big(\mathrm{scriptFlagsOf}(c.\mathrm{flags}),\ \mathrm{legacyOracle}(\mathrm{sigFlagsOf}(c.\mathrm{flags}),c.\mathrm{tx},c.\mathrm{nIn},c.\mathrm{amount},v,s),\ st,\ \mathrm{parsed}(s)\big)$ — note the oracle's script code is the byte string $s$ being evaluated, and the signature version $v$ is as passed.

$\mathrm{parseScript}(s)$: splits $s$ into instructions left to right: a byte $o\le\mathtt{0x4e}$ starts a push (size $o$ if $o<\mathtt{0x4c}$; the next 1, 2 or 4 little-endian bytes for $\mathtt{0x4c},\mathtt{0x4d},\mathtt{0x4e}$), $\mathrm{none}$ if the size or the data run past the end; a byte $>\mathtt{0x4e}$ is a non-push opcode $\mathrm{op}(o)$. The empty string parses to the empty script.

$\mathrm{isWitnessProgram}(s)$: $\mathrm{none}$ if $|s|<4$ or $|s|>42$; with $b_0:=s[0]$, $\mathrm{none}$ if $b_0\ne0$ and ($b_0<\mathtt{0x51}$ or $b_0>\mathtt{0x60}$); $\mathrm{some}(\mathrm{decodeOpN}(b_0),\ s\text{ without its first two bytes})$ if $s[1]+2=|s|$, else $\mathrm{none}$; $\mathrm{decodeOpN}(0)=0$ and $\mathrm{decodeOpN}(b)=b-\mathtt{0x50}$ otherwise.

$\mathrm{verifyWitnessProgram}(tap,c,W,v,\mathit{prog},\mathit{isP2sh})$, with $W$ in witness order (last element on top):

- $v=0$ and $|\mathit{prog}|=32$: $\mathrm{false}$ if $W=[\,]$; else let $\varsigma$ be the last element of $W$; $\mathrm{false}$ if $\mathrm{SHA256}(\varsigma)\ne\mathit{prog}$; else $\mathrm{executeWitnessScriptV0}(c,\ \mathrm{reverse}(W\text{ without its last element}),\ \varsigma)$.
- $v=0$ and $|\mathit{prog}|=20$: $\mathrm{false}$ unless $|W|=2$, then the pay-to-witness-public-key-hash execution. $v=0$ with any other program length: $\mathrm{false}$.
- $v=1$, $|\mathit{prog}|=32$, $\neg\mathit{isP2sh}$: $\mathrm{true}$ if $\neg c.\mathrm{flags}.\mathrm{taproot}$, else $tap(c,W,\mathit{prog})$ (the only place $tap$ is consulted).
- otherwise $\mathrm{true}$ (unknown versions and pay-to-anchor).

$\mathrm{executeWitnessScriptV0}(c,st,\mathit{exec})$: $\mathrm{false}$ if some element of $st$ has length $>520$; else $\mathrm{evalBytes}(c,\mathrm{witnessV0},st,\mathit{exec})$: $\mathrm{false}$ if $\mathrm{none}$; if $\mathrm{some}(st')$, the result is $|st'|=1$ and $\mathrm{topTrue}(st')$.

**Specialized to the theorem's arguments** (by the definitions above, on the concrete syntactic inputs): the scriptSig is $[\,]$, which parses to the empty script and evaluates on the empty stack to $\mathrm{some}\,[\,]$; the scriptPubKey $P=[\mathtt{0x00},\mathtt{0x20}]\|H$ parses to the two pushes $\mathrm{push}([\,]),\ \mathrm{push}(H)$, evaluated under $\mathrm{base}$ with the legacy oracle for script code $P$; $\mathrm{isWitnessProgram}(P)$ is $\mathrm{some}(0,H)$ (since $|P|=34\in[4,42]$, $b_0=0$, and $\mathtt{0x20}+2=34$); the scriptSig is empty, so step 4 yields $\mathrm{verifyWitnessProgram}(tap,c,\ ws\|[B],\ 0,\ H,\ \mathrm{false})$; there $|H|=32$, the last element of $ws\|[B]$ is $B$, and removing it and reversing gives $\mathrm{reverse}(ws)$, so this is: $\mathrm{false}$ if $\mathrm{SHA256}(B)\ne H$ (which is the definition of $H$), else $\mathrm{executeWitnessScriptV0}(c,\mathrm{reverse}(ws),B)$, i.e. the $520$-byte check on every element of $ws$, then $\mathrm{evalBytes}(c,\mathrm{witnessV0},\mathrm{reverse}(ws),B)$ — which, if $|B|\le10000$ and $B$ parses, is the interpreter $\mathrm{evalScript}$ with flags $F$ and oracle $O$ (the same $F$ and $O$ as on the right-hand side, since the script code is $B$ and the version is $\mathrm{witnessV0}$) on the initial stack $\mathrm{reverse}(ws)$ over the parsed $B$ — and finally the requirement that the resulting stack have exactly one element whose $\mathrm{castToBool}$ is true.

## The interpreter `evalScript` (as invoked above)

$\mathrm{evalScript}(f,o,st_0,S)$ is $\mathrm{none}$ or $\mathrm{some}(st)$. State: (main stack, alternate stack, condition stack $\mathit{vfExec}$, opcode counter), initially $(st_0,[\,],[\,],0)$; instructions of $S$ are run in order, any failure giving $\mathrm{none}$; after the last instruction the run fails if $\mathit{vfExec}\ne[\,]$, else returns the main stack.

- $\mathrm{push}(x)$: fail if $|x|>520$; if all of $\mathit{vfExec}$ is true (vacuous when empty) push $x$; fail if $|\text{main}|+|\text{alt}|>1000$.
- $\mathrm{op}(\gamma)$: counted iff $\gamma>\mathtt{0x60}$; if counted and counter$+1>201$ fail, else increment if counted; fail if $\gamma$ is one of the fifteen disabled opcodes; if all of $\mathit{vfExec}$ is true or $\mathtt{0x63}\le\gamma\le\mathtt{0x68}$, run the one-opcode executor (fail on failure) and then the $1000$ check; else skip with the $1000$ check.

One-opcode executor on the opcodes that the parsed $B$ can contain, $\mathtt{0x52}$ and $\mathtt{0xae}$ (the keys $k_1,k_2$ appear only as push data; if parsing of $B$ yields other opcodes, their branches are not reproduced here):

- $\gamma=\mathtt{0x52}$ (branch for $\mathtt{0x4f}$ or $\mathtt{0x51}$–$\mathtt{0x60}$; not counted): push the script-number encoding of $\gamma-\mathtt{0x50}$, i.e. $[\mathtt{0x02}]$.
- $\gamma=\mathtt{0xae}$ (counted), with main stack $st$ and counter $\kappa$: fail if $st=[\,]$; $st=n_k::r$; $N_k:=$ signed little-endian value of $n_k$ (fail if $|n_k|>4$; sign = top bit of last byte; empty $=0$); fail if $N_k<0$ or $N_k>20$; $\kappa':=\kappa+N_k$, fail if $\kappa'>201$; $\mathit{keys}:=$ first $N_k$ of $r$, $r:=$ rest, fail if fewer were available; fail if $r=[\,]$; $r=n_s::r$; $N_s:=$ value of $n_s$ likewise (fail if $|n_s|>4$); fail if $N_s<0$ or $N_s>N_k$; $\mathit{sigs}:=$ first $N_s$ of $r$, $r:=$ rest, fail if fewer were available; $\mathrm{multisigLoop}(o,\mathit{sigs},\mathit{keys})$: fail if $\mathrm{none}$, else $ok$; fail if $r=[\,]$; $r=d'::r'$; fail if $f.\mathrm{nulldummy}$ and $d'\ne[\,]$; new main stack $\mathrm{boolBytes}(ok)::r'$ ($[\mathtt{0x01}]$ for true, $[\,]$ for false), counter $\kappa'$.

$\mathrm{multisigLoop}(o,\mathit{sigs},\mathit{keys})$ (top-first): $\mathit{sigs}=[\,]\Rightarrow\mathrm{some}\,\mathrm{true}$; $\mathit{sigs}\ne[\,],\mathit{keys}=[\,]\Rightarrow\mathrm{some}\,\mathrm{false}$; $\mathit{sigs}=s::\mathit{sigs}'$, $\mathit{keys}=k::\mathit{keys}'$: $o.\mathrm{checkSig}(s,k)$ is $\mathrm{none}\Rightarrow\mathrm{none}$; $\mathrm{some}\,\mathrm{true}\Rightarrow$ if $|\mathit{keys}'|<|\mathit{sigs}'|$ then $\mathrm{some}\,\mathrm{false}$ else recurse on $(\mathit{sigs}',\mathit{keys}')$; $\mathrm{some}\,\mathrm{false}\Rightarrow$ if $|\mathit{keys}'|<|\mathit{sigs}|$ then $\mathrm{some}\,\mathrm{false}$ else recurse on $(\mathit{sigs},\mathit{keys}')$ (same signature, next key). The top signature is tried against the top key first.

## What the quantification silently includes

- $ws$ may be empty or of any length; its elements may be of any size. On the right-hand side, a $ws$ of length $\ne3$ makes $\mathrm{FundingSpend}$ false; on the left, $\mathrm{reverse}(ws)$ is the initial witness stack.
- The hypotheses $|k_1|,|k_2|\le520$ bound only the two keys; the keys are arbitrary byte strings (no public-key format is assumed; the encoding check on keys is vacuous under $\mathrm{sigFlagsOf}$, and format only enters through $\mathrm{pubkeyValid}$/$\mathrm{parsePubkey}$ inside $\mathrm{checkECDSASignature}$).
- $c.\mathrm{amount}$ may be negative (then $\mathrm{checkECDSASignature}$ is false for every signature/key pair); $c.\mathrm{nIn}$ may be out of range (then the default input is used in the digest); $c.\mathrm{flags}.\mathrm{p2sh},\mathrm{taproot},\mathrm{dersig},\mathrm{cltv},\mathrm{csv},\mathrm{nulldummy}$ are unconstrained; $c.\mathrm{flags}.\mathrm{witness}$ is fixed to true by $hf$.
- $tap$ is arbitrary and enters only through the version-1 branch of $\mathrm{verifyWitnessProgram}$.
- The equivalence relates a boolean equal to $\mathrm{true}$ on the left with a conjunction of a boolean equation, a universally quantified bound, and an existential proposition on the right.
