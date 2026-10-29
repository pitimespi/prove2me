# Read-back: `BitcoinAnchors.anchor_holder`

**Declaration.** For every flag record $f$ (three unconstrained Booleans $f.\mathrm{cltv},f.\mathrm{csv},f.\mathrm{nulldummy}$), every oracle $o$ (arbitrary hash functions, arbitrary three-valued $o.\mathrm{checkSig}$, arbitrary $o.\mathrm{checkLockTime}$, $o.\mathrm{checkSequence}$), and all byte strings $K$ (`fundingKey`) and $\sigma$ (`sig`), under the two hypotheses

- $|K|\le 520$ (`hfk`), and
- $o.\mathrm{checkSig}(\sigma,K)=\mathrm{some\ true}$ (`hcs`),

the following holds:

$$\mathrm{evalScript}\bigl(f,o,[\sigma],\mathrm{anchorScript}(K)\bigr)=\mathrm{some}\,[[1]],$$

i.e. running the seven-instruction script $\mathrm{push}(K)$, OP_CHECKSIG, OP_IFDUP, OP_NOTIF, OP_16, OP_CHECKSEQUENCEVERIFY, OP_ENDIF on the one-element stack $[\sigma]$ does not fail and leaves exactly one element, the one-byte string $0x01$. The conclusion does not depend on $f.\mathrm{csv}$ or on $o.\mathrm{checkSequence}$ in its statement: it is asserted for every $f$ and every $o$ satisfying `hcs`. Nothing is assumed about $\sigma$ beyond the oracle's verdict.

---

## Common unfolded definitions, part A: the script interpreter

Everything below is a literal unfolding of the definitions the statement depends on. Nothing here is a claim about the theorem; it only says what the symbols mean.

**Bytes and stacks.** A *byte* is an 8-bit word, i.e. a value in $\{0,\dots,255\}$. A *byte string* is a finite list of bytes; $|v|$ is its length and $[\,]$ is the empty byte string. A *stack* is a finite list of byte strings written **top first**: in $[a,b,c]$ the element $a$ is on top. The constants are $\mathrm{MAX\_SCRIPT\_ELEMENT\_SIZE}=520$, $\mathrm{MAX\_STACK\_SIZE}=1000$, $\mathrm{MAX\_OPS\_PER\_SCRIPT}=201$, $\mathrm{MAX\_PUBKEYS\_PER\_MULTISIG}=20$.

**Truth value of a byte string**, $\mathrm{castToBool}(v)$: $[\,]$ is false; a one-byte string $[b]$ is true iff $b\neq 0$ and $b\neq 0x80$; a string $b::r$ of length at least two is true iff $b\neq 0$ or $\mathrm{castToBool}(r)$. Equivalently, $v$ is true iff some byte of $v$ is nonzero, except that a string consisting of zero bytes followed by a final byte $0x80$ is false.

**$\mathrm{boolBytes}$**: $\mathrm{boolBytes}(\mathrm{true})=[0x01]$ (the single byte $1$) and $\mathrm{boolBytes}(\mathrm{false})=[\,]$ (the empty byte string).

**Stack literals used in the statements.** $[[1]]$ is the stack with exactly one element, the one-byte string $0x01$; $[[16]]$ is the stack with exactly one element, the one-byte string $0x10$ (decimal $16$); $[[\,]]$ is the stack with exactly one element, the empty byte string; $[\,]$ is the empty stack. A stack written $[\sigma]$ has exactly one element $\sigma$; $[x,\sigma]$ has exactly two, $x$ on top.

**Flags** $f$: a record of three Booleans $f.\mathrm{cltv}$, $f.\mathrm{csv}$, $f.\mathrm{nulldummy}$. No other verification flag exists in this model. Where $f$ is a parameter of a theorem, all three values are unconstrained.

**Oracle** $o$: a record of arbitrary functions with no axioms relating them to each other or to anything else: five byte-string-to-byte-string functions $o.\mathrm{ripemd160}$, $o.\mathrm{sha1}$, $o.\mathrm{sha256}$, $o.\mathrm{hash160}$, $o.\mathrm{hash256}$; a function $o.\mathrm{checkSig}(\sigma,k)$ from pairs of byte strings (first the signature, second the key) to the three values $\mathrm{none}$, $\mathrm{some\ true}$, $\mathrm{some\ false}$; and two functions $o.\mathrm{checkLockTime},\,o.\mathrm{checkSequence}:\mathbb Z\to\{\mathrm{true},\mathrm{false}\}$. In particular, in a theorem that takes $o$ as a parameter, $o.\mathrm{hash160}$ is an arbitrary function (its outputs need not be 20 bytes long, it need not be injective, and it has no relation to $o.\mathrm{sha256}$), and $o.\mathrm{checkSig}$ is an arbitrary three-valued function.

**Script numbers.** $\mathrm{serialize}(v)$ for $v\in\mathbb Z$: $[\,]$ if $v=0$; otherwise the little-endian bytes of $|v|$ with no trailing zero byte, after which: if the last byte has its top bit ($0x80$) set, one extra byte is appended ($0x80$ if $v<0$, $0x00$ if $v>0$); otherwise, if $v<0$, the top bit of the last byte is set. Thus $\mathrm{serialize}(1)=[0x01]$, $\mathrm{serialize}(2)=[0x02]$, $\mathrm{serialize}(16)=[0x10]$, $\mathrm{serialize}(32)=[0x20]$. The decoding $\mathrm{setVch}(v)$ is $0$ for $[\,]$, and otherwise the little-endian value of $v$ with the top bit of the last byte removed and read as a minus sign. $\mathrm{toNum}(\mathrm{false},m,v)$ is $\mathrm{none}$ if $m<|v|$ and $\mathrm{some}\,\mathrm{setVch}(v)$ otherwise (no minimal-encoding check is made).

**Instructions and scripts.** An instruction is either a push $\mathrm{push}(d)$ of a byte string $d$, or an opcode $\mathrm{op}(c)$ for a byte $c$. A script is a finite list of instructions. Opcode bytes that occur: OP_1NEGATE $=0x4f$, OP_1 $=0x51$, OP_2 $=0x52$, OP_16 $=0x60$, OP_IF $=0x63$, OP_NOTIF $=0x64$, OP_ELSE $=0x67$, OP_ENDIF $=0x68$, OP_IFDUP $=0x73$, OP_DROP $=0x75$, OP_DUP $=0x76$, OP_SWAP $=0x7c$, OP_SIZE $=0x82$, OP_EQUAL $=0x87$, OP_EQUALVERIFY $=0x88$, OP_HASH160 $=0xa9$, OP_CHECKSIG $=0xac$, OP_CHECKSIGVERIFY $=0xad$, OP_CHECKMULTISIG $=0xae$, OP_CHECKLOCKTIMEVERIFY $=0xb1$, OP_CHECKSEQUENCEVERIFY $=0xb2$.

$\mathrm{numInstr}(n)$ for $n\in\mathbb Z$: if $n=-1$ or $1\le n\le 16$, the opcode $\mathrm{op}(n+0x50)$ (so $\mathrm{numInstr}(1)=\mathrm{op}(\mathrm{OP\_1})$, $\mathrm{numInstr}(2)=\mathrm{op}(\mathrm{OP\_2})$, $\mathrm{numInstr}(16)=\mathrm{op}(\mathrm{OP\_16})$, $\mathrm{numInstr}(-1)=\mathrm{op}(0x4f)$); otherwise the push $\mathrm{push}(\mathrm{serialize}(n))$ (so $\mathrm{numInstr}(32)=\mathrm{push}([0x20])$ and $\mathrm{numInstr}(0)=\mathrm{push}([\,])$).

**The parsed scripts of the anchors file**, for arbitrary byte strings $K$ (funding key), $R$ (remote key), $L$ (local key), $H$ (revocation hash), $P$ (payment hash) and an integer $e$ (expiry):

$$\mathrm{toRemoteScript}(R)=[\mathrm{push}(R),\ \mathrm{op}(\mathrm{OP\_CHECKSIGVERIFY}),\ \mathrm{op}(\mathrm{OP\_1}),\ \mathrm{op}(\mathrm{OP\_CHECKSEQUENCEVERIFY})].$$

$$\mathrm{anchorScript}(K)=[\mathrm{push}(K),\ \mathrm{op}(\mathrm{OP\_CHECKSIG}),\ \mathrm{op}(\mathrm{OP\_IFDUP}),\ \mathrm{op}(\mathrm{OP\_NOTIF}),\ \mathrm{op}(\mathrm{OP\_16}),\ \mathrm{op}(\mathrm{OP\_CHECKSEQUENCEVERIFY}),\ \mathrm{op}(\mathrm{OP\_ENDIF})].$$

$\mathrm{offeredScript}(H,R,L,P)$ is the 30-instruction list: OP_DUP, OP_HASH160, $\mathrm{push}(H)$, OP_EQUAL, OP_IF, OP_CHECKSIG, OP_ELSE, $\mathrm{push}(R)$, OP_SWAP, OP_SIZE, $\mathrm{push}([0x20])$, OP_EQUAL, OP_NOTIF, OP_DROP, OP_2, OP_SWAP, $\mathrm{push}(L)$, OP_2, OP_CHECKMULTISIG, OP_ELSE, OP_HASH160, $\mathrm{push}(P)$, OP_EQUALVERIFY, OP_CHECKSIG, OP_ENDIF, OP_1, OP_CHECKSEQUENCEVERIFY, OP_DROP, OP_ENDIF.

$\mathrm{receivedScript}(H,R,L,P,e)$ is the 32-instruction list: OP_DUP, OP_HASH160, $\mathrm{push}(H)$, OP_EQUAL, OP_IF, OP_CHECKSIG, OP_ELSE, $\mathrm{push}(R)$, OP_SWAP, OP_SIZE, $\mathrm{push}([0x20])$, OP_EQUAL, OP_IF, OP_HASH160, $\mathrm{push}(P)$, OP_EQUALVERIFY, OP_2, OP_SWAP, $\mathrm{push}(L)$, OP_2, OP_CHECKMULTISIG, OP_ELSE, OP_DROP, $\mathrm{numInstr}(e)$, OP_CHECKLOCKTIMEVERIFY, OP_DROP, OP_CHECKSIG, OP_ENDIF, OP_1, OP_CHECKSEQUENCEVERIFY, OP_DROP, OP_ENDIF.

**Execution state**: a main stack, an alt stack, a condition stack $\mathrm{vfExec}$ (a list of Booleans) and an op counter. The initial state for a stack $st$ has main stack $st$, empty alt stack, empty $\mathrm{vfExec}$, counter $0$. The machine is *executing* when every entry of $\mathrm{vfExec}$ is true (vacuously, when $\mathrm{vfExec}$ is empty).

**$\mathrm{evalScript}(f,o,st,S)$**: starting from the initial state of $st$, apply $\mathrm{step}$ to the instructions of $S$ in order; if any step returns $\mathrm{none}$ the result is $\mathrm{none}$; after the last instruction the result is $\mathrm{none}$ if $\mathrm{vfExec}$ is non-empty and otherwise $\mathrm{some}$ of the final main stack. So the value is either $\mathrm{none}$ (script failure) or $\mathrm{some}\,st'$ for a stack $st'$ (the alt stack and the counter are discarded).

**$\mathrm{step}$ on $\mathrm{push}(d)$**: $\mathrm{none}$ if $520<|d|$; otherwise, if executing, $d$ is placed on top of the main stack (if not executing, nothing changes); then $\mathrm{none}$ if the main-stack size plus the alt-stack size exceeds $1000$, else the new state.

**$\mathrm{step}$ on $\mathrm{op}(c)$**: $c$ is *counted* when $0x60<c$; if counted and the counter plus one exceeds $201$, $\mathrm{none}$; otherwise the counter is incremented when counted; $\mathrm{none}$ if $c$ is one of the fifteen disabled opcodes (none of the opcodes listed above is disabled); otherwise, if executing or $0x63\le c\le 0x68$ (the conditionals), $\mathrm{execOp}$ is applied and the result is $\mathrm{none}$ if it is $\mathrm{none}$ or if the stack-size sum then exceeds $1000$; otherwise (not executing, not a conditional) the state is unchanged, again subject to the size check.

**$\mathrm{execOp}(f,o,\mathrm{fExec},c,s)$** for the opcodes that occur ("$\mathrm{none}$" means script failure; "no change" means the state is returned unchanged):

- OP_1NEGATE, OP_1, …, OP_16: push $\mathrm{serialize}(c-0x50)$; so OP_1 pushes $[0x01]$, OP_2 pushes $[0x02]$, OP_16 pushes $[0x10]$. These bytes are $\le 0x60$, so they are not counted.
- OP_CHECKLOCKTIMEVERIFY: if $f.\mathrm{cltv}=\mathrm{false}$, no change. Otherwise $\mathrm{none}$ on an empty stack; else with top $t$ (not popped): $\mathrm{none}$ if $|t|>5$; with $n=\mathrm{setVch}(t)$, $\mathrm{none}$ if $n<0$, $\mathrm{none}$ if $o.\mathrm{checkLockTime}(n)=\mathrm{false}$, else no change.
- OP_CHECKSEQUENCEVERIFY: if $f.\mathrm{csv}=\mathrm{false}$, no change. Otherwise $\mathrm{none}$ on an empty stack; else with top $t$ (not popped): $\mathrm{none}$ if $|t|>5$; with $n=\mathrm{setVch}(t)$, $\mathrm{none}$ if $n<0$; no change if bit $31$ of $n$ is set (precisely: $\max(n,0)\,\&\,2^{31}\neq 0$); else $\mathrm{none}$ if $o.\mathrm{checkSequence}(n)=\mathrm{false}$, else no change.
- OP_IF / OP_NOTIF: if executing, $\mathrm{none}$ on an empty stack; else the top $t$ is popped, $v=\mathrm{castToBool}(t)$ (negated for OP_NOTIF) and $v$ is pushed onto $\mathrm{vfExec}$. If not executing, $\mathrm{false}$ is pushed onto $\mathrm{vfExec}$ and the stack is untouched.
- OP_ELSE: $\mathrm{none}$ if $\mathrm{vfExec}$ is empty; else its top entry is negated.
- OP_ENDIF: $\mathrm{none}$ if $\mathrm{vfExec}$ is empty; else its top entry is removed.
- OP_IFDUP: $\mathrm{none}$ on an empty stack; else if $\mathrm{castToBool}$ of the top is true the top is duplicated, otherwise no change.
- OP_DROP: $\mathrm{none}$ on an empty stack; else the top is removed. OP_DUP: $\mathrm{none}$ on an empty stack; else the top is duplicated. OP_SWAP: $\mathrm{none}$ with fewer than two elements; else the top two are exchanged. OP_SIZE: $\mathrm{none}$ on an empty stack; else $\mathrm{serialize}(|t|)$ is pushed above the top $t$, which stays.
- OP_EQUAL / OP_EQUALVERIFY: $\mathrm{none}$ with fewer than two elements; else the top $a$ and the next $b$ are popped and $eq$ is the proposition "$a$ and $b$ are the same byte string"; OP_EQUAL pushes $\mathrm{boolBytes}(eq)$; OP_EQUALVERIFY pushes nothing and is $\mathrm{none}$ when $eq$ is false.
- OP_HASH160: $\mathrm{none}$ on an empty stack; else the top $t$ is replaced by $o.\mathrm{hash160}(t)$.
- OP_CHECKSIG / OP_CHECKSIGVERIFY: $\mathrm{none}$ with fewer than two elements; else the top $k$ (the key) and the next $\sigma$ (the signature) are popped and $o.\mathrm{checkSig}(\sigma,k)$ is consulted: $\mathrm{none}$ gives $\mathrm{none}$; $\mathrm{some}\,ok$: OP_CHECKSIG pushes $\mathrm{boolBytes}(ok)$, while OP_CHECKSIGVERIFY pushes nothing and is $\mathrm{none}$ when $ok=\mathrm{false}$.
- OP_CHECKMULTISIG: $\mathrm{none}$ on an empty stack; the top $n_k$ is popped and decoded by $\mathrm{toNum}(\mathrm{false},4,\cdot)$ ($\mathrm{none}$ if longer than 4 bytes); $\mathrm{none}$ if $n_k<0$ or $20<n_k$; the counter becomes counter $+\,n_k$, $\mathrm{none}$ if that exceeds $201$; the next $n_k$ elements are the keys ($\mathrm{none}$ if fewer remain); the next element $n_s$ is popped ($\mathrm{none}$ if none remains) and decoded likewise, $\mathrm{none}$ if $n_s<0$ or $n_k<n_s$; the next $n_s$ elements are the signatures ($\mathrm{none}$ if fewer remain); $\mathrm{multisigLoop}(o,\text{sigs},\text{keys})$ is computed: $\mathrm{none}$ gives $\mathrm{none}$; $\mathrm{some}\,ok$: $\mathrm{none}$ if no element remains, else one more element $dummy$ is popped, $\mathrm{none}$ if $f.\mathrm{nulldummy}=\mathrm{true}$ and $dummy\neq[\,]$, else $\mathrm{boolBytes}(ok)$ is pushed.

**$\mathrm{multisigLoop}(o,\text{sigs},\text{keys})$** (both lists top first): $\mathrm{some\ true}$ if sigs is empty; $\mathrm{some\ false}$ if sigs is non-empty and keys is empty; otherwise, with $\sigma$ the first signature and $k$ the first key, $o.\mathrm{checkSig}(\sigma,k)$: $\mathrm{none}$ gives $\mathrm{none}$; $\mathrm{some\ true}$ gives $\mathrm{some\ false}$ if fewer keys than signatures remain after removing both, else the loop on the remaining signatures and remaining keys; $\mathrm{some\ false}$ gives $\mathrm{some\ false}$ if the remaining keys are fewer than all the current signatures, else the loop on the same signatures and the remaining keys. For the only instance that occurs, $\mathrm{multisigLoop}(o,[\sigma_L,\sigma_R],[L,R])$ unfolds to: $\mathrm{none}$ if $o.\mathrm{checkSig}(\sigma_L,L)=\mathrm{none}$; $\mathrm{some\ false}$ if $o.\mathrm{checkSig}(\sigma_L,L)=\mathrm{some\ false}$; and, if $o.\mathrm{checkSig}(\sigma_L,L)=\mathrm{some\ true}$, the value $o.\mathrm{checkSig}(\sigma_R,R)$ itself. Hence it equals $\mathrm{some\ true}$ iff $o.\mathrm{checkSig}(\sigma_L,L)=\mathrm{some\ true}$ and $o.\mathrm{checkSig}(\sigma_R,R)=\mathrm{some\ true}$; the signature $\sigma_R$ is never checked against $L$, nor $\sigma_L$ against $R$.

**$\mathrm{CsvPasses}(f,o,d)$** for $d\in\mathbb Z$:
$$f.\mathrm{csv}=\mathrm{false}\ \ \lor\ \ \bigl(0\le d\ \land\ (\max(d,0)\,\&\,2^{31}\neq 0\ \lor\ o.\mathrm{checkSequence}(d)=\mathrm{true})\bigr).$$
For $d=1$ and $d=16$ the bit-31 disjunct is false ($1\,\&\,2^{31}=0$ and $16\,\&\,2^{31}=0$), so $\mathrm{CsvPasses}(f,o,1)\iff f.\mathrm{csv}=\mathrm{false}\lor o.\mathrm{checkSequence}(1)=\mathrm{true}$ and $\mathrm{CsvPasses}(f,o,16)\iff f.\mathrm{csv}=\mathrm{false}\lor o.\mathrm{checkSequence}(16)=\mathrm{true}$. When $f$ and $o$ are arbitrary parameters, $o.\mathrm{checkSequence}$ is an arbitrary function of an integer.

**$\mathrm{CltvPasses}(f,o,e)$** for $e\in\mathbb Z$: $f.\mathrm{cltv}=\mathrm{false}\ \lor\ (0\le e\ \land\ o.\mathrm{checkLockTime}(e)=\mathrm{true})$.

**$\mathrm{topTrue}(st)$**: $\mathrm{false}$ for the empty stack; $\mathrm{castToBool}$ of the top element otherwise.

**The spend predicates of the anchors file** (all stacks top first; $\sigma,\sigma_L,\sigma_R,pk,x,d$ range over byte strings):

$\mathrm{ToRemoteSpend}(f,o,R,st)$: there is $\sigma$ with $st=[\sigma]$, $o.\mathrm{checkSig}(\sigma,R)=\mathrm{some\ true}$ and $\mathrm{CsvPasses}(f,o,1)$.

$\mathrm{AnchorSpend}(f,o,K,st)$: there is $\sigma$ with $st=[\sigma]$ and either $o.\mathrm{checkSig}(\sigma,K)=\mathrm{some\ true}$, or both $o.\mathrm{checkSig}(\sigma,K)=\mathrm{some\ false}$ and $\mathrm{CsvPasses}(f,o,16)$.

$\mathrm{OfferedSpend}(f,o,H,R,L,P,st)$ is the disjunction of
1. there are $pk,\sigma$ with $st=[pk,\sigma]$, $o.\mathrm{hash160}(pk)=H$ and $o.\mathrm{checkSig}(\sigma,pk)=\mathrm{some\ true}$;
2. there are $x,\sigma$ with $st=[x,\sigma]$, $o.\mathrm{hash160}(x)\neq H$, $|x|=32$, $o.\mathrm{hash160}(x)=P$, $o.\mathrm{checkSig}(\sigma,R)=\mathrm{some\ true}$ and $\mathrm{CsvPasses}(f,o,1)$;
3. there are $x,\sigma_L,\sigma_R,d$ with $st=[x,\sigma_L,\sigma_R,d]$, $o.\mathrm{hash160}(x)\neq H$, $|x|\neq 32$, $\mathrm{multisigLoop}(o,[\sigma_L,\sigma_R],[L,R])=\mathrm{some\ true}$, ($f.\mathrm{nulldummy}=\mathrm{true}\Rightarrow d=[\,]$) and $\mathrm{CsvPasses}(f,o,1)$.

$\mathrm{ReceivedSpend}(f,o,H,R,L,P,e,st)$ is the disjunction of
1. there are $pk,\sigma$ with $st=[pk,\sigma]$, $o.\mathrm{hash160}(pk)=H$ and $o.\mathrm{checkSig}(\sigma,pk)=\mathrm{some\ true}$;
2. there are $x,\sigma_L,\sigma_R,d$ with $st=[x,\sigma_L,\sigma_R,d]$, $o.\mathrm{hash160}(x)\neq H$, $|x|=32$, $o.\mathrm{hash160}(x)=P$, $\mathrm{multisigLoop}(o,[\sigma_L,\sigma_R],[L,R])=\mathrm{some\ true}$, ($f.\mathrm{nulldummy}=\mathrm{true}\Rightarrow d=[\,]$) and $\mathrm{CsvPasses}(f,o,1)$;
3. there are $x,\sigma$ with $st=[x,\sigma]$, $o.\mathrm{hash160}(x)\neq H$, $|x|\neq 32$, $\mathrm{CltvPasses}(f,o,e)$, $o.\mathrm{checkSig}(\sigma,R)=\mathrm{some\ true}$ and $\mathrm{CsvPasses}(f,o,1)$.
