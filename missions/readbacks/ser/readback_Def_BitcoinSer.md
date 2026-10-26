# Read-back: `Def_BitcoinSer`

**Scope.** This file imports only the standard library and opens a single namespace. Everything below lives in that namespace. It introduces byte types, little-endian integer encoders and decoders, a variable-length integer ("CompactSize") encoder and decoder, list and byte-string encoders and decoders, record types for transactions, headers and blocks together with their serializers and deserializers, "well-formedness" predicates on those records, three hash functions (SHA-256, RIPEMD-160, SHA-1), composite hashes, weight functions, and a handful of concrete constants (a coinbase transaction, a header, a block, two 32-byte strings). Every decoder is a partial function, returning "no result" (written $\bot$ below) instead of raising an error. I go through the declarations in file order.

---

## Byte types and the size bound

**`Byte`, `Bytes`.** A *byte* is a bit-vector of width 8 (so an integer in $[0, 255]$); a *byte string* is a finite list of bytes. Lists may be empty. Throughout, $|s|$ denotes the length of a list $s$, $s[{:}k]$ its first $k$ elements (or all of $s$ if it has fewer), and $s[k{:}]$ the remainder after dropping $k$ elements (empty if $s$ has at most $k$).

**`MAX_SIZE`.** The natural number $\texttt{MAX\_SIZE} = \mathrm{0x02000000} = 33\,554\,432 = 2^{25}$.

---

## Little-endian fixed-width integers

**`leBytes k n`** ($k, n \in \mathbb{N}$). Defined by recursion on $k$: for $k = 0$ the result is the empty list; for $k+1$ it is the byte $n \bmod 256$ followed by $\texttt{leBytes}\;k\;\lfloor n/256\rfloor$. So the result always has exactly $k$ bytes, the least-significant byte first, and it encodes $n \bmod 2^{8k}$: any higher bits of $n$ are silently discarded (truncation, not failure). For $k = 0$ every $n$ gives the empty list.

**`leVal s`.** The little-endian value of a byte list: $\texttt{leVal}([\,]) = 0$ and $\texttt{leVal}(b :: r) = b + 256\cdot\texttt{leVal}(r)$. The empty list has value $0$; a list of $k$ bytes has value in $[0, 2^{8k})$.

**`readLE k s`.** If $|s| < k$ the result is $\bot$; otherwise it is the pair $(\texttt{leVal}(s[{:}k]),\, s[k{:}])$. Note the boundary: exactly $k$ bytes available is a success. For $k = 0$ the result is always $(0, s)$, even on the empty string.

**`beBytes k n`.** The reversal of $\texttt{leBytes}\;k\;n$: $k$ bytes, most-significant first, encoding $n \bmod 2^{8k}$.

**`ser8`, `ser16`, `ser32`, `ser64`.** Abbreviations for $\texttt{leBytes}$ with $k = 1, 2, 4, 8$ respectively. Inputs are unrestricted natural numbers; values $\ge 2^{8k}$ are truncated modulo $2^{8k}$.

**`serInt64 n`** ($n \in \mathbb{Z}$). The 8 little-endian bytes of the natural number $(n \bmod 2^{64})$, where $\bmod$ on integers here always yields a result in $[0, 2^{64})$ (Euclidean remainder with positive divisor). Hence $n \in [-2^{63}, 2^{63})$ is encoded in two's complement; an $n$ outside $[-2^{64}, 2^{64})$ wraps around.

**`serInt32 n`.** The same with 4 bytes and modulus $2^{32}$.

**`readInt64 s`.** Apply $\texttt{readLE}\;8$; if that gives $(v, r)$ then return $(v, r)$ if $v < 2^{63}$ and $(v - 2^{64}, r)$ otherwise, as integers. So the decoded value always lies in $[-2^{63}, 2^{63})$. $\bot$ if fewer than 8 bytes.

**`readInt32 s`.** Likewise with 4 bytes, thresholds $2^{31}$ and $2^{32}$; decoded value in $[-2^{31}, 2^{31})$.

---

## CompactSize

**`writeCompactSize n`** ($n \in \mathbb{N}$). A case split on $n$:

- $n < 253$: the single byte $n$;
- $253 \le n \le \mathrm{0xffff}$: the byte $253$ followed by $\texttt{ser16}\;n$;
- $\mathrm{0xffff} < n \le \mathrm{0xffffffff}$: the byte $254$ followed by $\texttt{ser32}\;n$;
- otherwise: the byte $255$ followed by $\texttt{ser64}\;n$.

For $n \ge 2^{64}$ the last case still applies and the 8 bytes hold $n \bmod 2^{64}$ (truncation).

**`readCompactSize rc s`** ($rc$ a Boolean, $s$ a byte string). If $s$ is empty: $\bot$. Otherwise let $c$ be the first byte and $r$ the rest, and compute a provisional result:

- $c < 253$: $(c, r)$;
- $c = 253$: read 2 bytes little-endian from $r$ to get $(v, r')$; if that read fails, $\bot$; if $v < 253$, $\bot$ (non-canonical); else $(v, r')$;
- $c = 254$: read 4 bytes; $\bot$ on short read; $\bot$ if $v < \mathrm{0x10000}$; else $(v, r')$;
- $c = 255$ (the only remaining case): read 8 bytes; $\bot$ on short read; $\bot$ if $v < \mathrm{0x100000000}$; else $(v, r')$.

Then, if the provisional result is $(v, r')$: return $\bot$ when $rc$ is true **and** $\texttt{MAX\_SIZE} < v$; otherwise return $(v, r')$. Thus with $rc$ true the accepted values are exactly those with $v \le \texttt{MAX\_SIZE}$ (equality allowed); with $rc$ false there is no upper bound beyond the $2^{64}$ implied by 8 bytes. The canonicality rejections are strict: in the 2-byte form $v = 253$ is accepted and $v = 252$ rejected; in the 4-byte form $v = \mathrm{0x10000}$ accepted; in the 8-byte form $v = 2^{32}$ accepted.

---

## Vectors and byte strings

**`serList f l`.** $\texttt{writeCompactSize}(|l|)$ followed by the concatenation of $f(x)$ over the elements $x$ of $l$ in order. The empty list serializes as the single byte $0$.

**`readN f n s`.** Read exactly $n$ items with the reader $f$, threading the remainder: for $n = 0$ return $([\,], s)$ without consuming anything; for $n+1$, apply $f$ to $s$; if it fails, $\bot$; otherwise recurse on the remainder for $n$ more items; if that fails, $\bot$; otherwise prepend the item. There is no bound on $n$ inside `readN` itself.

**`readList f s`.** Apply $\texttt{readCompactSize}$ **with range check on** to get a count $n$ (so $n \le \texttt{MAX\_SIZE}$ or $\bot$), then $\texttt{readN}\;f\;n$ on the remainder.

**`serBytes b`.** $\texttt{writeCompactSize}(|b|)$ followed by the raw bytes of $b$.

**`readBytes s`.** Range-checked $\texttt{readCompactSize}$ to get $(n, s')$ (so $n \le \texttt{MAX\_SIZE}$); then if $|s'| < n$, $\bot$; else $(s'[{:}n], s'[n{:}])$. Exactly $n$ bytes remaining is a success.

**`readHash s`.** If $|s| < 32$, $\bot$; else $(s[{:}32], s[32{:}])$. No interpretation of the bytes.

---

## Transaction record types

**`OutPoint`.** A record with fields $\texttt{hash}$ (a byte string of *unrestricted* length) and $\texttt{n}$ (a natural number, unrestricted).

**`TxIn`.** Fields $\texttt{prevout}$ (an `OutPoint`), $\texttt{scriptSig}$ (bytes), $\texttt{nSequence}$ (natural number), $\texttt{witness}$ (a list of byte strings).

**`TxOut`.** Fields $\texttt{nValue}$ (an **integer**, possibly negative or huge) and $\texttt{scriptPubKey}$ (bytes).

**`Tx`.** Fields $\texttt{version}$ (a **natural number**, not an integer), $\texttt{vin}$ (list of `TxIn`), $\texttt{vout}$ (list of `TxOut`), $\texttt{nLockTime}$ (natural number). All four record types have decidable equality (equality is field-wise).

**`Tx.hasWitness tx`.** Boolean: true iff some input of $\texttt{tx}$ has a non-empty witness list. A transaction with no inputs has no witness.

**`Tx.stripWitness tx`.** The same transaction with every input's witness list replaced by the empty list; all other fields unchanged. It is idempotent, and $\texttt{hasWitness}(\texttt{stripWitness}\;tx)$ is false.

**`serOutPoint o`.** The raw bytes $o.\texttt{hash}$ (whatever their length, with no length prefix) followed by $\texttt{ser32}(o.\texttt{n})$.

**`serTxIn i`.** $\texttt{serOutPoint}(i.\texttt{prevout}) \mathbin{+\!\!+} \texttt{serBytes}(i.\texttt{scriptSig}) \mathbin{+\!\!+} \texttt{ser32}(i.\texttt{nSequence})$. The witness field is **not** included.

**`serTxOut o`.** $\texttt{serInt64}(o.\texttt{nValue}) \mathbin{+\!\!+} \texttt{serBytes}(o.\texttt{scriptPubKey})$.

**`serTx aw tx`** ($aw$ a Boolean "allow witness"). Let $\phi = 1$ if $aw$ is true and $\texttt{hasWitness}(tx)$ is true, else $\phi = 0$. The output is the concatenation of:

1. $\texttt{ser32}(tx.\texttt{version})$ (4 bytes, unsigned, truncated mod $2^{32}$);
2. if $\phi \ne 0$: the two bytes $[\,0\,,\,\phi\,]$ (i.e. $\texttt{writeCompactSize}\;0$ then $\texttt{ser8}\;\phi$), otherwise nothing;
3. $\texttt{serList}\;\texttt{serTxIn}\;tx.\texttt{vin}$;
4. $\texttt{serList}\;\texttt{serTxOut}\;tx.\texttt{vout}$;
5. if $\phi \ne 0$: for each input in order, $\texttt{serList}\;\texttt{serBytes}$ of its witness list (a count then the length-prefixed stack items), otherwise nothing;
6. $\texttt{ser32}(tx.\texttt{nLockTime})$.

Since $\phi \in \{0,1\}$, item 2 is either absent or exactly $[\mathrm{0x00}, \mathrm{0x01}]$. With $aw$ false the output never depends on any witness; with $aw$ true and no non-empty witness it is byte-for-byte the same as with $aw$ false.

**`readOutPoint s`.** $\texttt{readHash}$ (32 bytes) then $\texttt{readLE}\;4$; $\bot$ if either fails.

**`readTxIn s`.** $\texttt{readOutPoint}$, then $\texttt{readBytes}$ (range-checked script), then $\texttt{readLE}\;4$; the resulting input has witness $[\,]$. $\bot$ if any step fails.

**`readTxOut s`.** $\texttt{readInt64}$ then $\texttt{readBytes}$; $\bot$ on failure.

**`attachWitness ins ws`.** Walk the two lists in parallel, replacing the witness of the $i$-th input by the $i$-th element of $ws$. When either list runs out, the remaining inputs are returned **unchanged** (keeping whatever witness they had) and any remaining elements of $ws$ are discarded.

**`readWitnesses n s`.** $\texttt{readN}$ with the item reader $\texttt{readList}\;\texttt{readBytes}$: reads exactly $n$ witness stacks, each a range-checked count followed by that many range-checked length-prefixed byte strings.

**`readTx aw s`.** The control flow is:

1. $\texttt{readLE}\;4$ to get an unsigned $\texttt{version}$; $\bot$ if fewer than 4 bytes.
2. $\texttt{readList}\;\texttt{readTxIn}$ to get $\texttt{vin}_0$; $\bot$ on failure.
3. *Step 2.* If $\texttt{vin}_0$ is empty **and** $aw$ is true:
   - if no bytes remain, $\bot$;
   - otherwise consume one byte $fl$ (the "flags" byte);
   - if $fl \ne 0$: $\texttt{readList}\;\texttt{readTxIn}$ again to get $\texttt{vin}$, then $\texttt{readList}\;\texttt{readTxOut}$ to get $\texttt{vout}$; $\bot$ if either fails; carry $(fl, \texttt{vin}, \texttt{vout})$;
   - if $fl = 0$: carry $(0, \texttt{vin}_0 = [\,], \texttt{vout} = [\,])$ **without reading an output list**; the byte $fl$ has been consumed.

   Otherwise ($\texttt{vin}_0$ non-empty, or $aw$ false): $\texttt{readList}\;\texttt{readTxOut}$ to get $\texttt{vout}$; $\bot$ on failure; carry $(0, \texttt{vin}_0, \texttt{vout})$.
4. *Step 3.* With flags $\phi$ and inputs $\texttt{vin}$ from step 2: if $\phi$ is odd **and** $aw$ is true, read $|\texttt{vin}|$ witness stacks with $\texttt{readWitnesses}$ ($\bot$ on failure), attach them to the inputs in order, and then require that the resulting input list has at least one non-empty witness stack — if it does not, $\bot$ ("superfluous witness record"); on success carry $(\phi - 1, \texttt{vin}')$. Otherwise carry $(\phi, \texttt{vin})$ unchanged. (Note: $\phi \ne 0$ can only arise in the branch where $aw$ is true, so the extra "$aw$ true" test here never changes the outcome.)
5. If the carried flags value is $\ne 0$, $\bot$ ("unknown optional data"). Consequently the only flags byte that can lead to success is $fl = 1$ (odd, and $1 - 1 = 0$); any even non-zero byte, or any odd byte other than 1, yields $\bot$.
6. $\texttt{readLE}\;4$ for $\texttt{nLockTime}$; $\bot$ if short. Return $\langle \texttt{version}, \texttt{vin}, \texttt{vout}, \texttt{lock}\rangle$ with the remaining bytes.

Failure cases worth listing explicitly: any short read; any non-canonical or over-$\texttt{MAX\_SIZE}$ count; $aw$ true, empty first input list and no further byte; $fl = 1$ but zero inputs in the re-read list (then there are zero witness stacks, nothing is non-empty, and the superfluous-witness test fails); $fl = 1$ but all witness stacks empty; $fl \notin \{0, 1\}$. Also note the consequence of the $fl = 0$ branch: a byte string of the form $\texttt{ser32}(v) \mathbin{+\!\!+} [0] \mathbin{+\!\!+} \texttt{writeCompactSize}(m) \mathbin{+\!\!+} \cdots$ (a witness-free transaction with no inputs and $m$ outputs) is, under $aw$ true, read with $m$ in the role of the flags byte, so for $m \ge 1$ the input list is re-read from the bytes of the first output, and for $m = 0$ the outputs are set to $[\,]$ and parsing continues at the lock time. A reader might expect the output count to be read here; the code does not do so.

---

## Headers and blocks

**`Header`.** Fields $\texttt{version}$ (an **integer**, in contrast to `Tx.version`), $\texttt{prevBlock}$ (bytes, unrestricted length), $\texttt{merkleRoot}$ (bytes, unrestricted length), $\texttt{time}$, $\texttt{bits}$, $\texttt{nonce}$ (natural numbers).

**`serHeader h`.** $\texttt{serInt32}(h.\texttt{version}) \mathbin{+\!\!+} h.\texttt{prevBlock} \mathbin{+\!\!+} h.\texttt{merkleRoot} \mathbin{+\!\!+} \texttt{ser32}(h.\texttt{time}) \mathbin{+\!\!+} \texttt{ser32}(h.\texttt{bits}) \mathbin{+\!\!+} \texttt{ser32}(h.\texttt{nonce})$. The two hash fields are emitted raw, with no length prefix and no length check; the length of the result is $16 + |h.\texttt{prevBlock}| + |h.\texttt{merkleRoot}|$.

**`readHeader s`.** $\texttt{readInt32}$ (signed), $\texttt{readHash}$, $\texttt{readHash}$, then three $\texttt{readLE}\;4$; $\bot$ if any fails. Requires at least 80 bytes.

**`Block`.** Fields $\texttt{header}$ and $\texttt{vtx}$ (a list of `Tx`).

**`serBlock aw b`.** $\texttt{serHeader}(b.\texttt{header}) \mathbin{+\!\!+} \texttt{serList}\;(\texttt{serTx}\;aw)\;b.\texttt{vtx}$.

**`readBlock aw s`.** $\texttt{readHeader}$ then $\texttt{readList}\;(\texttt{readTx}\;aw)$; $\bot$ on failure.

---

## Well-formedness predicates

All are propositions (not Booleans).

**`OutPoint.wf o`.** $|o.\texttt{hash}| = 32$ and $o.\texttt{n} < 2^{32}$.

**`TxIn.wf i`.** $i.\texttt{prevout}$ is well-formed, and $|i.\texttt{scriptSig}| \le \texttt{MAX\_SIZE}$, and $i.\texttt{nSequence} < 2^{32}$, and $|i.\texttt{witness}| \le \texttt{MAX\_SIZE}$, and every element $w$ of $i.\texttt{witness}$ has $|w| \le \texttt{MAX\_SIZE}$. (Each "$\le \texttt{MAX\_SIZE}$" matches the reader's acceptance of counts equal to $\texttt{MAX\_SIZE}$.)

**`TxOut.wf o`.** $-2^{63} \le o.\texttt{nValue} < 2^{63}$ and $|o.\texttt{scriptPubKey}| \le \texttt{MAX\_SIZE}$.

**`Tx.wf tx`.** $tx.\texttt{version} < 2^{32}$, $tx.\texttt{nLockTime} < 2^{32}$, $|tx.\texttt{vin}| \le \texttt{MAX\_SIZE}$, $|tx.\texttt{vout}| \le \texttt{MAX\_SIZE}$, every input well-formed, every output well-formed. Nothing is required of the number of inputs (it may be zero) or of the witness/no-witness status.

**`Header.wf h`.** $-2^{31} \le h.\texttt{version} < 2^{31}$, $|h.\texttt{prevBlock}| = 32$, $|h.\texttt{merkleRoot}| = 32$, and $h.\texttt{time}, h.\texttt{bits}, h.\texttt{nonce} < 2^{32}$.

**`Block.wf b`.** $b.\texttt{header}$ well-formed, $|b.\texttt{vtx}| \le \texttt{MAX\_SIZE}$, and for every transaction $tx$ in $b.\texttt{vtx}$: $tx$ is well-formed **and** ($tx.\texttt{vin} \ne [\,]$ or $\texttt{hasWitness}(tx)$ is true). Since a transaction with a non-empty witness necessarily has at least one input, the second disjunct implies the first, and the parenthesised condition is equivalent to "$tx$ has at least one input". This condition is imposed regardless of which serialization mode a theorem later uses.

---

## SHA-256

**Primitive word operations.** All on 32-bit unsigned words with wrap-around addition. $\texttt{rotr}(x, n) = (x \gg n) \,|\, (x \ll (32 - n))$ (a right rotation for $1 \le n \le 31$; shift amounts in this word type are taken modulo 32, which is only relevant for $n = 0$, never used). $\texttt{Ch}(x,y,z) = z \oplus (x \wedge (y \oplus z))$; $\texttt{Maj}(x,y,z) = (x \wedge y) \,|\, (z \wedge (x \,|\, y))$; $\Sigma_0(x) = \texttt{rotr}(x,2) \oplus \texttt{rotr}(x,13) \oplus \texttt{rotr}(x,22)$; $\Sigma_1(x) = \texttt{rotr}(x,6) \oplus \texttt{rotr}(x,11) \oplus \texttt{rotr}(x,25)$; $\sigma_0(x) = \texttt{rotr}(x,7) \oplus \texttt{rotr}(x,18) \oplus (x \gg 3)$; $\sigma_1(x) = \texttt{rotr}(x,17) \oplus \texttt{rotr}(x,19) \oplus (x \gg 10)$.

**`sha256K`.** A list of **64** 32-bit words written in decimal; the first is $\mathrm{0x428a2f98}$ and the last $\mathrm{0xc67178f2}$; all entries are below $2^{32}$.

**`Sha256State`, `sha256Init`.** An 8-word state $(a,\dots,h)$ with initial value $(\mathrm{0x6a09e667}, \mathrm{0xbb67ae85}, \mathrm{0x3c6ef372}, \mathrm{0xa54ff53a}, \mathrm{0x510e527f}, \mathrm{0x9b05688c}, \mathrm{0x1f83d9ab}, \mathrm{0x5be0cd19})$ — eight values.

**`sha256Round s kw`.** With $t_1 = h + \Sigma_1(e) + \texttt{Ch}(e,f,g) + kw$ and $t_2 = \Sigma_0(a) + \texttt{Maj}(a,b,c)$, the new state is $(t_1 + t_2,\, a,\, b,\, c,\, d + t_1,\, e,\, f,\, g)$. The single argument $kw$ is expected to be the already-summed round constant plus schedule word.

**`be32Words s`.** Groups the byte list into consecutive 4-byte big-endian words; a trailing group of fewer than 4 bytes is **dropped**.

**`sha256Schedule w`.** Starting from $w$, appends 48 words; each new word, at position $t = $ current length, is $\sigma_1(w_{t-2}) + w_{t-7} + \sigma_0(w_{t-15}) + w_{t-16}$, where an out-of-range index reads as $0$ and the subtractions are truncated at $0$. On a 16-word input this yields 64 words.

**`sha256Compress s chunk`.** Form the 64-word schedule from the big-endian words of the chunk; pair it element-wise with `sha256K` by addition (the pairing stops at the shorter list, 64 here); fold `sha256Round` over these 64 sums starting from $s$; return the word-wise sum of $s$ and the folded state.

**`chunks64Aux fuel s`, `chunks64 s`.** Cuts $s$ into successive 64-byte pieces as long as at least 64 bytes remain, with a recursion budget of $\lfloor |s|/64 \rfloor$; any trailing partial piece is silently dropped. On the padded inputs below the length is always a multiple of 64.

**`mdPad be msg`.** Appends the byte $\mathrm{0x80}$, then $z = (119 - (|msg| \bmod 64)) \bmod 64$ zero bytes, then 8 bytes holding $8\cdot|msg|$ (big-endian if $be$, little-endian otherwise; truncated mod $2^{64}$). One checks that $|msg| + 1 + z + 8$ is always a multiple of 64, and that the length field ends the final 64-byte block.

**`be32Bytes`, `le32Bytes`.** A 32-bit word as 4 big-endian, resp. little-endian, bytes.

**`sha256 msg`.** Fold `sha256Compress` over the 64-byte chunks of $\texttt{mdPad}\;\mathrm{true}\;msg$ starting from `sha256Init`; output the 8 state words each as 4 big-endian bytes (32 bytes). Defined for every byte string including the empty one (one chunk).

---

## RIPEMD-160

**Primitives.** $\texttt{rol}(x,n) = (x \ll n)\,|\,(x \gg (32-n))$; $f_1 = x \oplus y \oplus z$; $f_2 = (x \wedge y)\,|\,(\neg x \wedge z)$; $f_3 = (x \,|\, \neg y) \oplus z$; $f_4 = (x \wedge z)\,|\,(y \wedge \neg z)$; $f_5 = x \oplus (y \,|\, \neg z)$.

**`le32Words`.** Like `be32Words` but little-endian within each 4-byte group; trailing partial group dropped.

**Tables.** `ripemdRL`, `ripemdRR` (message-word indices) and `ripemdSL`, `ripemdSR` (rotation amounts) are each lists of **80** natural numbers. The index tables take values in $[0,15]$ (the left one begins $0,1,\dots,15$); the rotation tables take values in $[5,15]$.

**`R5`, `ripemdInit`.** A 5-word state with initial value $(\mathrm{0x67452301}, \mathrm{0xEFCDAB89}, \mathrm{0x98BADCFE}, \mathrm{0x10325476}, \mathrm{0xC3D2E1F0})$.

**Selectors.** By round index $j \in [0,80)$ in blocks of 16: the left line uses $f_1, f_2, f_3, f_4, f_5$ with constants $0, \mathrm{0x5A827999}, \mathrm{0x6ED9EBA1}, \mathrm{0x8F1BBCDC}, \mathrm{0xA953FD4E}$; the right line uses $f_5, f_4, f_3, f_2, f_1$ with constants $\mathrm{0x50A28BE6}, \mathrm{0x5C4DD124}, \mathrm{0x6D703EF3}, \mathrm{0x7A6D76E9}, 0$. The branches are "$j < 16$, $j < 32$, $j < 48$, $j < 64$, else", so $j \ge 80$ would fall in the last group (never reached).

**`ripemdStep s f x k r`.** $a' = \texttt{rol}(a + f + x + k, r) + e$, $c' = \texttt{rol}(c, 10)$, new state $(e,\, a',\, b,\, c',\, d)$.

**`ripemdLine`.** Fold `ripemdStep` over $j = 0, \dots, 79$, with $f = f_{\mathrm{sel}}(j, b, c, d)$ evaluated on the *current* state, message word $w[\texttt{idx}[j]]$ (missing entries read as $0$), constant $k(j)$ and rotation $\texttt{s}[j]$.

**`ripemdCompress s chunk`.** Run the left line and the right line independently from the same $s$ on the little-endian words of the chunk, giving $L$ and $R$; return $(b + L_c + R_d,\; c + L_d + R_e,\; d + L_e + R_a,\; e + L_a + R_b,\; a + L_b + R_c)$.

**`ripemd160 msg`.** Fold `ripemdCompress` over the chunks of $\texttt{mdPad}\;\mathrm{false}\;msg$ (little-endian length) from `ripemdInit`; output the 5 words as little-endian bytes (20 bytes).

---

## SHA-1

**`sha1F t`, `sha1K t`.** By $t$ in blocks of 20: $d \oplus (b \wedge (c \oplus d))$, then $b \oplus c \oplus d$, then $(b \wedge c)\,|\,(d \wedge (b\,|\,c))$, then $b \oplus c \oplus d$; constants $\mathrm{0x5A827999}, \mathrm{0x6ED9EBA1}, \mathrm{0x8F1BBCDC}, \mathrm{0xCA62C1D6}$.

**`sha1Schedule`.** Appends 64 words, each $\texttt{rol}(w_{t-3} \oplus w_{t-8} \oplus w_{t-14} \oplus w_{t-16}, 1)$ with the same out-of-range convention as SHA-256.

**`sha1Compress`.** 80 rounds of $\texttt{temp} = \texttt{rol}(a,5) + \texttt{sha1F}(t,b,c,d) + e + \texttt{sha1K}(t) + w_t$, new state $(\texttt{temp}, a, \texttt{rol}(b,30), c, d)$; then word-wise addition to the input state.

**`sha1 msg`.** Fold over the chunks of $\texttt{mdPad}\;\mathrm{true}\;msg$ starting from **`ripemdInit`** (the RIPEMD-160 initial-value constant is reused as the SHA-1 initial state; the five values are the same numbers); output 5 words big-endian (20 bytes). No other declaration in the file refers to `sha1`.

---

## Composite hashes

**`hash256 m`** $= \texttt{sha256}(\texttt{sha256}(m))$ (32 bytes). **`hash160 m`** $= \texttt{ripemd160}(\texttt{sha256}(m))$ (20 bytes). **`txid tx`** $= \texttt{hash256}(\texttt{serTx}\;\mathrm{false}\;tx)$ — the witness-free serialization is hashed whether or not the transaction has witnesses. **`wtxid tx`** $= \texttt{hash256}(\texttt{serTx}\;\mathrm{true}\;tx)$ if $\texttt{hasWitness}(tx)$, else $\texttt{txid}(tx)$. **`headerHash h`** $= \texttt{hash256}(\texttt{serHeader}\;h)$.

---

## Weights

**Constants.** $\texttt{WITNESS\_SCALE\_FACTOR} = 4$; $\texttt{MAX\_BLOCK\_WEIGHT} = \texttt{MAX\_BLOCK\_SERIALIZED\_SIZE} = 4\,000\,000$ (the latter two are not used elsewhere in the file).

**`txWeight tx`** $= 3\cdot|\texttt{serTx}\;\mathrm{false}\;tx| + |\texttt{serTx}\;\mathrm{true}\;tx|$ (the factor is $\texttt{WITNESS\_SCALE\_FACTOR} - 1$ in natural-number subtraction, i.e. $3$). **`blockWeight b`** is the same with `serBlock`.

---

## Genesis constants

**`genesisScriptSig`.** A literal list of **77** bytes: $\mathrm{04\,ff\,ff\,00\,1d\,01\,04\,45}$ followed by the 69 ASCII bytes of the text "The Times 03/Jan/2009 Chancellor on brink of second bailout for banks".

**`genesisOutputScript`.** A literal list of **67** bytes: $\mathrm{0x41}$, then 65 bytes beginning $\mathrm{0x04}$, then $\mathrm{0xac}$.

**`genesisCoinbase`.** The transaction with version $1$; one input whose previous outpoint is (32 zero bytes, $\mathrm{0xffffffff}$), whose script is `genesisScriptSig`, sequence $\mathrm{0xffffffff}$, witness $[\,]$; one output with value $5\,000\,000\,000$ and script `genesisOutputScript`; lock time $0$. Its witness-free serialization has $4 + 1 + (32+4+1+77+4) + 1 + (8+1+67) + 4 = 204$ bytes.

**`genesisHeader`.** Version $1$; previous block 32 zero bytes; merkle root **defined as $\texttt{txid}(\texttt{genesisCoinbase})$** (a computed value, not the literal `genesisMerkleRoot` below); time $1231006505$; bits $\mathrm{0x1d00ffff}$; nonce $2083236893$.

**`genesisBlock`.** The block with `genesisHeader` and the single transaction `genesisCoinbase`.

**`genesisHash`.** A literal list of **32** bytes beginning $\mathrm{6f\,e2\,8c\,0a}$ and ending with five zero bytes.

**`genesisMerkleRoot`.** A literal list of **32** bytes beginning $\mathrm{3b\,a3\,ed\,fd}$ and ending $\mathrm{1e\,5e\,4a}$.

---

## Points a reader may wish to note

- Range-checked counts accept $v = \texttt{MAX\_SIZE}$ (the test is strict $\texttt{MAX\_SIZE} < v$), and the well-formedness predicates use $\le \texttt{MAX\_SIZE}$ accordingly.
- In `readTx`, when the first input list is empty and $aw$ is true, the next byte is always consumed as a flags byte; if it is $0$ the output list is set to $[\,]$ without being read.
- `Block.wf` requires every transaction to have an input (the disjunct about witnesses is implied by the other), in both serialization modes.
- `Tx.version` is unsigned and read unsigned; `Header.version` is signed and read signed.
- Hash fields of outpoints and headers are serialized raw with no length check; only `wf` ties them to 32 bytes.
- All fixed-width encoders truncate rather than fail; `serInt64`/`serInt32` wrap outside the signed range.
- `sha1` uses `ripemdInit` as its initial value and is not referenced by anything else.
- `chunks64` and `be32Words`/`le32Words` drop trailing partial groups silently; `mdPad` always produces a multiple of 64 bytes, so this never triggers inside the hash functions.
