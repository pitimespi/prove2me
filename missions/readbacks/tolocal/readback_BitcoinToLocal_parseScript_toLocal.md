# Read-back: `BitcoinToLocal.parseScript_toLocal`

**Statement.** For all byte strings $R$ (named `rev`) and $D$ (named `dpk`) and every integer $\delta$ (named `delay`), under the hypotheses

$$
|R| \le 520, \qquad |D| \le 520, \qquad |\delta| < 2^{32}
$$

($520$ is the preamble's `MAX_SCRIPT_ELEMENT_SIZE`; $|\delta|$ is the absolute value as a natural),

$$
\mathrm{parseScript}\big(\mathrm{toLocalBytes}(R, \delta, D)\big) \;=\; \mathrm{some}\big(\mathrm{toLocalScript}(R, \delta, D)\big).
$$

That is, byte-level parsing of the serialized script succeeds (does not return "none") and yields exactly the nine-instruction parsed script.

**The two sides.**

$\mathrm{toLocalBytes}(R, \delta, D)$ is the byte string

$$
[\mathtt{0x63}] \mathbin{+\!\!+} \mathrm{pushBytes}(R) \mathbin{+\!\!+} [\mathtt{0x67}] \mathbin{+\!\!+} \mathrm{numBytes}(\delta) \mathbin{+\!\!+} [\mathtt{0xb2}, \mathtt{0x75}] \mathbin{+\!\!+} \mathrm{pushBytes}(D) \mathbin{+\!\!+} [\mathtt{0x68}, \mathtt{0xac}],
$$

where $\mathrm{pushBytes}(d)$ is: for $|d| < 76$, the byte $|d|$ then $d$; for $76 \le |d| \le 255$, bytes $\mathtt{0x4c}, |d|$ then $d$; for $256 \le |d| \le 65535$, byte $\mathtt{0x4d}$, the 2-byte little-endian $|d|$, then $d$; otherwise $\mathtt{0x4e}$, the 4-byte little-endian $|d|$, then $d$. And $\mathrm{numBytes}(\delta)$ is the single byte $\delta + 80$ (i.e. $\mathtt{0x4f}$ for $\delta = -1$, $\mathtt{0x51}\ldots\mathtt{0x60}$ for $\delta = 1,\ldots,16$) when $\delta = -1$ or $1 \le \delta \le 16$, and $\mathrm{pushBytes}(\mathrm{serialize}(\delta))$ otherwise, with $\mathrm{serialize}$ the script-number encoding ($\mathrm{serialize}(0) = [\,]$, so $\mathrm{numBytes}(0) = [\mathtt{0x00}]$; for $\delta \ne 0$ the little-endian magnitude bytes of $|\delta|$ without trailing zeros, with an appended $\mathtt{0x80}$/$\mathtt{0x00}$ byte if the top bit of the last byte is set, else the top bit set on the last byte when $\delta<0$).

$\mathrm{toLocalScript}(R, \delta, D)$ is the instruction list

$$
[\ \mathrm{op}\,\mathtt{0x63},\ \mathrm{push}\,R,\ \mathrm{op}\,\mathtt{0x67},\ \mathrm{numInstr}(\delta),\ \mathrm{op}\,\mathtt{0xb2},\ \mathrm{op}\,\mathtt{0x75},\ \mathrm{push}\,D,\ \mathrm{op}\,\mathtt{0x68},\ \mathrm{op}\,\mathtt{0xac}\ ],
$$

where $\mathrm{numInstr}(\delta)$ is the opcode with byte $\delta + 80$ when $\delta = -1$ or $1 \le \delta \le 16$, and the data push of $\mathrm{serialize}(\delta)$ otherwise (the empty push for $\delta = 0$).

**The parser.** $\mathrm{parseScript}(s)$ runs a fuel-bounded loop (fuel $= |s|$) that repeatedly applies $\mathrm{getOp}$ and collects the instructions: on the empty string it returns $\mathrm{some}\,[\,]$; if the fuel is exhausted on a non-empty string it returns $\mathrm{none}$; if $\mathrm{getOp}$ fails it returns $\mathrm{none}$; otherwise it prepends the instruction and continues on the remainder. $\mathrm{getOp}(s)$ on the empty string is $\mathrm{none}$; on $c :: r$ with $c$ read as a natural: if $c \le \mathtt{0x4e}$ ($=78$) it is a push whose size is $c$ itself when $c < \mathtt{0x4c}$; the next byte when $c = \mathtt{0x4c}$ ($\mathrm{none}$ if $r$ is empty); the little-endian value of the next two bytes when $c = \mathtt{0x4d}$ ($\mathrm{none}$ if fewer than two); the little-endian value of the next four bytes when $c = \mathtt{0x4e}$ ($\mathrm{none}$ if fewer than four); then, with the size bytes consumed, if fewer than that many bytes remain the result is $\mathrm{none}$, else the instruction is the push of exactly that many bytes and the remainder follows. If $c > \mathtt{0x4e}$ the instruction is the opcode $c$ with remainder $r$ (any such byte, including $\mathtt{0x4f}$ and $\mathtt{0x51}$–$\mathtt{0x60}$, is returned as an opcode instruction).

**Hypotheses.** The size bounds on $R$ and $D$ and the magnitude bound on $\delta$ are the only assumptions; nothing else about the contents of $R$, $D$ is assumed, and $\delta$ may be negative or zero.
