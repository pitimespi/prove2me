#!/usr/bin/env python3
"""Differential test generator: Bitcoin Core's `src/test/data/script_tests.json` (revision
a773e1e33b349dc819b5a0edc1c7a4839dc73b48) against the Lean transcription of `VerifyScript`
(`BitcoinTaproot.verifyScriptFull`).

Run with `python3 -I core_script_tests.py <script_tests.json> <out dir>`; it emits
`CoreScriptTests<k>.lean` files (one `#eval` per included test, printing `true` iff the Lean verdict
equals Core's expected success/failure) and a `core_script_tests.index.json` with the metadata of every
included test (for the summary).

Harness semantics reproduced here (src/test/script_tests.cpp):
  * Core's `ParseScript` assembly: decimal numbers -> `CScript << int64_t` (OP_0, OP_1NEGATE,
    OP_1..OP_16, otherwise the minimal push of `CScriptNum::serialize`); `0x..` raw bytes inserted as-is;
    `'...'` strings pushed as data; opcode names with or without the `OP_` prefix (`OP_RESERVED` and
    `OP_NOP`..`OP_CHECKSIGADD`).
  * Witness elements are hex, except `#SCRIPT# <assembly>` (a tapscript, pushed as its bytes) and
    `#CONTROLBLOCK#` (the control block of the preceding script as the only leaf of a Taproot tree with
    internal key `XOnlyPubKey::NUMS_H`); `#TAPROOTOUTPUT#` in the scriptPubKey is the resulting output
    key. The last element of the witness array is the amount in BTC.
  * Crediting transaction: version 1, one input (null prevout, scriptSig `OP_0 OP_0`, nSequence final),
    one output (amount, scriptPubKey), locktime 0. Spending transaction: version 1, one input spending
    output 0 of the crediting transaction with the scriptSig and witness, nSequence final, one output
    (amount, empty script), locktime 0.
  * `VerifyScript(scriptSig, scriptPubKey, &witness, flags, checker(spending tx, 0, amount))`.

Inclusion rule (the Lean models consensus flags only: P2SH, WITNESS, TAPROOT, DERSIG, CLTV, CSV,
NULLDUMMY): a test is included iff its flag set is a subset of the consensus flags, or its expected
result is OK. Flags only add failure conditions (Core's own harness asserts that removing flags from a
passing test keeps it passing), so an OK test under more flags is OK under the consensus subset; a
failing test whose flags include a policy flag may fail because of that flag, so it is skipped.
"""
import hashlib
import json
import os
import struct
import sys
from decimal import Decimal

# --- opcode table (script/script.h at the pinned revision) -------------------------------------
OP_NAMES = {
    'OP_RESERVED': 0x50,
    'OP_NOP': 0x61, 'OP_VER': 0x62, 'OP_IF': 0x63, 'OP_NOTIF': 0x64, 'OP_VERIF': 0x65, 'OP_VERNOTIF': 0x66,
    'OP_ELSE': 0x67, 'OP_ENDIF': 0x68, 'OP_VERIFY': 0x69, 'OP_RETURN': 0x6a,
    'OP_TOALTSTACK': 0x6b, 'OP_FROMALTSTACK': 0x6c, 'OP_2DROP': 0x6d, 'OP_2DUP': 0x6e, 'OP_3DUP': 0x6f,
    'OP_2OVER': 0x70, 'OP_2ROT': 0x71, 'OP_2SWAP': 0x72, 'OP_IFDUP': 0x73, 'OP_DEPTH': 0x74, 'OP_DROP': 0x75,
    'OP_DUP': 0x76, 'OP_NIP': 0x77, 'OP_OVER': 0x78, 'OP_PICK': 0x79, 'OP_ROLL': 0x7a, 'OP_ROT': 0x7b,
    'OP_SWAP': 0x7c, 'OP_TUCK': 0x7d,
    'OP_CAT': 0x7e, 'OP_SUBSTR': 0x7f, 'OP_LEFT': 0x80, 'OP_RIGHT': 0x81, 'OP_SIZE': 0x82,
    'OP_INVERT': 0x83, 'OP_AND': 0x84, 'OP_OR': 0x85, 'OP_XOR': 0x86, 'OP_EQUAL': 0x87, 'OP_EQUALVERIFY': 0x88,
    'OP_RESERVED1': 0x89, 'OP_RESERVED2': 0x8a,
    'OP_1ADD': 0x8b, 'OP_1SUB': 0x8c, 'OP_2MUL': 0x8d, 'OP_2DIV': 0x8e, 'OP_NEGATE': 0x8f, 'OP_ABS': 0x90,
    'OP_NOT': 0x91, 'OP_0NOTEQUAL': 0x92, 'OP_ADD': 0x93, 'OP_SUB': 0x94, 'OP_MUL': 0x95, 'OP_DIV': 0x96,
    'OP_MOD': 0x97, 'OP_LSHIFT': 0x98, 'OP_RSHIFT': 0x99, 'OP_BOOLAND': 0x9a, 'OP_BOOLOR': 0x9b,
    'OP_NUMEQUAL': 0x9c, 'OP_NUMEQUALVERIFY': 0x9d, 'OP_NUMNOTEQUAL': 0x9e, 'OP_LESSTHAN': 0x9f,
    'OP_GREATERTHAN': 0xa0, 'OP_LESSTHANOREQUAL': 0xa1, 'OP_GREATERTHANOREQUAL': 0xa2, 'OP_MIN': 0xa3,
    'OP_MAX': 0xa4, 'OP_WITHIN': 0xa5,
    'OP_RIPEMD160': 0xa6, 'OP_SHA1': 0xa7, 'OP_SHA256': 0xa8, 'OP_HASH160': 0xa9, 'OP_HASH256': 0xaa,
    'OP_CODESEPARATOR': 0xab, 'OP_CHECKSIG': 0xac, 'OP_CHECKSIGVERIFY': 0xad, 'OP_CHECKMULTISIG': 0xae,
    'OP_CHECKMULTISIGVERIFY': 0xaf,
    'OP_NOP1': 0xb0, 'OP_CHECKLOCKTIMEVERIFY': 0xb1, 'OP_CHECKSEQUENCEVERIFY': 0xb2, 'OP_NOP4': 0xb3,
    'OP_NOP5': 0xb4, 'OP_NOP6': 0xb5, 'OP_NOP7': 0xb6, 'OP_NOP8': 0xb7, 'OP_NOP9': 0xb8, 'OP_NOP10': 0xb9,
    'OP_CHECKSIGADD': 0xba,
}
for _k in list(OP_NAMES):
    OP_NAMES[_k[3:]] = OP_NAMES[_k]   # "ADD" as well as "OP_ADD"


def scriptnum_serialize(v):
    """`CScriptNum::serialize`."""
    if v == 0:
        return b''
    neg = v < 0
    a = abs(v)
    out = bytearray()
    while a:
        out.append(a & 0xff)
        a >>= 8
    if out[-1] & 0x80:
        out.append(0x80 if neg else 0)
    elif neg:
        out[-1] |= 0x80
    return bytes(out)


def push_data(b):
    """`CScript::operator<<(const std::vector<unsigned char>&)`: the minimal push opcode."""
    n = len(b)
    if n < 0x4c:
        return bytes([n]) + b
    if n <= 0xff:
        return b'\x4c' + bytes([n]) + b
    if n <= 0xffff:
        return b'\x4d' + struct.pack('<H', n) + b
    return b'\x4e' + struct.pack('<I', n) + b


def push_int64(v):
    """`CScript::push_int64`."""
    if v == -1 or 1 <= v <= 16:
        return bytes([v + 0x50])
    if v == 0:
        return b'\x00'
    return push_data(scriptnum_serialize(v))


def is_hex(s):
    return len(s) > 0 and len(s) % 2 == 0 and all(c in '0123456789abcdefABCDEF' for c in s)


def parse_script(s):
    """`ParseScript` of src/core_read.cpp."""
    out = b''
    for w in s.replace('\t', ' ').replace('\n', ' ').split(' '):
        if w == '':
            continue
        if (w.isascii() and w.isdigit()) or (w[0] == "-" and len(w) > 1 and w[1:].isascii() and w[1:].isdigit()):
            v = int(w)
            if v > 0xffffffff or v < -0xffffffff:
                raise ValueError('decimal out of range: ' + w)
            out += push_int64(v)
        elif w[:2] == '0x' and len(w) > 2 and is_hex(w[2:]):
            out += bytes.fromhex(w[2:])
        elif len(w) >= 2 and w[0] == "'" and w[-1] == "'":
            out += push_data(w[1:-1].encode('latin-1'))
        elif w in OP_NAMES:
            out += bytes([OP_NAMES[w]])
        else:
            raise ValueError('unknown opcode: ' + w)
    return out


# --- flags ---------------------------------------------------------------------------------------
CONSENSUS_FLAGS = {'P2SH', 'WITNESS', 'TAPROOT', 'DERSIG', 'CHECKLOCKTIMEVERIFY', 'CHECKSEQUENCEVERIFY', 'NULLDUMMY'}
ALL_FLAGS = CONSENSUS_FLAGS | {
    'STRICTENC', 'LOW_S', 'SIGPUSHONLY', 'MINIMALDATA', 'DISCOURAGE_UPGRADABLE_NOPS', 'CLEANSTACK',
    'MINIMALIF', 'NULLFAIL', 'DISCOURAGE_UPGRADABLE_WITNESS_PROGRAM', 'WITNESS_PUBKEYTYPE', 'CONST_SCRIPTCODE',
    'DISCOURAGE_UPGRADABLE_TAPROOT_VERSION', 'DISCOURAGE_OP_SUCCESS', 'DISCOURAGE_UPGRADABLE_PUBKEYTYPE'}
FLAG_ORDER = ['P2SH', 'WITNESS', 'TAPROOT', 'DERSIG', 'CHECKLOCKTIMEVERIFY', 'CHECKSEQUENCEVERIFY', 'NULLDUMMY']


def parse_flags(s):
    """`ParseScriptFlags`: the set of named flags ('' and 'NONE' are the empty set)."""
    if s == '' or s == 'NONE':
        return set()
    fl = set(s.split(','))
    for f in fl:
        if f not in ALL_FLAGS:
            raise ValueError('unknown flag ' + f)
    return fl


def lean_flags(fl):
    """The `BitcoinActivation.ScriptFlags` literal (p2sh, witness, taproot, dersig, cltv, csv, nulldummy)."""
    return '(fl ' + ' '.join('true' if f in fl else 'false' for f in FLAG_ORDER) + ')'


# --- hashing, transactions -------------------------------------------------------------------------
def sha256(b):
    return hashlib.sha256(b).digest()


def sha256d(b):
    return sha256(sha256(b))


def compact_size(n):
    if n < 253:
        return bytes([n])
    if n <= 0xffff:
        return b'\xfd' + struct.pack('<H', n)
    if n <= 0xffffffff:
        return b'\xfe' + struct.pack('<I', n)
    return b'\xff' + struct.pack('<Q', n)


def ser_bytes(b):
    return compact_size(len(b)) + b


def ser_tx_no_witness(version, vin, vout, locktime):
    """`SerializeTransaction` without witness: vin = [(hash, n, scriptSig, seq)], vout = [(value, spk)]."""
    s = struct.pack('<I', version) + compact_size(len(vin))
    for h, n, sig, seq in vin:
        s += h + struct.pack('<I', n) + ser_bytes(sig) + struct.pack('<I', seq)
    s += compact_size(len(vout))
    for v, spk in vout:
        s += struct.pack('<q', v) + ser_bytes(spk)
    return s + struct.pack('<I', locktime)


def crediting_txid(script_pubkey, amount):
    """`BuildCreditingTransaction(scriptPubKey, nValue).GetHash()` (internal byte order)."""
    vin = [(b'\x00' * 32, 0xffffffff, b'\x00\x00', 0xffffffff)]
    return sha256d(ser_tx_no_witness(1, vin, [(amount, script_pubkey)], 0))


# --- Taproot (for the #CONTROLBLOCK# / #TAPROOTOUTPUT# tests) ----------------------------------------
P = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
G = (0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798,
     0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8)
NUMS_H = bytes.fromhex('50929b74c1a04954b78b4b6035e97a5e078a5a0f28ec96d547bfee9ace803ac0')


def padd(a, b):
    if a is None:
        return b
    if b is None:
        return a
    if a[0] == b[0] and (a[1] + b[1]) % P == 0:
        return None
    if a == b:
        l = 3 * a[0] * a[0] * pow(2 * a[1], P - 2, P) % P
    else:
        l = (b[1] - a[1]) * pow(b[0] - a[0], P - 2, P) % P
    x = (l * l - a[0] - b[0]) % P
    return (x, (l * (a[0] - x) - a[1]) % P)


def pmul(k, pt):
    r = None
    while k:
        if k & 1:
            r = padd(r, pt)
        pt = padd(pt, pt)
        k >>= 1
    return r


def lift_x(xb):
    x = int.from_bytes(xb, 'big')
    y = pow((x * x * x + 7) % P, (P + 1) // 4, P)
    assert y * y % P == (x * x * x + 7) % P
    return (x, y if y % 2 == 0 else P - y)


def tagged(tag, m):
    t = sha256(tag.encode())
    return sha256(t + t + m)


def taproot_single_leaf(script):
    """`TaprootBuilder().Add(0, script, 0xc0).Finalize(NUMS_H)`: (output key, control block)."""
    leaf = tagged('TapLeaf', b'\xc0' + ser_bytes(script))
    p = lift_x(NUMS_H)
    t = int.from_bytes(tagged('TapTweak', NUMS_H + leaf), 'big')
    assert t < N
    q = padd(p, pmul(t, G))
    parity = q[1] & 1
    return q[0].to_bytes(32, 'big'), bytes([0xc0 | parity]) + NUMS_H


# --- the JSON ----------------------------------------------------------------------------------------
def load_tests(path):
    with open(path) as f:
        return json.load(f, parse_float=Decimal)


def amount_from_value(v):
    """`AmountFromValue`: BTC with at most 8 decimals, as satoshis."""
    d = Decimal(v) if not isinstance(v, Decimal) else v
    sat = d * 100000000
    assert sat == sat.to_integral_value(), v
    return int(sat)


def translate(entry):
    """One JSON entry -> dict with bytes, or None for a comment line."""
    if len(entry) < 2:
        return None
    pos = 0
    witness = []
    amount = 0
    taproot_output = None
    if isinstance(entry[0], list):
        arr = entry[0]
        for el in arr[:-1]:
            if el.startswith('#SCRIPT#'):
                witness.append(parse_script(el[len('#SCRIPT#'):]))
            elif el == '#CONTROLBLOCK#':
                taproot_output, control = taproot_single_leaf(witness[-1])
                witness.append(control)
            else:
                witness.append(bytes.fromhex(el))
        amount = amount_from_value(arr[-1])
        pos = 1
    script_sig_s = entry[pos]
    script_pubkey_s = entry[pos + 1]
    if '#TAPROOTOUTPUT#' in script_pubkey_s:
        assert taproot_output is not None
        script_pubkey_s = script_pubkey_s.replace('#TAPROOTOUTPUT#', '0x' + taproot_output.hex())
    flags = parse_flags(entry[pos + 2])
    expected = entry[pos + 3]
    comment = entry[pos + 4] if len(entry) > pos + 4 else ''
    return {
        'scriptSig': parse_script(script_sig_s),
        'scriptPubKey': parse_script(script_pubkey_s),
        'witness': witness,
        'amount': amount,
        'flags': flags,
        'expected': expected,
        'comment': comment,
        'raw': entry,
    }


def included(t):
    return t['expected'] == 'OK' or t['flags'] <= CONSENSUS_FLAGS


HEADER = '''import Definitions.Def_BitcoinTaproot
open BitcoinSer BitcoinSig BitcoinVerify BitcoinTaproot

/-! Generated by tests/reference/core_script_tests.py from Bitcoin Core's src/test/data/script_tests.json
(revision a773e1e33b349dc819b5a0edc1c7a4839dc73b48). Each `#eval` prints `true` iff the Lean
`verifyScriptFull` agrees with Core's expected success/failure. Tests whose flags include a policy flag
are included only when their expected result is OK (see the generator's docstring). -/

def hexVal (c : Char) : Nat := if c.isDigit then c.toNat - 48 else c.toLower.toNat - 87
def ofHexL : List Char → Bytes
  | a :: b :: r => BitVec.ofNat 8 (hexVal a * 16 + hexVal b) :: ofHexL r
  | _ => []
def ofHex (s : String) : Bytes := ofHexL s.toList
/-- `⟨p2sh, witness, taproot, dersig, cltv, csv, nulldummy⟩`. -/
def fl (p w t d c s n : Bool) : BitcoinActivation.ScriptFlags := ⟨p, w, t, d, c, s, n⟩
/-- `BuildSpendingTransaction`: version 1, one input spending output 0 of the crediting transaction
(whose txid is `prev`, internal byte order), nSequence final, one output of `amount` with an empty
script, locktime 0. -/
def spendTx (prev : String) (sig : Bytes) (wit : List Bytes) (amount : Int) : Tx :=
  ⟨1, [⟨⟨ofHex prev, 0⟩, sig, 0xffffffff, wit⟩], [⟨amount, []⟩], 0⟩
/-- `VerifyScript(scriptSig, scriptPubKey, &witness, flags, checker(spending tx, 0, amount))`. -/
def run (f : BitcoinActivation.ScriptFlags) (prev sigH spkH : String) (witH : List String) (amount : Int) : Bool :=
  let sig := ofHex sigH
  let spk := ofHex spkH
  let wit := witH.map ofHex
  verifyScriptFull [⟨amount, spk⟩] ⟨f, spendTx prev sig wit amount, 0, amount⟩ sig spk wit

'''


def lean_str(s):
    return '"' + s + '"'


def emit(tests, out_dir, per_file):
    files = []
    index = []
    chunk = []
    for k, t in enumerate(tests):
        prev = crediting_txid(t['scriptPubKey'], t['amount'])
        comment = t['comment'].replace('\n', ' ').replace('\r', ' ')
        line = '#eval run %s %s %s %s [%s] %d == %s   -- #%d %s' % (
            lean_flags(t['flags']), lean_str(prev.hex()), lean_str(t['scriptSig'].hex()),
            lean_str(t['scriptPubKey'].hex()), ', '.join(lean_str(w.hex()) for w in t['witness']),
            t['amount'], 'true' if t['expected'] == 'OK' else 'false', t['id'], comment)
        chunk.append(line)
        index.append({'id': t['id'], 'file': len(files) + 1, 'expected': t['expected'],
                      'flags': sorted(t['flags']), 'comment': t['comment']})
        if len(chunk) == per_file or k == len(tests) - 1:
            name = 'CoreScriptTests%d.lean' % (len(files) + 1)
            with open(os.path.join(out_dir, name), 'w') as f:
                f.write(HEADER + '\n'.join(chunk) + '\n')
            files.append(name)
            chunk = []
    with open(os.path.join(out_dir, 'reference', 'core_script_tests.index.json'), 'w') as f:
        json.dump({'files': files, 'tests': index}, f, indent=0, default=str)
    return files


def main():
    src = sys.argv[1] if len(sys.argv) > 1 else '/tmp/claude-0/coretests/script_tests.json'
    out_dir = sys.argv[2] if len(sys.argv) > 2 else os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
    per_file = int(sys.argv[3]) if len(sys.argv) > 3 else 160
    data = load_tests(src)
    total = 0
    inc = []
    skipped = []
    for i, e in enumerate(data):
        t = translate(e)
        if t is None:
            continue
        total += 1
        t['id'] = i
        if included(t):
            inc.append(t)
        else:
            skipped.append(t)
    files = emit(inc, out_dir, per_file)
    print('total %d, included %d, skipped %d (expected failure with policy flags)' % (total, len(inc), len(skipped)))
    from collections import Counter
    print('skipped by flag set:', Counter(','.join(sorted(t['flags'])) for t in skipped).most_common())
    print('included with policy flags (expected OK):', sum(1 for t in inc if not t['flags'] <= CONSENSUS_FLAGS))
    print('files:', files)


if __name__ == '__main__':
    main()
