#!/usr/bin/env python3
"""Second (independent) review reference for the script layer, written from Bitcoin Core
script/interpreter.cpp, script/script.{h,cpp} and pubkey.cpp at a773e1e33b349dc819b5a0edc1c7a4839dc73b48,
never from the Lean.  It transcribes CScriptNum, CastToBool, GetScriptOp, EvalScript (BASE,
WITNESS_V0, TAPSCRIPT), SignatureHash (legacy and BIP143), SignatureHashSchnorr, the two signature
checkers, VerifyWitnessProgram, ExecuteWitnessScript and VerifyScript, with the mainnet consensus
flag set (P2SH, WITNESS, TAPROOT, DERSIG, CLTV, CSV, NULLDUMMY; everything else is policy and off).

Running this file writes tests/SecondReviewScriptVectors.lean (spot 1: EvalScript on parsed
instructions against an abstract oracle).  second_verify_reference.py and second_taproot_reference.py
import it for spots 7 and 8.  Run with `python3 -I`.
"""
import hashlib, struct, os, sys

# ----------------------------------------------------------------------------------------------
# script/script.h constants
MAX_SCRIPT_ELEMENT_SIZE = 520
MAX_OPS_PER_SCRIPT = 201
MAX_PUBKEYS_PER_MULTISIG = 20
MAX_SCRIPT_SIZE = 10000
MAX_STACK_SIZE = 1000
LOCKTIME_THRESHOLD = 500000000
ANNEX_TAG = 0x50
VALIDATION_WEIGHT_PER_SIGOP_PASSED = 50
VALIDATION_WEIGHT_OFFSET = 50
SEQUENCE_FINAL = 0xffffffff
SEQUENCE_LOCKTIME_DISABLE_FLAG = 1 << 31
SEQUENCE_LOCKTIME_TYPE_FLAG = 1 << 22
SEQUENCE_LOCKTIME_MASK = 0x0000ffff
# interpreter.h
WITNESS_V0_SCRIPTHASH_SIZE = 32
WITNESS_V0_KEYHASH_SIZE = 20
WITNESS_V1_TAPROOT_SIZE = 32
TAPROOT_LEAF_MASK = 0xfe
TAPROOT_LEAF_TAPSCRIPT = 0xc0
TAPROOT_CONTROL_BASE_SIZE = 33
TAPROOT_CONTROL_NODE_SIZE = 32
TAPROOT_CONTROL_MAX_NODE_COUNT = 128
TAPROOT_CONTROL_MAX_SIZE = TAPROOT_CONTROL_BASE_SIZE + TAPROOT_CONTROL_NODE_SIZE * TAPROOT_CONTROL_MAX_NODE_COUNT
SIGHASH_ALL, SIGHASH_NONE, SIGHASH_SINGLE, SIGHASH_ANYONECANPAY = 1, 2, 3, 0x80
SIGHASH_DEFAULT, SIGHASH_OUTPUT_MASK, SIGHASH_INPUT_MASK = 0, 3, 0x80

# opcodes
OP_0 = 0x00; OP_PUSHDATA1 = 0x4c; OP_PUSHDATA2 = 0x4d; OP_PUSHDATA4 = 0x4e; OP_1NEGATE = 0x4f
OP_RESERVED = 0x50; OP_1 = 0x51; OP_16 = 0x60; OP_NOP = 0x61; OP_VER = 0x62; OP_IF = 0x63
OP_NOTIF = 0x64; OP_VERIF = 0x65; OP_VERNOTIF = 0x66; OP_ELSE = 0x67; OP_ENDIF = 0x68
OP_VERIFY = 0x69; OP_RETURN = 0x6a; OP_TOALTSTACK = 0x6b; OP_FROMALTSTACK = 0x6c; OP_2DROP = 0x6d
OP_2DUP = 0x6e; OP_3DUP = 0x6f; OP_2OVER = 0x70; OP_2ROT = 0x71; OP_2SWAP = 0x72; OP_IFDUP = 0x73
OP_DEPTH = 0x74; OP_DROP = 0x75; OP_DUP = 0x76; OP_NIP = 0x77; OP_OVER = 0x78; OP_PICK = 0x79
OP_ROLL = 0x7a; OP_ROT = 0x7b; OP_SWAP = 0x7c; OP_TUCK = 0x7d; OP_CAT = 0x7e; OP_SUBSTR = 0x7f
OP_LEFT = 0x80; OP_RIGHT = 0x81; OP_SIZE = 0x82; OP_INVERT = 0x83; OP_AND = 0x84; OP_OR = 0x85
OP_XOR = 0x86; OP_EQUAL = 0x87; OP_EQUALVERIFY = 0x88; OP_RESERVED1 = 0x89; OP_RESERVED2 = 0x8a
OP_1ADD = 0x8b; OP_1SUB = 0x8c; OP_2MUL = 0x8d; OP_2DIV = 0x8e; OP_NEGATE = 0x8f; OP_ABS = 0x90
OP_NOT = 0x91; OP_0NOTEQUAL = 0x92; OP_ADD = 0x93; OP_SUB = 0x94; OP_MUL = 0x95; OP_DIV = 0x96
OP_MOD = 0x97; OP_LSHIFT = 0x98; OP_RSHIFT = 0x99; OP_BOOLAND = 0x9a; OP_BOOLOR = 0x9b
OP_NUMEQUAL = 0x9c; OP_NUMEQUALVERIFY = 0x9d; OP_NUMNOTEQUAL = 0x9e; OP_LESSTHAN = 0x9f
OP_GREATERTHAN = 0xa0; OP_LESSTHANOREQUAL = 0xa1; OP_GREATERTHANOREQUAL = 0xa2; OP_MIN = 0xa3
OP_MAX = 0xa4; OP_WITHIN = 0xa5; OP_RIPEMD160 = 0xa6; OP_SHA1 = 0xa7; OP_SHA256 = 0xa8
OP_HASH160 = 0xa9; OP_HASH256 = 0xaa; OP_CODESEPARATOR = 0xab; OP_CHECKSIG = 0xac
OP_CHECKSIGVERIFY = 0xad; OP_CHECKMULTISIG = 0xae; OP_CHECKMULTISIGVERIFY = 0xaf; OP_NOP1 = 0xb0
OP_CHECKLOCKTIMEVERIFY = 0xb1; OP_CHECKSEQUENCEVERIFY = 0xb2; OP_NOP4 = 0xb3; OP_NOP5 = 0xb4
OP_NOP6 = 0xb5; OP_NOP7 = 0xb6; OP_NOP8 = 0xb7; OP_NOP9 = 0xb8; OP_NOP10 = 0xb9; OP_CHECKSIGADD = 0xba
OP_INVALIDOPCODE = 0xff

DISABLED = {OP_CAT, OP_SUBSTR, OP_LEFT, OP_RIGHT, OP_INVERT, OP_AND, OP_OR, OP_XOR, OP_2MUL, OP_2DIV,
            OP_MUL, OP_DIV, OP_MOD, OP_LSHIFT, OP_RSHIFT}

BASE, WITNESS_V0, TAPROOT, TAPSCRIPT = 0, 1, 2, 3
CONSENSUS_FLAGS = frozenset({'P2SH', 'WITNESS', 'TAPROOT', 'DERSIG', 'CLTV', 'CSV', 'NULLDUMMY'})


class ScriptError(Exception):
    """set_error(serror, X): the script fails with error X."""
    def __init__(self, code):
        super().__init__(code); self.code = code


class ScriptNumError(Exception):
    pass


# ----------------------------------------------------------------------------------------------
# CScriptNum
def scriptnum_decode(vch, require_minimal=False, max_size=4):
    if len(vch) > max_size:
        raise ScriptNumError("script number overflow")
    if require_minimal and len(vch) > 0:
        if (vch[-1] & 0x7f) == 0:
            if len(vch) <= 1 or (vch[-2] & 0x80) == 0:
                raise ScriptNumError("non-minimally encoded script number")
    if len(vch) == 0:
        return 0
    result = int.from_bytes(vch, 'little')
    if vch[-1] & 0x80:
        return -(result & ~(0x80 << (8 * (len(vch) - 1))))
    return result


def scriptnum_encode(value):
    if value == 0:
        return b''
    neg = value < 0
    absvalue = -value if neg else value
    result = bytearray()
    while absvalue:
        result.append(absvalue & 0xff); absvalue >>= 8
    if result[-1] & 0x80:
        result.append(0x80 if neg else 0)
    elif neg:
        result[-1] |= 0x80
    return bytes(result)


def getint(v):
    """CScriptNum::getint: clamp to the int range."""
    return max(-2**31, min(2**31 - 1, v))


def cast_to_bool(vch):
    for i in range(len(vch)):
        if vch[i] != 0:
            if i == len(vch) - 1 and vch[i] == 0x80:
                return False
            return True
    return False


# ----------------------------------------------------------------------------------------------
# GetScriptOp
def get_op(script, pc):
    """Returns (ok, pc', opcode, data)."""
    if pc >= len(script):
        return False, pc, OP_INVALIDOPCODE, b''
    opcode = script[pc]; pc += 1
    data = b''
    if opcode <= OP_PUSHDATA4:
        if opcode < OP_PUSHDATA1:
            n = opcode
        elif opcode == OP_PUSHDATA1:
            if len(script) - pc < 1: return False, pc, OP_INVALIDOPCODE, b''
            n = script[pc]; pc += 1
        elif opcode == OP_PUSHDATA2:
            if len(script) - pc < 2: return False, pc, OP_INVALIDOPCODE, b''
            n = struct.unpack('<H', script[pc:pc + 2])[0]; pc += 2
        else:
            if len(script) - pc < 4: return False, pc, OP_INVALIDOPCODE, b''
            n = struct.unpack('<I', script[pc:pc + 4])[0]; pc += 4
        if len(script) - pc < n:
            return False, pc, OP_INVALIDOPCODE, b''
        data = script[pc:pc + n]; pc += n
    return True, pc, opcode, data


def push_bytes(d):
    """CScript() << vector: the canonical push."""
    if len(d) < OP_PUSHDATA1: return bytes([len(d)]) + d
    if len(d) <= 0xff: return bytes([OP_PUSHDATA1, len(d)]) + d
    if len(d) <= 0xffff: return bytes([OP_PUSHDATA2]) + struct.pack('<H', len(d)) + d
    return bytes([OP_PUSHDATA4]) + struct.pack('<I', len(d)) + d


def is_push_only(script):
    pc = 0
    while pc < len(script):
        ok, pc, opcode, _ = get_op(script, pc)
        if not ok: return False
        if opcode > OP_16: return False
    return True


def is_pay_to_script_hash(s):
    return len(s) == 23 and s[0] == OP_HASH160 and s[1] == 0x14 and s[22] == OP_EQUAL


def is_witness_program(s):
    if len(s) < 4 or len(s) > 42: return None
    if s[0] != OP_0 and (s[0] < OP_1 or s[0] > OP_16): return None
    if s[1] + 2 == len(s):
        version = 0 if s[0] == OP_0 else s[0] - (OP_1 - 1)
        return version, s[2:]
    return None


def is_pay_to_anchor(version, program):
    return version == 1 and len(program) == 2 and program[0] == 0x4e and program[1] == 0x73


def is_op_success(opcode):
    return opcode == 80 or opcode == 98 or 126 <= opcode <= 129 or 131 <= opcode <= 134 or \
        137 <= opcode <= 138 or 141 <= opcode <= 142 or 149 <= opcode <= 153 or 187 <= opcode <= 254


def find_and_delete(script, b):
    """FindAndDelete(script, b): returns (new script, nFound)."""
    if len(b) == 0: return script, 0
    result = bytearray(); pc = 0; pc2 = 0; nfound = 0
    while True:
        result += script[pc2:pc]
        while len(script) - pc >= len(b) and script[pc:pc + len(b)] == b:
            pc += len(b); nfound += 1
        pc2 = pc
        ok, pc, _, _ = get_op(script, pc)
        if not ok: break
    if nfound > 0:
        result += script[pc2:]
        return bytes(result), nfound
    return script, nfound


# ----------------------------------------------------------------------------------------------
# hashes and serialization
def sha256(b): return hashlib.sha256(b).digest()
def sha256d(b): return sha256(sha256(b))
def ripemd160(b): return hashlib.new('ripemd160', b).digest()
def sha1(b): return hashlib.sha1(b).digest()
def hash160(b): return ripemd160(sha256(b))


def tagged_hash(tag, m):
    t = sha256(tag.encode()); return sha256(t + t + m)


def compact_size(n):
    if n < 253: return bytes([n])
    if n <= 0xffff: return b'\xfd' + struct.pack('<H', n)
    if n <= 0xffffffff: return b'\xfe' + struct.pack('<I', n)
    return b'\xff' + struct.pack('<Q', n)


def ser_bytes(b): return compact_size(len(b)) + b
def ser_vector(items, f): return compact_size(len(items)) + b''.join(f(i) for i in items)


class Tx:
    """CTransaction data: uint32 version, vin [(prevhash32, n, scriptSig, nSequence, witness)],
    vout [(nValue, scriptPubKey)], uint32 nLockTime."""
    def __init__(self, version, vin, vout, locktime):
        self.version, self.vin, self.vout, self.locktime = version, vin, vout, locktime


def ser_outpoint(h, n): return h + struct.pack('<I', n)
def ser_txout(v, spk): return struct.pack('<q', v) + ser_bytes(spk)
def ser_txin_nowit(i): return ser_outpoint(i[0], i[1]) + ser_bytes(i[2]) + struct.pack('<I', i[3])


# ----------------------------------------------------------------------------------------------
# secp256k1 (pure Python), ECDSA and BIP340
P = 2**256 - 2**32 - 977
N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
G = (0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798,
     0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8)


def inv(a, m): return pow(a, m - 2, m)


def padd(A, B):
    if A is None: return B
    if B is None: return A
    if A[0] == B[0]:
        if (A[1] + B[1]) % P == 0: return None
        l = 3 * A[0] * A[0] * inv(2 * A[1], P) % P
    else:
        l = (B[1] - A[1]) * inv(B[0] - A[0], P) % P
    x = (l * l - A[0] - B[0]) % P
    return (x, (l * (A[0] - x) - A[1]) % P)


def pmul(k, A):
    R = None
    while k:
        if k & 1: R = padd(R, A)
        A = padd(A, A); k >>= 1
    return R


def lift_x(x):
    if x >= P: return None
    y2 = (pow(x, 3, P) + 7) % P
    y = pow(y2, (P + 1) // 4, P)
    if y * y % P != y2: return None
    return (x, y if y % 2 == 0 else P - y)


def pubkey_compressed(Pt): return bytes([2 + (Pt[1] & 1)]) + Pt[0].to_bytes(32, 'big')
def pubkey_uncompressed(Pt): return b'\x04' + Pt[0].to_bytes(32, 'big') + Pt[1].to_bytes(32, 'big')
def xonly(Pt): return Pt[0].to_bytes(32, 'big')


def parse_pubkey(pk):
    """secp256k1_ec_pubkey_parse on a CPubKey that IsValid()."""
    if len(pk) == 33 and pk[0] in (2, 3):
        Pt = lift_x(int.from_bytes(pk[1:], 'big'))
        if Pt is None: return None
        return Pt if (Pt[1] & 1) == (pk[0] & 1) else (Pt[0], P - Pt[1])
    if len(pk) == 65 and pk[0] in (4, 6, 7):
        x, y = int.from_bytes(pk[1:33], 'big'), int.from_bytes(pk[33:], 'big')
        if x >= P or y >= P or (y * y - pow(x, 3, P) - 7) % P != 0: return None
        if pk[0] != 4 and (y & 1) != (pk[0] & 1): return None
        return (x, y)
    return None


def cpubkey_is_valid(pk):
    """CPubKey(vch).IsValid(): the size implied by the header byte matches."""
    if len(pk) == 0: return False
    h = pk[0]
    if h in (2, 3): return len(pk) == 33
    if h in (4, 6, 7): return len(pk) == 65
    return False


def der_int(v):
    b = v.to_bytes((v.bit_length() + 7) // 8 or 1, 'big')
    if b[0] & 0x80: b = b'\x00' + b
    return b'\x02' + bytes([len(b)]) + b


def ecdsa_sign(d, hash32, k=None, low_s=True):
    """Returns the DER signature (no hash-type byte)."""
    e = int.from_bytes(hash32, 'big')
    if k is None:
        k = int.from_bytes(sha256(d.to_bytes(32, 'big') + hash32), 'big') % N or 1
    R = pmul(k, G); r = R[0] % N
    s = inv(k, N) * (e + r * d) % N
    if low_s and s > N // 2: s = N - s
    body = der_int(r) + der_int(s)
    return b'\x30' + bytes([len(body)]) + body


def der_parse_lax(sig):
    """ecdsa_signature_parse_der_lax (pubkey.cpp): returns (r, s) or None.  Overlong values are
    clamped to zero as in the source (r/s of more than 32 significant bytes -> 0)."""
    pos = 0
    if pos == len(sig) or sig[pos] != 0x30: return None
    pos += 1
    if pos == len(sig): return None
    lenbyte = sig[pos]; pos += 1
    if lenbyte & 0x80:
        lenbyte -= 0x80
        if lenbyte > len(sig) - pos: return None
        pos += lenbyte
    if pos == len(sig) or sig[pos] != 0x02: return None
    pos += 1
    if pos == len(sig): return None
    lenbyte = sig[pos]; pos += 1
    if lenbyte & 0x80:
        lenbyte -= 0x80
        if lenbyte > len(sig) - pos: return None
        while lenbyte > 0 and sig[pos] == 0: pos += 1; lenbyte -= 1
        if lenbyte >= 4: return None
        rlen = 0
        while lenbyte > 0: rlen = (rlen << 8) + sig[pos]; pos += 1; lenbyte -= 1
    else:
        rlen = lenbyte
    if rlen > len(sig) - pos: return None
    rpos = pos; pos += rlen
    if pos == len(sig) or sig[pos] != 0x02: return None
    pos += 1
    if pos == len(sig): return None
    lenbyte = sig[pos]; pos += 1
    if lenbyte & 0x80:
        lenbyte -= 0x80
        if lenbyte > len(sig) - pos: return None
        while lenbyte > 0 and sig[pos] == 0: pos += 1; lenbyte -= 1
        if lenbyte >= 4: return None
        slen = 0
        while lenbyte > 0: slen = (slen << 8) + sig[pos]; pos += 1; lenbyte -= 1
    else:
        slen = lenbyte
    if slen > len(sig) - pos: return None
    spos = pos
    # skip leading zeros, overlong -> zero
    while rlen > 0 and sig[rpos] == 0: rlen -= 1; rpos += 1
    r = 0 if rlen > 32 else int.from_bytes(sig[rpos:rpos + rlen], 'big')
    while slen > 0 and sig[spos] == 0: slen -= 1; spos += 1
    s = 0 if slen > 32 else int.from_bytes(sig[spos:spos + slen], 'big')
    return r, s


def ecdsa_verify_raw(Q, hash32, r, s):
    """secp256k1_ecdsa_verify after secp256k1_ecdsa_signature_normalize (low S)."""
    if r == 0 or r >= N or s == 0 or s >= N: return False
    if s > N // 2: s = N - s  # normalize; verification itself rejects high S
    e = int.from_bytes(hash32, 'big') % N
    w = inv(s, N)
    Rp = padd(pmul(e * w % N, G), pmul(r * w % N, Q))
    if Rp is None: return False
    return Rp[0] % N == r


def cpubkey_verify(pk, hash32, sig):
    """CPubKey::Verify."""
    if not cpubkey_is_valid(pk): return False
    Q = parse_pubkey(pk)
    if Q is None: return False
    rs = der_parse_lax(sig)
    if rs is None: return False
    return ecdsa_verify_raw(Q, hash32, rs[0], rs[1])


def schnorr_sign(d, msg32, k=None):
    Pt = pmul(d, G)
    if Pt[1] & 1: d = N - d; Pt = (Pt[0], P - Pt[1])
    if k is None:
        k = int.from_bytes(tagged_hash("BIP0340/nonce", d.to_bytes(32, 'big') + xonly(Pt) + msg32), 'big') % N or 1
    R = pmul(k, G)
    if R[1] & 1: k = N - k; R = (R[0], P - R[1])
    e = int.from_bytes(tagged_hash("BIP0340/challenge", xonly(R) + xonly(Pt) + msg32), 'big') % N
    return xonly(R) + ((k + e * d) % N).to_bytes(32, 'big')


def schnorr_verify(pk32, msg32, sig64):
    if len(pk32) != 32 or len(sig64) != 64: return False
    Pt = lift_x(int.from_bytes(pk32, 'big'))
    if Pt is None: return False
    r = int.from_bytes(sig64[:32], 'big'); s = int.from_bytes(sig64[32:], 'big')
    if r >= P or s >= N: return False
    e = int.from_bytes(tagged_hash("BIP0340/challenge", sig64[:32] + pk32 + msg32), 'big') % N
    R = padd(pmul(s, G), pmul((N - e) % N, Pt))
    return R is not None and R[1] % 2 == 0 and R[0] == r


# ----------------------------------------------------------------------------------------------
# signature encodings (BIP66 etc.)
def is_valid_signature_encoding(sig):
    if len(sig) < 9 or len(sig) > 73: return False
    if sig[0] != 0x30: return False
    if sig[1] != len(sig) - 3: return False
    lenR = sig[3]
    if 5 + lenR >= len(sig): return False
    lenS = sig[5 + lenR]
    if lenR + lenS + 7 != len(sig): return False
    if sig[2] != 0x02: return False
    if lenR == 0: return False
    if sig[4] & 0x80: return False
    if lenR > 1 and sig[4] == 0x00 and not (sig[5] & 0x80): return False
    if sig[lenR + 4] != 0x02: return False
    if lenS == 0: return False
    if sig[lenR + 6] & 0x80: return False
    if lenS > 1 and sig[lenR + 6] == 0x00 and not (sig[lenR + 7] & 0x80): return False
    return True


def check_signature_encoding(sig, flags):
    if len(sig) == 0: return True
    if ({'DERSIG', 'LOW_S', 'STRICTENC'} & flags) and not is_valid_signature_encoding(sig):
        raise ScriptError('SIG_DER')
    # LOW_S and STRICTENC are policy (never in `flags` here)
    return True


def check_pubkey_encoding(pk, flags, sigversion):
    # STRICTENC / WITNESS_PUBKEYTYPE are policy: nothing to check under consensus flags
    return True


# ----------------------------------------------------------------------------------------------
# signature hashes
class ExecData:
    def __init__(self):
        self.tapleaf_hash = None; self.codeseparator_pos = None; self.annex_present = None
        self.annex_hash = None; self.validation_weight_left = None


def serialize_script_code(sc):
    """SerializeScriptCode: scriptCode with OP_CODESEPARATORs removed."""
    pc = 0; ncs = 0
    while True:
        ok, pc, opcode, _ = get_op(sc, pc)
        if not ok: break
        if opcode == OP_CODESEPARATOR: ncs += 1
    out = compact_size(len(sc) - ncs)
    pc = 0; begin = 0
    while True:
        ok, pc2, opcode, _ = get_op(sc, pc)
        if not ok: break
        if opcode == OP_CODESEPARATOR:
            out += sc[begin:pc2 - 1]; begin = pc2
        pc = pc2
    if begin != len(sc): out += sc[begin:pc]
    return out


def sighash_legacy(script_code, tx, nIn, hashtype):
    """SignatureHash for SigVersion::BASE (hashtype is the int32 nHashType)."""
    if (hashtype & 0x1f) == SIGHASH_SINGLE and nIn >= len(tx.vout):
        return b'\x01' + bytes(31)  # uint256::ONE
    anyone = bool(hashtype & SIGHASH_ANYONECANPAY)
    single = (hashtype & 0x1f) == SIGHASH_SINGLE
    none_ = (hashtype & 0x1f) == SIGHASH_NONE
    s = struct.pack('<I', tx.version)
    nInputs = 1 if anyone else len(tx.vin)
    s += compact_size(nInputs)
    for idx in range(nInputs):
        nInput = nIn if anyone else idx
        i = tx.vin[nInput]
        s += ser_outpoint(i[0], i[1])
        if nInput != nIn: s += ser_bytes(b'')
        else: s += serialize_script_code(script_code)
        if nInput != nIn and (single or none_): s += struct.pack('<i', 0)
        else: s += struct.pack('<I', i[3])
    nOutputs = 0 if none_ else (nIn + 1 if single else len(tx.vout))
    s += compact_size(nOutputs)
    for o in range(nOutputs):
        if single and o != nIn: s += ser_txout(-1, b'')
        else: s += ser_txout(tx.vout[o][0], tx.vout[o][1])
    s += struct.pack('<I', tx.locktime)
    s += struct.pack('<i', hashtype)
    return sha256d(s)


def sighash_v0(script_code, tx, nIn, hashtype, amount):
    """SignatureHash for SigVersion::WITNESS_V0 (BIP143)."""
    hp = hs = ho = bytes(32)
    if not (hashtype & SIGHASH_ANYONECANPAY):
        hp = sha256d(b''.join(ser_outpoint(i[0], i[1]) for i in tx.vin))
    if not (hashtype & SIGHASH_ANYONECANPAY) and (hashtype & 0x1f) != SIGHASH_SINGLE and (hashtype & 0x1f) != SIGHASH_NONE:
        hs = sha256d(b''.join(struct.pack('<I', i[3]) for i in tx.vin))
    if (hashtype & 0x1f) != SIGHASH_SINGLE and (hashtype & 0x1f) != SIGHASH_NONE:
        ho = sha256d(b''.join(ser_txout(v, spk) for v, spk in tx.vout))
    elif (hashtype & 0x1f) == SIGHASH_SINGLE and nIn < len(tx.vout):
        ho = sha256d(ser_txout(*tx.vout[nIn]))
    i = tx.vin[nIn]
    s = struct.pack('<I', tx.version) + hp + hs + ser_outpoint(i[0], i[1]) + ser_bytes(script_code) + \
        struct.pack('<q', amount) + struct.pack('<I', i[3]) + ho + struct.pack('<I', tx.locktime) + struct.pack('<i', hashtype)
    return sha256d(s)


def sighash_schnorr(tx, spent, in_pos, hash_type, sigversion, execdata):
    """SignatureHashSchnorr; returns None where the source returns false."""
    ext_flag = 0 if sigversion == TAPROOT else 1
    key_version = 0
    assert in_pos < len(tx.vin)
    output_type = SIGHASH_ALL if hash_type == SIGHASH_DEFAULT else (hash_type & SIGHASH_OUTPUT_MASK)
    input_type = hash_type & SIGHASH_INPUT_MASK
    if not (hash_type <= 0x03 or (0x81 <= hash_type <= 0x83)): return None
    ss = bytes([0]) + bytes([hash_type]) + struct.pack('<I', tx.version) + struct.pack('<I', tx.locktime)
    if input_type != SIGHASH_ANYONECANPAY:
        ss += sha256(b''.join(ser_outpoint(i[0], i[1]) for i in tx.vin))
        ss += sha256(b''.join(struct.pack('<q', o[0]) for o in spent))
        ss += sha256(b''.join(ser_bytes(o[1]) for o in spent))
        ss += sha256(b''.join(struct.pack('<I', i[3]) for i in tx.vin))
    if output_type == SIGHASH_ALL:
        ss += sha256(b''.join(ser_txout(v, spk) for v, spk in tx.vout))
    have_annex = execdata.annex_present
    spend_type = (ext_flag << 1) + (1 if have_annex else 0)
    ss += bytes([spend_type])
    if input_type == SIGHASH_ANYONECANPAY:
        i = tx.vin[in_pos]
        ss += ser_outpoint(i[0], i[1]) + ser_txout(*spent[in_pos]) + struct.pack('<I', i[3])
    else:
        ss += struct.pack('<I', in_pos)
    if have_annex:
        ss += execdata.annex_hash
    if output_type == SIGHASH_SINGLE:
        if in_pos >= len(tx.vout): return None
        ss += sha256(ser_txout(*tx.vout[in_pos]))
    if sigversion == TAPSCRIPT:
        ss += execdata.tapleaf_hash + bytes([key_version]) + struct.pack('<I', execdata.codeseparator_pos)
    return tagged_hash("TapSighash", ss)


# ----------------------------------------------------------------------------------------------
# the transaction signature checker
class TxChecker:
    """GenericTransactionSignatureChecker(tx, nIn, amount, txdata with spent outputs)."""
    def __init__(self, tx, nIn, amount, spent=None):
        self.tx, self.nIn, self.amount, self.spent = tx, nIn, amount, spent

    def check_ecdsa(self, sig_in, pubkey, script_code, sigversion):
        if not cpubkey_is_valid(pubkey): return False
        if len(sig_in) == 0: return False
        hashtype = sig_in[-1]; sig = sig_in[:-1]
        if sigversion == WITNESS_V0 and self.amount < 0: return False  # MissingDataBehavior::FAIL
        if sigversion == WITNESS_V0:
            h = sighash_v0(script_code, self.tx, self.nIn, hashtype, self.amount)
        else:
            h = sighash_legacy(script_code, self.tx, self.nIn, hashtype)
        return cpubkey_verify(pubkey, h, sig)

    def check_schnorr(self, sig, pubkey, sigversion, execdata):
        """CheckSchnorrSignature: raises ScriptError where it set_error()s, returns True otherwise."""
        assert len(pubkey) == 32
        if len(sig) != 64 and len(sig) != 65: raise ScriptError('SCHNORR_SIG_SIZE')
        hashtype = SIGHASH_DEFAULT
        if len(sig) == 65:
            hashtype = sig[-1]; sig = sig[:-1]
            if hashtype == SIGHASH_DEFAULT: raise ScriptError('SCHNORR_SIG_HASHTYPE')
        h = sighash_schnorr(self.tx, self.spent, self.nIn, hashtype, sigversion, execdata)
        if h is None: raise ScriptError('SCHNORR_SIG_HASHTYPE')
        if not schnorr_verify(pubkey, h, sig): raise ScriptError('SCHNORR_SIG')
        return True

    def check_locktime(self, nLockTime):
        tl = self.tx.locktime
        if not ((tl < LOCKTIME_THRESHOLD and nLockTime < LOCKTIME_THRESHOLD) or
                (tl >= LOCKTIME_THRESHOLD and nLockTime >= LOCKTIME_THRESHOLD)):
            return False
        if nLockTime > tl: return False
        if self.tx.vin[self.nIn][3] == SEQUENCE_FINAL: return False
        return True

    def check_sequence(self, nSequence):
        txToSequence = self.tx.vin[self.nIn][3]
        if self.tx.version < 2: return False  # uint32_t version
        if txToSequence & SEQUENCE_LOCKTIME_DISABLE_FLAG: return False
        mask = SEQUENCE_LOCKTIME_TYPE_FLAG | SEQUENCE_LOCKTIME_MASK
        txm = txToSequence & mask
        sm = nSequence & mask
        if not ((txm < SEQUENCE_LOCKTIME_TYPE_FLAG and sm < SEQUENCE_LOCKTIME_TYPE_FLAG) or
                (txm >= SEQUENCE_LOCKTIME_TYPE_FLAG and sm >= SEQUENCE_LOCKTIME_TYPE_FLAG)):
            return False
        if sm > txm: return False
        return True


# ----------------------------------------------------------------------------------------------
# EvalChecksig
def eval_checksig_pretapscript(sig, pubkey, script_code, flags, checker, sigversion):
    """Returns fSuccess; raises ScriptError where the source returns false."""
    if sigversion == BASE:
        script_code, found = find_and_delete(script_code, push_bytes(sig))
        # CONST_SCRIPTCODE is policy
    check_signature_encoding(sig, flags)
    check_pubkey_encoding(pubkey, flags, sigversion)
    return checker.check_ecdsa(sig, pubkey, script_code, sigversion)


def eval_checksig_tapscript(sig, pubkey, execdata, flags, checker, sigversion):
    success = len(sig) > 0
    if success:
        execdata.validation_weight_left -= VALIDATION_WEIGHT_PER_SIGOP_PASSED
        if execdata.validation_weight_left < 0: raise ScriptError('TAPSCRIPT_VALIDATION_WEIGHT')
    if len(pubkey) == 0:
        raise ScriptError('TAPSCRIPT_EMPTY_PUBKEY')
    elif len(pubkey) == 32:
        if success: checker.check_schnorr(sig, pubkey, sigversion, execdata)
    else:
        pass  # DISCOURAGE_UPGRADABLE_PUBKEYTYPE is policy
    return success


def eval_checksig(sig, pubkey, script_code, execdata, flags, checker, sigversion):
    if sigversion in (BASE, WITNESS_V0):
        return eval_checksig_pretapscript(sig, pubkey, script_code, flags, checker, sigversion)
    return eval_checksig_tapscript(sig, pubkey, execdata, flags, checker, sigversion)


# ----------------------------------------------------------------------------------------------
# EvalScript
def eval_script(stack, script, flags, checker, sigversion, execdata=None):
    """Returns (True, stack) or (False, error code).  `stack` is bottom-first like the source."""
    if execdata is None: execdata = ExecData()
    stack = list(stack)
    try:
        _eval_script(stack, script, flags, checker, sigversion, execdata)
        return True, stack
    except ScriptError as e:
        return False, e.code
    except ScriptNumError:
        return False, 'SCRIPTNUM'


def _eval_script(stack, script, flags, checker, sigversion, execdata):
    vchFalse, vchTrue = b'', b'\x01'
    pc = 0; pend = len(script); pbegincodehash = 0
    vfExec = []           # ConditionStack, materialized
    altstack = []
    if sigversion in (BASE, WITNESS_V0) and len(script) > MAX_SCRIPT_SIZE:
        raise ScriptError('SCRIPT_SIZE')
    nOpCount = 0
    fRequireMinimal = 'MINIMALDATA' in flags
    opcode_pos = 0
    execdata.codeseparator_pos = 0xFFFFFFFF
    while pc < pend:
        fExec = all(vfExec)
        ok, pc, opcode, vchPushValue = get_op(script, pc)
        if not ok: raise ScriptError('BAD_OPCODE')
        if len(vchPushValue) > MAX_SCRIPT_ELEMENT_SIZE: raise ScriptError('PUSH_SIZE')
        if sigversion in (BASE, WITNESS_V0):
            if opcode > OP_16:
                nOpCount += 1
                if nOpCount > MAX_OPS_PER_SCRIPT: raise ScriptError('OP_COUNT')
        if opcode in DISABLED: raise ScriptError('DISABLED_OPCODE')
        # CONST_SCRIPTCODE codeseparator rejection is policy
        if fExec and 0 <= opcode <= OP_PUSHDATA4:
            stack.append(vchPushValue)
        elif fExec or (OP_IF <= opcode <= OP_ENDIF):
            if OP_1NEGATE == opcode or OP_1 <= opcode <= OP_16:
                stack.append(scriptnum_encode(opcode - (OP_1 - 1)))
            elif opcode == OP_NOP:
                pass
            elif opcode == OP_CHECKLOCKTIMEVERIFY:
                if 'CLTV' in flags:
                    if len(stack) < 1: raise ScriptError('INVALID_STACK_OPERATION')
                    nLockTime = scriptnum_decode(stack[-1], fRequireMinimal, 5)
                    if nLockTime < 0: raise ScriptError('NEGATIVE_LOCKTIME')
                    if not checker.check_locktime(nLockTime): raise ScriptError('UNSATISFIED_LOCKTIME')
            elif opcode == OP_CHECKSEQUENCEVERIFY:
                if 'CSV' in flags:
                    if len(stack) < 1: raise ScriptError('INVALID_STACK_OPERATION')
                    nSequence = scriptnum_decode(stack[-1], fRequireMinimal, 5)
                    if nSequence < 0: raise ScriptError('NEGATIVE_LOCKTIME')
                    if (nSequence & SEQUENCE_LOCKTIME_DISABLE_FLAG) == 0:
                        if not checker.check_sequence(nSequence): raise ScriptError('UNSATISFIED_LOCKTIME')
            elif opcode in (OP_NOP1, OP_NOP4, OP_NOP5, OP_NOP6, OP_NOP7, OP_NOP8, OP_NOP9, OP_NOP10):
                pass  # DISCOURAGE_UPGRADABLE_NOPS is policy
            elif opcode in (OP_IF, OP_NOTIF):
                fValue = False
                if fExec:
                    if len(stack) < 1: raise ScriptError('UNBALANCED_CONDITIONAL')
                    vch = stack[-1]
                    if sigversion == TAPSCRIPT:
                        if len(vch) > 1 or (len(vch) == 1 and vch[0] != 1): raise ScriptError('TAPSCRIPT_MINIMALIF')
                    # MINIMALIF under WITNESS_V0 is policy
                    fValue = cast_to_bool(vch)
                    if opcode == OP_NOTIF: fValue = not fValue
                    stack.pop()
                vfExec.append(fValue)
            elif opcode == OP_ELSE:
                if not vfExec: raise ScriptError('UNBALANCED_CONDITIONAL')
                vfExec[-1] = not vfExec[-1]
            elif opcode == OP_ENDIF:
                if not vfExec: raise ScriptError('UNBALANCED_CONDITIONAL')
                vfExec.pop()
            elif opcode == OP_VERIFY:
                if len(stack) < 1: raise ScriptError('INVALID_STACK_OPERATION')
                if cast_to_bool(stack[-1]): stack.pop()
                else: raise ScriptError('VERIFY')
            elif opcode == OP_RETURN:
                raise ScriptError('OP_RETURN')
            elif opcode == OP_TOALTSTACK:
                if len(stack) < 1: raise ScriptError('INVALID_STACK_OPERATION')
                altstack.append(stack.pop())
            elif opcode == OP_FROMALTSTACK:
                if len(altstack) < 1: raise ScriptError('INVALID_ALTSTACK_OPERATION')
                stack.append(altstack.pop())
            elif opcode == OP_2DROP:
                if len(stack) < 2: raise ScriptError('INVALID_STACK_OPERATION')
                stack.pop(); stack.pop()
            elif opcode == OP_2DUP:
                if len(stack) < 2: raise ScriptError('INVALID_STACK_OPERATION')
                stack.extend([stack[-2], stack[-1]])
            elif opcode == OP_3DUP:
                if len(stack) < 3: raise ScriptError('INVALID_STACK_OPERATION')
                stack.extend([stack[-3], stack[-2], stack[-1]])
            elif opcode == OP_2OVER:
                if len(stack) < 4: raise ScriptError('INVALID_STACK_OPERATION')
                stack.extend([stack[-4], stack[-3]])
            elif opcode == OP_2ROT:
                if len(stack) < 6: raise ScriptError('INVALID_STACK_OPERATION')
                a, b = stack[-6], stack[-5]
                del stack[-6:-4]
                stack.extend([a, b])
            elif opcode == OP_2SWAP:
                if len(stack) < 4: raise ScriptError('INVALID_STACK_OPERATION')
                stack[-4], stack[-2] = stack[-2], stack[-4]
                stack[-3], stack[-1] = stack[-1], stack[-3]
            elif opcode == OP_IFDUP:
                if len(stack) < 1: raise ScriptError('INVALID_STACK_OPERATION')
                if cast_to_bool(stack[-1]): stack.append(stack[-1])
            elif opcode == OP_DEPTH:
                stack.append(scriptnum_encode(len(stack)))
            elif opcode == OP_DROP:
                if len(stack) < 1: raise ScriptError('INVALID_STACK_OPERATION')
                stack.pop()
            elif opcode == OP_DUP:
                if len(stack) < 1: raise ScriptError('INVALID_STACK_OPERATION')
                stack.append(stack[-1])
            elif opcode == OP_NIP:
                if len(stack) < 2: raise ScriptError('INVALID_STACK_OPERATION')
                del stack[-2]
            elif opcode == OP_OVER:
                if len(stack) < 2: raise ScriptError('INVALID_STACK_OPERATION')
                stack.append(stack[-2])
            elif opcode in (OP_PICK, OP_ROLL):
                if len(stack) < 2: raise ScriptError('INVALID_STACK_OPERATION')
                n = getint(scriptnum_decode(stack[-1], fRequireMinimal))
                stack.pop()
                if n < 0 or n >= len(stack): raise ScriptError('INVALID_STACK_OPERATION')
                vch = stack[-n - 1]
                if opcode == OP_ROLL: del stack[-n - 1]
                stack.append(vch)
            elif opcode == OP_ROT:
                if len(stack) < 3: raise ScriptError('INVALID_STACK_OPERATION')
                stack[-3], stack[-2] = stack[-2], stack[-3]
                stack[-2], stack[-1] = stack[-1], stack[-2]
            elif opcode == OP_SWAP:
                if len(stack) < 2: raise ScriptError('INVALID_STACK_OPERATION')
                stack[-2], stack[-1] = stack[-1], stack[-2]
            elif opcode == OP_TUCK:
                if len(stack) < 2: raise ScriptError('INVALID_STACK_OPERATION')
                stack.insert(len(stack) - 2, stack[-1])
            elif opcode == OP_SIZE:
                if len(stack) < 1: raise ScriptError('INVALID_STACK_OPERATION')
                stack.append(scriptnum_encode(len(stack[-1])))
            elif opcode in (OP_EQUAL, OP_EQUALVERIFY):
                if len(stack) < 2: raise ScriptError('INVALID_STACK_OPERATION')
                fEqual = stack[-2] == stack[-1]
                stack.pop(); stack.pop()
                stack.append(vchTrue if fEqual else vchFalse)
                if opcode == OP_EQUALVERIFY:
                    if fEqual: stack.pop()
                    else: raise ScriptError('EQUALVERIFY')
            elif opcode in (OP_1ADD, OP_1SUB, OP_NEGATE, OP_ABS, OP_NOT, OP_0NOTEQUAL):
                if len(stack) < 1: raise ScriptError('INVALID_STACK_OPERATION')
                bn = scriptnum_decode(stack[-1], fRequireMinimal)
                if opcode == OP_1ADD: bn += 1
                elif opcode == OP_1SUB: bn -= 1
                elif opcode == OP_NEGATE: bn = -bn
                elif opcode == OP_ABS: bn = -bn if bn < 0 else bn
                elif opcode == OP_NOT: bn = 1 if bn == 0 else 0
                else: bn = 1 if bn != 0 else 0
                stack.pop(); stack.append(scriptnum_encode(bn))
            elif opcode in (OP_ADD, OP_SUB, OP_BOOLAND, OP_BOOLOR, OP_NUMEQUAL, OP_NUMEQUALVERIFY, OP_NUMNOTEQUAL,
                            OP_LESSTHAN, OP_GREATERTHAN, OP_LESSTHANOREQUAL, OP_GREATERTHANOREQUAL, OP_MIN, OP_MAX):
                if len(stack) < 2: raise ScriptError('INVALID_STACK_OPERATION')
                bn1 = scriptnum_decode(stack[-2], fRequireMinimal)
                bn2 = scriptnum_decode(stack[-1], fRequireMinimal)
                if opcode == OP_ADD: bn = bn1 + bn2
                elif opcode == OP_SUB: bn = bn1 - bn2
                elif opcode == OP_BOOLAND: bn = int(bn1 != 0 and bn2 != 0)
                elif opcode == OP_BOOLOR: bn = int(bn1 != 0 or bn2 != 0)
                elif opcode in (OP_NUMEQUAL, OP_NUMEQUALVERIFY): bn = int(bn1 == bn2)
                elif opcode == OP_NUMNOTEQUAL: bn = int(bn1 != bn2)
                elif opcode == OP_LESSTHAN: bn = int(bn1 < bn2)
                elif opcode == OP_GREATERTHAN: bn = int(bn1 > bn2)
                elif opcode == OP_LESSTHANOREQUAL: bn = int(bn1 <= bn2)
                elif opcode == OP_GREATERTHANOREQUAL: bn = int(bn1 >= bn2)
                elif opcode == OP_MIN: bn = bn1 if bn1 < bn2 else bn2
                else: bn = bn1 if bn1 > bn2 else bn2
                stack.pop(); stack.pop(); stack.append(scriptnum_encode(bn))
                if opcode == OP_NUMEQUALVERIFY:
                    if cast_to_bool(stack[-1]): stack.pop()
                    else: raise ScriptError('NUMEQUALVERIFY')
            elif opcode == OP_WITHIN:
                if len(stack) < 3: raise ScriptError('INVALID_STACK_OPERATION')
                bn1 = scriptnum_decode(stack[-3], fRequireMinimal)
                bn2 = scriptnum_decode(stack[-2], fRequireMinimal)
                bn3 = scriptnum_decode(stack[-1], fRequireMinimal)
                fValue = bn2 <= bn1 < bn3
                stack.pop(); stack.pop(); stack.pop()
                stack.append(vchTrue if fValue else vchFalse)
            elif opcode in (OP_RIPEMD160, OP_SHA1, OP_SHA256, OP_HASH160, OP_HASH256):
                if len(stack) < 1: raise ScriptError('INVALID_STACK_OPERATION')
                vch = stack[-1]
                h = checker.hashes[opcode](vch)
                stack.pop(); stack.append(h)
            elif opcode == OP_CODESEPARATOR:
                pbegincodehash = pc
                execdata.codeseparator_pos = opcode_pos
            elif opcode in (OP_CHECKSIG, OP_CHECKSIGVERIFY):
                if len(stack) < 2: raise ScriptError('INVALID_STACK_OPERATION')
                vchSig, vchPubKey = stack[-2], stack[-1]
                fSuccess = checker.eval_checksig(vchSig, vchPubKey, script[pbegincodehash:pend], execdata, flags, sigversion)
                stack.pop(); stack.pop()
                stack.append(vchTrue if fSuccess else vchFalse)
                if opcode == OP_CHECKSIGVERIFY:
                    if fSuccess: stack.pop()
                    else: raise ScriptError('CHECKSIGVERIFY')
            elif opcode == OP_CHECKSIGADD:
                if sigversion in (BASE, WITNESS_V0): raise ScriptError('BAD_OPCODE')
                if len(stack) < 3: raise ScriptError('INVALID_STACK_OPERATION')
                sig = stack[-3]
                num = scriptnum_decode(stack[-2], fRequireMinimal)
                pubkey = stack[-1]
                success = checker.eval_checksig(sig, pubkey, script[pbegincodehash:pend], execdata, flags, sigversion)
                stack.pop(); stack.pop(); stack.pop()
                stack.append(scriptnum_encode(num + (1 if success else 0)))
            elif opcode in (OP_CHECKMULTISIG, OP_CHECKMULTISIGVERIFY):
                if sigversion == TAPSCRIPT: raise ScriptError('TAPSCRIPT_CHECKMULTISIG')
                i = 1
                if len(stack) < i: raise ScriptError('INVALID_STACK_OPERATION')
                nKeysCount = getint(scriptnum_decode(stack[-i], fRequireMinimal))
                if nKeysCount < 0 or nKeysCount > MAX_PUBKEYS_PER_MULTISIG: raise ScriptError('PUBKEY_COUNT')
                nOpCount += nKeysCount
                if nOpCount > MAX_OPS_PER_SCRIPT: raise ScriptError('OP_COUNT')
                i += 1; ikey = i
                ikey2 = nKeysCount + 2
                i += nKeysCount
                if len(stack) < i: raise ScriptError('INVALID_STACK_OPERATION')
                nSigsCount = getint(scriptnum_decode(stack[-i], fRequireMinimal))
                if nSigsCount < 0 or nSigsCount > nKeysCount: raise ScriptError('SIG_COUNT')
                i += 1; isig = i
                i += nSigsCount
                if len(stack) < i: raise ScriptError('INVALID_STACK_OPERATION')
                scriptCode = script[pbegincodehash:pend]
                for k in range(nSigsCount):
                    vchSig = stack[-isig - k]
                    if sigversion == BASE:
                        scriptCode, found = find_and_delete(scriptCode, push_bytes(vchSig))
                fSuccess = True
                while fSuccess and nSigsCount > 0:
                    vchSig, vchPubKey = stack[-isig], stack[-ikey]
                    fOk = checker.multisig_check(vchSig, vchPubKey, scriptCode, flags, sigversion)
                    if fOk:
                        isig += 1; nSigsCount -= 1
                    ikey += 1; nKeysCount -= 1
                    if nSigsCount > nKeysCount: fSuccess = False
                while i > 1:
                    i -= 1
                    # NULLFAIL is policy
                    if ikey2 > 0: ikey2 -= 1
                    stack.pop()
                if len(stack) < 1: raise ScriptError('INVALID_STACK_OPERATION')
                if 'NULLDUMMY' in flags and len(stack[-1]): raise ScriptError('SIG_NULLDUMMY')
                stack.pop()
                stack.append(vchTrue if fSuccess else vchFalse)
                if opcode == OP_CHECKMULTISIGVERIFY:
                    if fSuccess: stack.pop()
                    else: raise ScriptError('CHECKMULTISIGVERIFY')
            else:
                raise ScriptError('BAD_OPCODE')
        if len(stack) + len(altstack) > MAX_STACK_SIZE: raise ScriptError('STACK_SIZE')
        opcode_pos += 1
    if vfExec: raise ScriptError('UNBALANCED_CONDITIONAL')


class RealChecker:
    """The hashes of the source and EvalChecksig over a TxChecker."""
    def __init__(self, txchecker):
        self.tc = txchecker
        self.hashes = {OP_RIPEMD160: ripemd160, OP_SHA1: sha1, OP_SHA256: sha256, OP_HASH160: hash160, OP_HASH256: sha256d}

    def eval_checksig(self, sig, pubkey, script_code, execdata, flags, sigversion):
        return eval_checksig(sig, pubkey, script_code, execdata, flags, self.tc, sigversion)

    def multisig_check(self, sig, pubkey, script_code, flags, sigversion):
        check_signature_encoding(sig, flags); check_pubkey_encoding(pubkey, flags, sigversion)
        return self.tc.check_ecdsa(sig, pubkey, script_code, sigversion)

    def check_locktime(self, n): return self.tc.check_locktime(n)
    def check_sequence(self, n): return self.tc.check_sequence(n)


# ----------------------------------------------------------------------------------------------
# ExecuteWitnessScript, taproot helpers, VerifyWitnessProgram, VerifyScript
def execute_witness_script(stack, exec_script, flags, sigversion, checker, execdata):
    stack = list(stack)
    if sigversion == TAPSCRIPT:
        pc = 0
        while pc < len(exec_script):
            ok, pc, opcode, _ = get_op(exec_script, pc)
            if not ok: raise ScriptError('BAD_OPCODE')
            if is_op_success(opcode):
                return True  # DISCOURAGE_OP_SUCCESS is policy
        if len(stack) > MAX_STACK_SIZE: raise ScriptError('STACK_SIZE')
    for elem in stack:
        if len(elem) > MAX_SCRIPT_ELEMENT_SIZE: raise ScriptError('PUSH_SIZE')
    ok, res = eval_script(stack, exec_script, flags, checker, sigversion, execdata)
    if not ok: raise ScriptError(res)
    if len(res) != 1: raise ScriptError('CLEANSTACK')
    if not cast_to_bool(res[-1]): raise ScriptError('EVAL_FALSE')
    return True


def tapleaf_hash(leaf_version, script):
    return tagged_hash("TapLeaf", bytes([leaf_version]) + compact_size(len(script)) + script)


def tapbranch_hash(a, b):
    return tagged_hash("TapBranch", a + b if a < b else b + a)


def taproot_merkle_root(control, leaf_hash):
    path_len = (len(control) - TAPROOT_CONTROL_BASE_SIZE) // TAPROOT_CONTROL_NODE_SIZE
    k = leaf_hash
    for i in range(path_len):
        node = control[TAPROOT_CONTROL_BASE_SIZE + 32 * i: TAPROOT_CONTROL_BASE_SIZE + 32 * (i + 1)]
        k = tapbranch_hash(k, node)
    return k


def tap_tweak_hash(internal32, merkle_root):
    return tagged_hash("TapTweak", internal32 + merkle_root)


def check_tap_tweak(output32, internal32, merkle_root, parity):
    """XOnlyPubKey::CheckTapTweak with secp256k1_xonly_pubkey_tweak_add_check."""
    Pi = lift_x(int.from_bytes(internal32, 'big'))
    if Pi is None: return False
    t = int.from_bytes(tap_tweak_hash(internal32, merkle_root), 'big')
    if t >= N: return False
    Q = padd(Pi, pmul(t, G))
    if Q is None: return False
    return xonly(Q) == output32 and (Q[1] & 1) == (1 if parity else 0)


def verify_taproot_commitment(control, program, leaf_hash):
    return check_tap_tweak(program, control[1:33], taproot_merkle_root(control, leaf_hash), bool(control[0] & 1))


def taproot_tweak(Pi, merkle_root):
    """CreateTapTweak for an even-y internal point: (Q, parity, t)."""
    t = int.from_bytes(tap_tweak_hash(xonly(Pi), merkle_root), 'big')
    Q = padd(Pi, pmul(t, G))
    return Q, Q[1] & 1, t


def verify_witness_program(witness, witversion, program, flags, checker, is_p2sh):
    """Returns True, or raises ScriptError."""
    stack = list(witness)
    execdata = ExecData()
    if witversion == 0:
        if len(program) == WITNESS_V0_SCRIPTHASH_SIZE:
            if len(stack) == 0: raise ScriptError('WITNESS_PROGRAM_WITNESS_EMPTY')
            script_bytes = stack.pop()
            if sha256(script_bytes) != program: raise ScriptError('WITNESS_PROGRAM_MISMATCH')
            return execute_witness_script(stack, script_bytes, flags, WITNESS_V0, checker, execdata)
        elif len(program) == WITNESS_V0_KEYHASH_SIZE:
            if len(stack) != 2: raise ScriptError('WITNESS_PROGRAM_MISMATCH')
            exec_script = bytes([OP_DUP, OP_HASH160]) + push_bytes(program) + bytes([OP_EQUALVERIFY, OP_CHECKSIG])
            return execute_witness_script(stack, exec_script, flags, WITNESS_V0, checker, execdata)
        else:
            raise ScriptError('WITNESS_PROGRAM_WRONG_LENGTH')
    elif witversion == 1 and len(program) == WITNESS_V1_TAPROOT_SIZE and not is_p2sh:
        if 'TAPROOT' not in flags: return True
        if len(stack) == 0: raise ScriptError('WITNESS_PROGRAM_WITNESS_EMPTY')
        if len(stack) >= 2 and len(stack[-1]) > 0 and stack[-1][0] == ANNEX_TAG:
            annex = stack.pop()
            execdata.annex_hash = sha256(ser_bytes(annex))
            execdata.annex_present = True
        else:
            execdata.annex_present = False
        if len(stack) == 1:
            checker.tc.check_schnorr(stack[0], program, TAPROOT, execdata)
            return True
        control = stack.pop(); script = stack.pop()
        if len(control) < TAPROOT_CONTROL_BASE_SIZE or len(control) > TAPROOT_CONTROL_MAX_SIZE or \
                (len(control) - TAPROOT_CONTROL_BASE_SIZE) % TAPROOT_CONTROL_NODE_SIZE != 0:
            raise ScriptError('TAPROOT_WRONG_CONTROL_SIZE')
        execdata.tapleaf_hash = tapleaf_hash(control[0] & TAPROOT_LEAF_MASK, script)
        if not verify_taproot_commitment(control, program, execdata.tapleaf_hash):
            raise ScriptError('WITNESS_PROGRAM_MISMATCH')
        if (control[0] & TAPROOT_LEAF_MASK) == TAPROOT_LEAF_TAPSCRIPT:
            execdata.validation_weight_left = len(ser_vector(witness, ser_bytes)) + VALIDATION_WEIGHT_OFFSET
            return execute_witness_script(stack, script, flags, TAPSCRIPT, checker, execdata)
        return True  # DISCOURAGE_UPGRADABLE_TAPROOT_VERSION is policy
    elif not is_p2sh and is_pay_to_anchor(witversion, program):
        return True
    else:
        return True  # DISCOURAGE_UPGRADABLE_WITNESS_PROGRAM is policy


def verify_script(scriptSig, scriptPubKey, witness, flags, checker):
    """VerifyScript: returns (True, 'OK') or (False, error)."""
    try:
        return _verify_script(scriptSig, scriptPubKey, witness, flags, checker), 'OK'
    except ScriptError as e:
        return False, e.code


def _verify_script(scriptSig, scriptPubKey, witness, flags, checker):
    hadWitness = False
    # SIGPUSHONLY is policy
    ok, stack = eval_script([], scriptSig, flags, checker, BASE)
    if not ok: raise ScriptError(stack)
    stackCopy = list(stack) if 'P2SH' in flags else None
    ok, stack = eval_script(stack, scriptPubKey, flags, checker, BASE)
    if not ok: raise ScriptError(stack)
    if len(stack) == 0: raise ScriptError('EVAL_FALSE')
    if not cast_to_bool(stack[-1]): raise ScriptError('EVAL_FALSE')
    if 'WITNESS' in flags:
        wp = is_witness_program(scriptPubKey)
        if wp is not None:
            hadWitness = True
            if len(scriptSig) != 0: raise ScriptError('WITNESS_MALLEATED')
            verify_witness_program(witness, wp[0], wp[1], flags, checker, False)
            stack = stack[:1]
    if 'P2SH' in flags and is_pay_to_script_hash(scriptPubKey):
        if not is_push_only(scriptSig): raise ScriptError('SIG_PUSHONLY')
        stack = stackCopy
        assert len(stack) > 0
        pubKey2 = stack.pop()
        ok, stack = eval_script(stack, pubKey2, flags, checker, BASE)
        if not ok: raise ScriptError(stack)
        if len(stack) == 0: raise ScriptError('EVAL_FALSE')
        if not cast_to_bool(stack[-1]): raise ScriptError('EVAL_FALSE')
        if 'WITNESS' in flags:
            wp = is_witness_program(pubKey2)
            if wp is not None:
                hadWitness = True
                if scriptSig != push_bytes(pubKey2): raise ScriptError('WITNESS_MALLEATED_P2SH')
                verify_witness_program(witness, wp[0], wp[1], flags, checker, True)
                stack = stack[:1]
    # CLEANSTACK is policy
    if 'WITNESS' in flags:
        if not hadWitness and len(witness) != 0: raise ScriptError('WITNESS_UNEXPECTED')
    return True


# ----------------------------------------------------------------------------------------------
# Lean rendering helpers
def lean_bytes(b):
    return '[' + ', '.join(str(x) for x in b) + ']'


def lean_hx(b):
    return 'hx "' + b.hex() + '"' if len(b) else '[]'


def lean_stack(stack_bottom_first):
    """A source stack (bottom first) as the Lean top-first list."""
    return '[' + ', '.join(lean_bytes(e) for e in reversed(stack_bottom_first)) + ']'


# ----------------------------------------------------------------------------------------------
# Spot 1: instruction-level vectors against an abstract oracle
class AbstractChecker:
    """The oracle of SecondReviewScriptVectors.lean: hashes prefix a tag byte; checkSig fails the
    script for the signature [0xff] and otherwise succeeds iff sig == pubkey + 2 bytewise; the lock-time
    checks are the real ones over a TxChecker."""
    def __init__(self, txchecker):
        self.tc = txchecker
        self.hashes = {op: (lambda b, op=op: bytes([op]) + b) for op in (OP_RIPEMD160, OP_SHA1, OP_SHA256, OP_HASH160, OP_HASH256)}

    def _sig(self, sig, pubkey):
        if sig == b'\xff': raise ScriptError('SIG_DER')
        return sig == bytes((x + 2) & 0xff for x in pubkey)

    def eval_checksig(self, sig, pubkey, script_code, execdata, flags, sigversion): return self._sig(sig, pubkey)
    def multisig_check(self, sig, pubkey, script_code, flags, sigversion): return self._sig(sig, pubkey)
    def check_locktime(self, n): return self.tc.check_locktime(n)
    def check_sequence(self, n): return self.tc.check_sequence(n)


def instrs_to_bytes(instrs):
    out = b''
    for i in instrs:
        if isinstance(i, bytes): out += push_bytes(i)
        else: out += bytes([i])
    return out


def lean_instr(i):
    if isinstance(i, bytes): return '.push ' + lean_bytes(i)
    if i == OP_0: return '.push []'   # OP_0 is a push of the empty element
    return '.op (0x%02x : Byte)' % i


def lean_script(segs):
    """segs: list of instructions or ('rep', n, [instrs]) segments."""
    parts = []
    for s in segs:
        if isinstance(s, tuple):
            _, n, body = s
            parts.append('(List.replicate %d [%s]).flatten' % (n, ', '.join(lean_instr(i) for i in body)))
        else:
            parts.append('[' + lean_instr(s) + ']')
    return ' ++ '.join(parts) if parts else '[]'


def flatten(segs):
    out = []
    for s in segs:
        if isinstance(s, tuple): out.extend(s[2] * s[1])
        else: out.append(s)
    return out


def main():
    L = []
    L.append('import Definitions.Def_BitcoinScript')
    L.append('import Definitions.Def_BitcoinSig')
    L.append('open BitcoinScript')
    L.append('/-! Second-review vectors for spot 1 (`Def_BitcoinScript`: `execOp`, `step`, `run`, `evalScript`),')
    L.append('generated by tests/reference/second_script_reference.py from `EvalScript` (SigVersion::BASE, mainnet')
    L.append('consensus flags).  Every line must print `true`. -/')
    # three transactions for the lock-time checks (version, nLockTime, input nSequence)
    txs = {
        'A': Tx(2, [(bytes(32), 0, b'', 10, [])], [(1, b'\x51')], 600000000),        # time lock, height-type relative lock 10
        'B': Tx(1, [(bytes(32), 0, b'', SEQUENCE_FINAL, [])], [(1, b'\x51')], 1000),  # version 1, final input
        'C': Tx(2, [(bytes(32), 0, b'', SEQUENCE_LOCKTIME_TYPE_FLAG | 10, [])], [(1, b'\x51')], 1000),  # height lock, time-type relative lock
        'D': Tx(2, [(bytes(32), 0, b'', SEQUENCE_LOCKTIME_DISABLE_FLAG | 5, [])], [(1, b'\x51')], 499999999),
    }
    for name, tx in txs.items():
        i = tx.vin[0]
        L.append('def tx%s : BitcoinSer.Tx := ⟨%d, [⟨⟨List.replicate 32 0, 0⟩, [], %d, []⟩], [⟨1, [0x51]⟩], %d⟩' % (name, tx.version, i[3], tx.locktime))
        L.append('def O%s : Oracle where' % name)
        L.append('  ripemd160 := fun b => 0xa6 :: b')
        L.append('  sha1 := fun b => 0xa7 :: b')
        L.append('  sha256 := fun b => 0xa8 :: b')
        L.append('  hash160 := fun b => 0xa9 :: b')
        L.append('  hash256 := fun b => 0xaa :: b')
        L.append('  checkSig := fun sig pk => if sig == [0xff] then none else some (sig == pk.map (· + 2))')
        L.append('  checkLockTime := BitcoinSig.checkLockTime tx%s 0' % name)
        L.append('  checkSequence := BitcoinSig.checkSequence tx%s 0' % name)
    L.append('def F : Flags := ⟨true, true, true⟩')
    L.append('def Fnd : Flags := ⟨true, true, false⟩')
    L.append('def Fnone : Flags := ⟨false, false, false⟩')
    checkers = {k: AbstractChecker(TxChecker(v, 0, 1)) for k, v in txs.items()}

    def vec(segs, comment='', flags=CONSENSUS_FLAGS, fl='F', oracle='A', init=()):
        script = instrs_to_bytes(flatten(segs))
        ok, res = eval_script(list(init), script, flags, checkers[oracle], BASE)
        exp = ('some ' + lean_stack(res)) if ok else 'none'
        init_s = lean_stack(list(init))
        line = '#eval evalScript %s O%s %s (%s) == %s' % (fl, oracle, init_s, lean_script(segs), exp)
        if comment: line += '   -- ' + comment
        if not ok: line += ('  [' if comment else '   -- [') + res + ']'
        L.append(line)

    def op(c): return c
    def opn(n): return OP_1 + n - 1 if n else OP_0

    L.append('-- 1. empty-stack and short-stack behaviour of every opcode that needs operands')
    unary = [OP_CHECKLOCKTIMEVERIFY, OP_CHECKSEQUENCEVERIFY, OP_IF, OP_NOTIF, OP_VERIFY, OP_TOALTSTACK, OP_IFDUP, OP_DROP,
             OP_DUP, OP_SIZE, OP_1ADD, OP_1SUB, OP_NEGATE, OP_ABS, OP_NOT, OP_0NOTEQUAL, OP_RIPEMD160, OP_SHA1, OP_SHA256,
             OP_HASH160, OP_HASH256, OP_CHECKMULTISIG, OP_CHECKMULTISIGVERIFY]
    for c in unary: vec([c], 'needs 1')
    binary = [OP_2DROP, OP_2DUP, OP_NIP, OP_OVER, OP_PICK, OP_ROLL, OP_SWAP, OP_TUCK, OP_EQUAL, OP_EQUALVERIFY, OP_ADD, OP_SUB,
              OP_BOOLAND, OP_BOOLOR, OP_NUMEQUAL, OP_NUMEQUALVERIFY, OP_NUMNOTEQUAL, OP_LESSTHAN, OP_GREATERTHAN,
              OP_LESSTHANOREQUAL, OP_GREATERTHANOREQUAL, OP_MIN, OP_MAX, OP_CHECKSIG, OP_CHECKSIGVERIFY]
    for c in binary: vec([b'\x01', c], 'needs 2')
    for c in [OP_3DUP, OP_ROT, OP_WITHIN]: vec([b'\x01', b'\x02', c], 'needs 3')
    for c in [OP_2OVER, OP_2SWAP]: vec([b'\x01', b'\x02', b'\x03', c], 'needs 4')
    vec([b'\x01', b'\x02', b'\x03', b'\x04', b'\x05', OP_2ROT], 'needs 6')
    vec([OP_FROMALTSTACK], 'empty altstack')
    vec([OP_ELSE], 'ELSE without IF'); vec([OP_ENDIF], 'ENDIF without IF')
    vec([OP_DEPTH], 'DEPTH on an empty stack pushes 0 = []')
    vec([OP_NOP], 'NOP leaves an empty stack: success with no element')
    L.append('-- 2. opcodes that fail only when executed, and those that fail even when skipped')
    for c in [OP_RESERVED, OP_VER, OP_RESERVED1, OP_RESERVED2, OP_CHECKSIGADD, 0xbb, OP_INVALIDOPCODE]:
        vec([c], 'executed: BAD_OPCODE')
        vec([OP_0, OP_IF, c, OP_ENDIF, OP_1], 'skipped: fine')
    for c in [OP_VERIF, OP_VERNOTIF]:
        vec([OP_0, OP_IF, c, OP_ENDIF, OP_1], 'in the IF..ENDIF range: fails even when skipped')
    for c in sorted(DISABLED):
        vec([OP_0, OP_IF, c, OP_ENDIF, OP_1], 'disabled, skipped')
    vec([OP_0, OP_IF, OP_RETURN, OP_ENDIF, OP_1], 'OP_RETURN skipped')
    vec([OP_0, OP_IF, OP_VERIFY, OP_ENDIF, OP_1], 'OP_VERIFY skipped on an empty stack')
    L.append('-- 3. push-size limit also in skipped branches; stack-size limit after skipped instructions')
    vec([OP_0, OP_IF, b'\x01' * 520, OP_ENDIF, OP_1], '520 bytes skipped')
    vec([OP_0, OP_IF, b'\x01' * 521, OP_ENDIF, OP_1], '521 bytes skipped: PUSH_SIZE')
    vec([b'\x01' * 520, OP_SIZE], 'SIZE of 520 bytes = [8,2]')
    vec([b'\x01' * 521], 'executed 521-byte push')
    vec([('rep', 999, [b'\x01']), OP_0, OP_IF, b'\x01', OP_ENDIF], '999 elements + the condition = 1000 (allowed); IF pops it; the skipped push adds nothing')
    vec([('rep', 1000, [b'\x01']), OP_0], '1001 elements: the 1001st push fails')
    vec([OP_NOTIF, b'\x01', OP_ENDIF], '1001 initial elements: NOTIF pops to 1000, the skipped push keeps 1000', init=[b'\x01'] * 1001)
    vec([OP_NOTIF, b'\x01', OP_ENDIF], '1002 initial elements: 1001 after NOTIF → STACK_SIZE', init=[b'\x01'] * 1002)
    vec([('rep', 999, [b'\x01']), OP_0, OP_IF, OP_DUP, OP_ENDIF], 'IF pops the condition: 999 elements; skipped DUP')
    vec([('rep', 1000, [b'\x01']), OP_TOALTSTACK, OP_1], '1000 pushes, TOALTSTACK (999 + 1), OP_1 → 1001 → STACK_SIZE')
    vec([('rep', 1000, [b'\x01']), OP_TOALTSTACK, OP_FROMALTSTACK], 'stays at 1000')
    L.append('-- 4. operation count: skipped opcodes count, pushes and OP_n do not; the 202nd fails before the disabled test')
    vec([OP_0, OP_IF, ('rep', 200, [OP_NOP]), OP_ENDIF, OP_1], 'IF+200 NOP+ENDIF = 202 counted → OP_COUNT')
    vec([OP_0, OP_IF, ('rep', 199, [OP_NOP]), OP_ENDIF, OP_1], 'IF+199 NOP+ENDIF = 201')
    vec([('rep', 201, [OP_NOP]), OP_CAT], 'the 202nd op fails with OP_COUNT, not DISABLED (same verdict)')
    vec([('rep', 100, [OP_1NEGATE, OP_0, OP_16]), ('rep', 201, [OP_NOP])], 'OP_1NEGATE, OP_0, OP_16 do not count')
    vec([('rep', 200, [OP_NOP]), OP_0, OP_0, OP_0, OP_CHECKMULTISIG], '200 + CMS(1) + 0 keys = 201')
    vec([('rep', 200, [OP_NOP]), OP_0, OP_0, b'\x05', OP_1, OP_CHECKMULTISIG], '200 + 1 + 1 key = 202')
    vec([('rep', 180, [OP_NOP]), OP_0, OP_0, ('rep', 20, [b'\x05']), b'\x14', OP_CHECKMULTISIG], '180 + 1 + 20 = 201')
    vec([OP_0, OP_0, ('rep', 20, [b'\x05']), b'\x14', OP_CHECKMULTISIG, OP_DROP, OP_0, OP_0, ('rep', 20, [b'\x05']), b'\x14', OP_CHECKMULTISIG], '21+1+21 = 43 keys counted across two CMS')
    L.append('-- 5. OP_1NEGATE..OP_16 values; OP_0 pushes the empty element')
    vec([OP_1NEGATE, OP_0, OP_1, opn(2), opn(15), OP_16], 'pushes -1, [], 1, 2, 15, 16')
    L.append('-- 6. CScriptNum: 4 bytes in, 5 bytes out; non-minimal operands accepted (MINIMALDATA is policy)')
    vec([b'\xff\xff\xff\x7f', OP_1ADD], '2^31-1 + 1 → 5 bytes')
    vec([b'\xff\xff\xff\xff', OP_1SUB], '-(2^31-1) - 1 → 5 bytes')
    vec([b'\xff\xff\xff\xff', OP_ABS], 'abs(-(2^31-1))')
    vec([b'\xff\xff\xff\x7f', OP_NEGATE], 'negate 2^31-1')
    vec([b'\xff\xff\xff\x7f', b'\xff\xff\xff\x7f', OP_ADD], '2^32-2')
    vec([b'\xff\xff\xff\xff', b'\xff\xff\xff\x7f', OP_SUB], '-(2^32-2)')
    vec([b'\xff\xff\xff\x7f', OP_1ADD, OP_1SUB], 'the 5-byte result cannot be an operand')
    vec([b'\x00\x00\x00\x80', OP_1ADD], '4-byte negative zero is 0')
    vec([b'\x01\x00\x00\x00', b'\x01', OP_NUMEQUAL], 'padded 1 equals 1')
    vec([b'\x80', b'\x00', OP_NUMEQUAL], '-0 equals 0')
    vec([b'\x00\x00\x00\x00\x00', OP_NOT], '5-byte operand: SCRIPTNUM')
    vec([b'\x01', b'\x00\x00\x00\x00\x00', OP_ADD], '5-byte second operand')
    vec([b'\xff\xff\xff\x7f', b'\xff\xff\xff\xff', OP_MIN], 'MIN')
    vec([b'\xff\xff\xff\x7f', b'\xff\xff\xff\xff', OP_MAX], 'MAX')
    vec([b'\x02', b'\x03', OP_LESSTHAN], '2 < 3'); vec([b'\x03', b'\x02', OP_LESSTHAN], '3 < 2')
    vec([b'\x83', b'\x82', OP_LESSTHANOREQUAL], '-3 <= -2'); vec([b'\x83', b'\x83', OP_GREATERTHANOREQUAL], '-3 >= -3')
    vec([b'\x83', b'\x82', OP_GREATERTHAN], '-3 > -2')
    vec([b'\x00', b'\x80', OP_BOOLAND], '0 and -0'); vec([b'\x02', b'\x80', OP_BOOLOR], '2 or -0'); vec([b'\x80', b'\x00', OP_BOOLOR], '-0 or 0')
    vec([b'\x05', b'\x05', OP_NUMNOTEQUAL], '5 != 5'); vec([b'\x05', b'\x06', OP_NUMNOTEQUAL], '5 != 6')
    vec([b'\x05', b'\x05\x00', OP_NUMEQUALVERIFY, OP_1], 'NUMEQUALVERIFY pops'); vec([b'\x05', b'\x06', OP_NUMEQUALVERIFY], 'NUMEQUALVERIFY fails')
    vec([b'\x05', b'\x05\x00', OP_EQUAL], 'EQUAL is bytewise: [5] ≠ [5,0]'); vec([b'\x05', b'\x05\x00', OP_EQUALVERIFY], 'EQUALVERIFY fails bytewise')
    vec([b'', b'', OP_EQUALVERIFY], 'EQUALVERIFY of two empties pops both')
    vec([OP_1NEGATE, OP_1NEGATE, b'\x02', OP_WITHIN], '-1 in [-1, 2)'); vec([b'\x02', OP_1NEGATE, b'\x02', OP_WITHIN], '2 in [-1, 2) is false')
    vec([b'\x80', b'\x00', b'\x01', OP_WITHIN], '-0 in [0,1)'); vec([b'\x80', OP_0, b'\x00\x00\x00\x00\x00', OP_WITHIN], '5-byte max: SCRIPTNUM')
    vec([b'\x80', OP_0NOTEQUAL], '-0 is zero'); vec([b'\x80', OP_NEGATE], 'negate -0 = 0'); vec([b'\x80', OP_ABS], 'abs -0')
    L.append('-- 7. OP_PICK/OP_ROLL index semantics (4-byte number, 0 = top after the pop)')
    vec([b'\x0a', b'\x0b', b'\x0c', b'\x02', OP_PICK], 'pick 2'); vec([b'\x0a', b'\x0b', b'\x0c', b'\x02', OP_ROLL], 'roll 2')
    vec([b'\x0a', b'\x0b', b'\x0c', b'\x02\x00\x00\x00', OP_ROLL], 'padded index 2 accepted')
    vec([b'\x0a', b'\x0b', b'\x0c', b'\x80', OP_PICK], 'index -0 = 0')
    vec([b'\x0a', b'\x0b', b'\x0c', b'\x03', OP_ROLL], 'index 3 with 3 elements: out of range')
    vec([b'\x0a', b'\x0b', b'\x0c', b'\xff\xff\xff\x7f', OP_PICK], 'huge index')
    vec([b'\x0a', b'\x0b', b'\x0c', b'\x02\x00\x00\x00\x00', OP_PICK], '5-byte index: SCRIPTNUM')
    vec([b'\x0a', b'\x00', OP_PICK], 'one element below the index: pick 0')
    vec([b'\x0a', b'\x01', OP_ROLL], 'one element below the index: roll 1 out of range')
    L.append('-- 8. stack shuffles once more, with distinct elements')
    vec([b'\x0a', b'\x0b', OP_TUCK], 'TUCK'); vec([b'\x0a', b'\x0b', OP_NIP], 'NIP'); vec([b'\x0a', b'\x0b', OP_OVER], 'OVER')
    vec([b'\x0a', b'\x0b', b'\x0c', OP_ROT], 'ROT'); vec([b'\x0a', b'\x0b', OP_SWAP], 'SWAP'); vec([b'\x0a', b'\x0b', OP_2DUP], '2DUP')
    vec([b'\x0a', b'\x0b', OP_2DROP], '2DROP'); vec([b'\x0a', b'\x0b', OP_TOALTSTACK, OP_TOALTSTACK, OP_FROMALTSTACK], 'altstack order')
    vec([b'\x80', OP_IFDUP], 'IFDUP of -0 does not duplicate'); vec([b'\x00\x01', OP_IFDUP], 'IFDUP of [0,1] duplicates')
    vec([b'\x0a', b'\x0b', OP_DEPTH, OP_DEPTH], 'DEPTH twice: 2 then 3')
    L.append('-- 9. conditionals: NOTIF, nesting, unbalanced at the end, condition popped only when executed')
    vec([OP_0, OP_NOTIF, OP_1, OP_ENDIF], 'NOTIF on false'); vec([b'\x80', OP_NOTIF, OP_1, OP_ENDIF], 'NOTIF on -0')
    vec([OP_1, OP_IF, OP_1], 'unbalanced IF'); vec([OP_0, OP_IF, OP_ENDIF, OP_ENDIF], 'extra ENDIF')
    vec([OP_0, OP_IF, OP_1, OP_IF, OP_ENDIF, OP_ENDIF, OP_1], 'skipped inner IF does not pop')
    vec([OP_1, OP_IF, OP_0, OP_IF, b'\x07', OP_ELSE, b'\x08', OP_ENDIF, OP_ELSE, b'\x09', OP_ENDIF], 'nested else')
    vec([OP_0, OP_IF, OP_ELSE, OP_ELSE, OP_1, OP_ENDIF], 'double ELSE on a false branch re-disables')
    vec([OP_0, OP_IF, OP_ELSE, OP_ELSE, OP_ELSE, OP_1, OP_ENDIF], 'triple ELSE')
    vec([b'\x00\x80', OP_IF, OP_1, OP_ELSE, b'\x02', OP_ENDIF], '[0,0x80] is false')
    vec([b'\x80\x00', OP_IF, OP_1, OP_ELSE, b'\x02', OP_ENDIF], '[0x80,0] is true')
    L.append('-- 10. OP_VERIFY, OP_RETURN, hashes through the oracle, OP_CODESEPARATOR as a no-op on the stack')
    vec([b'\x00\x80', OP_VERIFY], 'VERIFY on -0 fails'); vec([b'\x02', OP_VERIFY], 'VERIFY pops true'); vec([OP_1, OP_RETURN], 'RETURN')
    vec([b'\x01', OP_SHA256, OP_HASH160, OP_RIPEMD160, OP_SHA1, OP_HASH256], 'the five hashes')
    vec([OP_1, OP_CODESEPARATOR, OP_CODESEPARATOR], 'CODESEPARATOR counts as an op, no stack effect')
    vec([('rep', 201, [OP_CODESEPARATOR]), OP_1], '201 codeseparators'); vec([('rep', 202, [OP_CODESEPARATOR]), OP_1], '202')
    L.append('-- 11. CHECKSIG: result encoding, VERIFY, encoding failure (oracle none) is a script error')
    vec([b'\x07', b'\x05', OP_CHECKSIG], 'valid'); vec([b'\x08', b'\x05', OP_CHECKSIG], 'invalid → []')
    vec([b'\x08', b'\x05', OP_CHECKSIGVERIFY], 'CHECKSIGVERIFY invalid'); vec([b'\x07', b'\x05', OP_CHECKSIGVERIFY, OP_1], 'CHECKSIGVERIFY valid pops')
    vec([b'\xff', b'\x05', OP_CHECKSIG], 'encoding failure'); vec([b'', b'\x05', OP_CHECKSIG], 'empty signature → []')
    L.append('-- 12. CHECKMULTISIG: counts, ordering, early exit, encoding failures that are never reached, the dummy')
    vec([OP_0, OP_0, OP_0, OP_CHECKMULTISIG], '0-of-0 with dummy')
    vec([OP_0, OP_0, OP_CHECKMULTISIG], '0-of-0 without dummy')
    vec([OP_0, OP_1, OP_0, OP_CHECKMULTISIG], '1-of-0: SIG_COUNT')
    vec([OP_1NEGATE, OP_CHECKMULTISIG], 'nKeys -1: PUBKEY_COUNT')
    vec([OP_0, b'\x07', OP_1NEGATE, b'\x05', OP_1, OP_CHECKMULTISIG], 'nSigs -1: SIG_COUNT')
    vec([OP_0, b'\x07', OP_1, b'\x05', b'\x01\x00\x00\x00', OP_CHECKMULTISIG], 'padded nKeys accepted')
    vec([OP_0, b'\x07', OP_1, b'\x05', b'\x01\x00\x00\x00\x00', OP_CHECKMULTISIG], '5-byte nKeys: SCRIPTNUM')
    vec([OP_0, b'\x07', OP_1, b'\x05', b'\x80', OP_CHECKMULTISIG], 'nKeys -0 = 0: then nSigs=[5]... SIG_COUNT 5 > 0')
    vec([OP_0, b'\x07', b'\x0b', opn(2), b'\x05', b'\x09', opn(2), OP_CHECKMULTISIG], '2-of-2 in order')
    vec([OP_0, b'\x0b', b'\x07', opn(2), b'\x05', b'\x09', opn(2), OP_CHECKMULTISIG], '2-of-2 reversed: false')
    vec([OP_0, b'\xff', b'\x07', opn(2), b'\x05', b'\x09', opn(2), OP_CHECKMULTISIG], '[7] vs key [9] fails, 2 sigs > 1 key: exit before [0xff] is examined → false, no error')
    vec([OP_0, b'\x07', b'\xff', opn(2), b'\x05', b'\x09', opn(2), OP_CHECKMULTISIG], '[0xff] is the top signature: examined first → error')
    vec([OP_0, b'\xff', b'\x0b', opn(2), b'\x05', b'\x09', opn(2), OP_CHECKMULTISIG], '[11] matches key [9], then [0xff] vs [5] → error')
    vec([OP_0, b'\x07', b'\xff', opn(2), b'\x05', b'\x05', b'\x05', opn(3), OP_CHECKMULTISIG], '[0xff] on top against the first key → error')
    vec([OP_0, b'\x07', OP_1, b'\x09', b'\x09', b'\x05', opn(3), OP_CHECKMULTISIG], '1-of-3, sig matches the last key')
    vec([OP_0, b'\x07', OP_1, b'\x05', b'\x09', b'\x09', opn(3), OP_CHECKMULTISIG], '1-of-3, sig matches the first key')
    vec([OP_0, b'\x0b', OP_1, b'\x05', b'\x09', opn(2), OP_CHECKMULTISIGVERIFY, OP_1], 'CMSV success pops')
    vec([OP_0, b'\x0c', OP_1, b'\x05', b'\x09', opn(2), OP_CHECKMULTISIGVERIFY, OP_1], 'CMSV failure')
    vec([b'\x00', b'\x07', OP_1, b'\x05', OP_1, OP_CHECKMULTISIG], 'dummy [0] non-empty: NULLDUMMY')
    vec([b'\x00', b'\x07', OP_1, b'\x05', OP_1, OP_CHECKMULTISIG], 'NULLDUMMY off', fl='Fnd', flags=CONSENSUS_FLAGS - {'NULLDUMMY'})
    vec([b'\x07', OP_1, b'\x05', OP_1, OP_CHECKMULTISIG], 'no dummy at all')
    vec([OP_0, ('rep', 20, [b'\x07']), b'\x14', ('rep', 20, [b'\x05']), b'\x14', OP_CHECKMULTISIG], '20-of-20')
    vec([OP_0, ('rep', 21, [b'\x07']), b'\x15', ('rep', 21, [b'\x05']), b'\x15', OP_CHECKMULTISIG], '21 keys: PUBKEY_COUNT')
    vec([OP_0, b'\x07', opn(2), b'\x05', OP_1, OP_CHECKMULTISIG], 'nSigs 2 > nKeys 1')
    vec([b'\x07', OP_1, b'\x05', b'\x09', opn(2), OP_CHECKMULTISIG], 'stack too short for the dummy after a successful match')
    L.append('-- 13. CLTV semantics through the real checker: txA locks by time 600000000, input sequence 10')
    vec([b'\x00\x8d\x27\x00', OP_CHECKLOCKTIMEVERIFY], '2592000 < threshold but tx is time-locked: type mismatch', oracle='A')
    vec([b'\x00\x46\xc3\x23', OP_CHECKLOCKTIMEVERIFY], '600000000 == nLockTime: satisfied', oracle='A')
    vec([b'\x01\x46\xc3\x23', OP_CHECKLOCKTIMEVERIFY], '600000001 > nLockTime', oracle='A')
    vec([b'\x00\x65\xcd\x1d', OP_CHECKLOCKTIMEVERIFY], '500000000: time type, below', oracle='A')
    vec([b'\xff\x64\xcd\x1d', OP_CHECKLOCKTIMEVERIFY], '499999999: height type: mismatch', oracle='A')
    vec([b'\x00\x00\x00\x00\x01', OP_CHECKLOCKTIMEVERIFY], '2^32: 5-byte, time type, above', oracle='A')
    vec([b'\x00\x00\x00\x80', OP_CHECKLOCKTIMEVERIFY], '[0,0,0,0x80] = -0 = 0: height type vs a time-locked tx: mismatch', oracle='A')
    vec([b'\x81', OP_CHECKLOCKTIMEVERIFY], '-1: NEGATIVE_LOCKTIME', oracle='A')
    vec([b'\x81', OP_CHECKLOCKTIMEVERIFY], 'flag off: NOP', oracle='A', fl='Fnone', flags=frozenset())
    vec([b'\xe8\x03', OP_CHECKLOCKTIMEVERIFY], 'txB: 1000 == nLockTime but the input is final', oracle='B')
    vec([b'\xe7\x03', OP_CHECKLOCKTIMEVERIFY], 'txC: 999 ≤ 1000, height type, input not final', oracle='C')
    vec([OP_0, OP_CHECKLOCKTIMEVERIFY], 'txC: 0 (empty) ≤ 1000', oracle='C')
    vec([b'\x80', OP_CHECKLOCKTIMEVERIFY], 'txC: -0 is 0', oracle='C')
    vec([OP_1, OP_CHECKLOCKTIMEVERIFY], 'txD: 1 ≤ 499999999', oracle='D')
    L.append('-- 14. CSV semantics: txA height-type 10; txB version 1; txC time-type 10; txD disabled input')
    vec([b'\x0a', OP_CHECKSEQUENCEVERIFY], 'txA: 10 ≤ 10', oracle='A')
    vec([b'\x0b', OP_CHECKSEQUENCEVERIFY], 'txA: 11 > 10', oracle='A')
    vec([b'\x0a\x00\x40', OP_CHECKSEQUENCEVERIFY], 'txA: time-type 10 vs height-type input: mismatch', oracle='A')
    vec([b'\x0a\x00\x01', OP_CHECKSEQUENCEVERIFY], 'txA: bits outside the mask are ignored (0x01000a & mask = 10)', oracle='A')
    vec([b'\x0b\x00\x00\x80\x00', OP_CHECKSEQUENCEVERIFY], 'txA: 2^31+11 → disable flag set: NOP', oracle='A')
    vec([b'\x0b\x00\x00\x80', OP_CHECKSEQUENCEVERIFY], 'txA: [0b,0,0,0x80] is negative (-11): NEGATIVE_LOCKTIME', oracle='A')
    vec([b'\x00\x00\x00\x00\x01', OP_CHECKSEQUENCEVERIFY], 'txA: 2^32: no disable bit (bit 31 clear), masked 0 ≤ 10, height type', oracle='A')
    vec([OP_1, OP_CHECKSEQUENCEVERIFY], 'txB: version 1 → fail', oracle='B')
    vec([OP_0, OP_CHECKSEQUENCEVERIFY], 'txB: even 0 fails on version 1', oracle='B')
    vec([b'\x0a\x00\x40', OP_CHECKSEQUENCEVERIFY], 'txC: time-type 10 ≤ 10', oracle='C')
    vec([b'\x0b\x00\x40', OP_CHECKSEQUENCEVERIFY], 'txC: time-type 11 > 10', oracle='C')
    vec([b'\x0a', OP_CHECKSEQUENCEVERIFY], 'txC: height-type vs time-type input: mismatch', oracle='C')
    vec([OP_0, OP_CHECKSEQUENCEVERIFY], 'txD: input has the disable flag → fail', oracle='D')
    vec([b'\x00\x00\x00\x80\x00', OP_CHECKSEQUENCEVERIFY], 'txD: operand disable flag → NOP regardless', oracle='D')
    vec([b'\x0a', OP_CHECKSEQUENCEVERIFY], 'flag off: NOP', oracle='B', fl='Fnone', flags=frozenset())
    vec([b'\x0a\x00\x00\x00\x00\x00', OP_CHECKSEQUENCEVERIFY], '6-byte operand: SCRIPTNUM', oracle='A')
    L.append('-- 15. initial stacks (as for scriptPubKey after scriptSig): the count and altstack restart')
    vec([OP_DEPTH], 'DEPTH 3', init=[b'\x01', b'\x02', b'\x03'])
    vec([opn(2), OP_PICK], 'pick from the initial stack', init=[b'\x0a', b'\x0b', b'\x0c'])
    vec([OP_FROMALTSTACK], 'the altstack does not carry over', init=[b'\x01'])
    vec([('rep', 201, [OP_NOP])], 'the count restarts', init=[b'\x01'])
    vec([OP_DROP], 'a 1001-element initial stack is only tested after the first instruction', init=[b'\x01'] * 1001)
    vec([OP_DUP], '1001 → 1002 fails', init=[b'\x01'] * 1001)
    vec([OP_NOP], '1001 elements and a NOP: still over the limit after the op', init=[b'\x01'] * 1001)
    out = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'SecondReviewScriptVectors.lean')
    open(out, 'w').write('\n'.join(L) + '\n')
    print(sum(1 for l in L if l.startswith('#eval')), 'vectors ->', out)


if __name__ == '__main__':
    main()
