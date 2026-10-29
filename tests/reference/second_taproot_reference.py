#!/usr/bin/env python3
"""Second (independent) review reference for spot 8 (`Def_BitcoinTaproot`): the version-1 branch of
VerifyWitnessProgram, ExecuteWitnessScript under TAPSCRIPT, EvalChecksigTapscript, SignatureHashSchnorr,
VerifyTaprootCommitment, ComputeTapleafHash/ComputeTapbranchHash.  The consensus logic is in
second_script_reference.py (transcribed from the C++).  Writes tests/SecondReviewTaprootVectors.lean.
Run with `python3 -I`.
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from second_script_reference import *  # noqa

L = []
HERE = os.path.dirname(os.path.abspath(__file__))

# keys: internal key with even y, two leaf keys
d_int = 0x4444444444444444444444444444444444444444444444444444444444444444
d1 = 0x5555555555555555555555555555555555555555555555555555555555555555
d2 = 0x6666666666666666666666666666666666666666666666666666666666666666
def even_key(d):
    Pt = pmul(d, G)
    return (N - d, (Pt[0], P - Pt[1])) if Pt[1] & 1 else (d, Pt)
d_int, Pint = even_key(d_int)
d1, P1 = even_key(d1)
d2, P2 = even_key(d2)
X1, X2 = xonly(P1), xonly(P2)

# the spending transaction: two inputs, one output; both prevouts are taproot outputs (filled in later)
prev0 = bytes(range(32)); prev1 = bytes(range(32, 64))
vout = [(150000, b'\x51\x20' + bytes(32))]
AMOUNT = 100000


def make_tx(): return Tx(2, [(prev0, 0, b'', 0xfffffffe, []), (prev1, 1, b'', 0xffffffff, [])], vout, 0)


def tree(leaves):
    """leaves: list of (version, script).  Returns (root, [control-path bytes per leaf]) for a
    left-to-right balanced tree built pairwise, like a simple BIP341 builder."""
    hashes = [tapleaf_hash(v, s) for v, s in leaves]
    paths = [b'' for _ in leaves]
    groups = [[i] for i in range(len(leaves))]
    level = list(hashes)
    while len(level) > 1:
        nl, ng = [], []
        for i in range(0, len(level) - 1, 2):
            a, b = level[i], level[i + 1]
            for j in groups[i]: paths[j] += b
            for j in groups[i + 1]: paths[j] += a
            nl.append(tapbranch_hash(a, b)); ng.append(groups[i] + groups[i + 1])
        if len(level) % 2: nl.append(level[-1]); ng.append(groups[-1])
        level, groups = nl, ng
    return level[0], paths


class Output:
    """A taproot output committing to a tree of leaves."""
    def __init__(self, leaves):
        self.leaves = leaves
        self.root, self.paths = tree(leaves)
        self.Q, self.parity, self.t = taproot_tweak(Pint, self.root)
        self.program = xonly(self.Q)
        self.spk = b'\x51\x20' + self.program
        dq = (d_int + self.t) % N
        self.dq = N - dq if self.parity else dq   # the key-path signing key

    def control(self, i, version=None):
        v = self.leaves[i][0] if version is None else version
        return bytes([v | self.parity]) + xonly(Pint) + self.paths[i]


def spent_for(out, nIn=0):
    return [(AMOUNT, out.spk), (AMOUNT + 1, out.spk)] if nIn == 1 else [(AMOUNT, out.spk), (AMOUNT + 1, b'\x51\x20' + bytes(32))]


def lean_spent(spent): return '[' + ', '.join('⟨%d, hx "%s"⟩' % (v, s.hex()) for v, s in spent) + ']'
def lean_wit(w): return '[' + ', '.join(lean_hx(e) for e in w) + ']'


def run_handler(out, witness, nIn=0, program=None):
    """VerifyWitnessProgram version 1 with the TAPROOT flag: (ok, err)."""
    tx = make_tx(); spent = spent_for(out, nIn)
    checker = RealChecker(TxChecker(tx, nIn, AMOUNT, spent))
    try:
        verify_witness_program(witness, 1, out.program if program is None else program, CONSENSUS_FLAGS, checker, False)
        return True, 'OK'
    except ScriptError as e:
        return False, e.code


def H(out, witness, comment, nIn=0, program=None, core_expected=None):
    ok, err = run_handler(out, witness, nIn, program)
    if core_expected is not None: assert ok == core_expected, (comment, ok, err)
    spent = spent_for(out, nIn)
    prog = out.program if program is None else program
    line = '#eval taprootHandler %s (⟨allF, txT, %d, %d⟩ : Ctx) %s (hx "%s") == %s   -- %s' % (
        lean_spent(spent), nIn, AMOUNT, lean_wit(witness), prog.hex(), str(ok).lower(), comment)
    if not ok: line += ' [' + err + ']'
    L.append(line)


def sig_key(out, hashtype=0, nIn=0, annex=None):
    tx = make_tx(); ed = ExecData(); ed.annex_present = annex is not None
    if annex is not None: ed.annex_hash = sha256(ser_bytes(annex))
    h = sighash_schnorr(tx, spent_for(out, nIn), nIn, hashtype, TAPROOT, ed)
    if h is None: return None
    s = schnorr_sign(out.dq, h)
    return s if hashtype == 0 else s + bytes([hashtype])


def sig_leaf(d, out, i, hashtype=0, nIn=0, annex=None, codesep=0xFFFFFFFF, version=None):
    tx = make_tx(); ed = ExecData(); ed.annex_present = annex is not None
    if annex is not None: ed.annex_hash = sha256(ser_bytes(annex))
    v, script = out.leaves[i]
    ed.tapleaf_hash = tapleaf_hash(v if version is None else version, script); ed.codeseparator_pos = codesep
    h = sighash_schnorr(tx, spent_for(out, nIn), nIn, hashtype, TAPSCRIPT, ed)
    if h is None: return None
    s = schnorr_sign(d, h)
    return s if hashtype == 0 else s + bytes([hashtype])


def ps(b): return push_bytes(b)


L.append('import Definitions.Def_BitcoinTaproot')
L.append('open BitcoinSer BitcoinSig BitcoinVerify BitcoinTaproot')
L.append('/-! Second-review vectors for spot 8 (`Def_BitcoinTaproot`: `taprootHandler`, `executeTapscript`,')
L.append('`tapExecOp`, `evalChecksigTapscript`, `sigHashSchnorr`, `verifyTaprootCommitment`, `hasAnnex`), generated by')
L.append('tests/reference/second_taproot_reference.py from the version-1 branch of `VerifyWitnessProgram` and the')
L.append('TAPSCRIPT rules of `EvalScript`/`ExecuteWitnessScript`.  Every line must print `true`. -/')
L.append('def hexDigit (c : Char) : Nat := if c.isDigit then c.toNat - 48 else if c.isLower then c.toNat - 87 else c.toNat - 55')
L.append('def hx (s : String) : Bytes := let cs := s.toList; (List.range (cs.length / 2)).map fun i => BitVec.ofNat 8 (hexDigit (cs.getD (2*i) \'0\') * 16 + hexDigit (cs.getD (2*i+1) \'0\'))')
L.append('def allF : BitcoinActivation.ScriptFlags := ⟨true, true, true, true, true, true, true⟩')
tx0 = make_tx()
L.append('def txT : Tx := ⟨2, [⟨⟨hx "%s", 0⟩, [], %d, []⟩, ⟨⟨hx "%s", 1⟩, [], %d, []⟩], [⟨%d, hx "%s"⟩], 0⟩' % (
    prev0.hex(), tx0.vin[0][3], prev1.hex(), tx0.vin[1][3], vout[0][0], vout[0][1].hex()))

# ---- outputs
csig1 = ps(X1) + bytes([OP_CHECKSIG])                 # <X1> CHECKSIG
O1 = Output([(0xc0, csig1)])                           # single leaf
notif = bytes([OP_NOTIF]) + ps(X1) + bytes([OP_CHECKSIG, OP_ELSE, OP_1, OP_ENDIF])   # NOTIF <X1> CHECKSIG ELSE 1 ENDIF
csep_mid = bytes([OP_1, OP_DROP, OP_CODESEPARATOR]) + csig1                           # positions 0,1,2
csep_skip = bytes([OP_0, OP_IF, OP_CODESEPARATOR, OP_ENDIF]) + csig1
csep_two = bytes([OP_CODESEPARATOR, OP_CODESEPARATOR]) + csig1
csep_after = csig1 + bytes([OP_CODESEPARATOR])
csadd_n = lambda n: n + ps(X1) + bytes([OP_CHECKSIGADD])                                # <n> <X1> CHECKSIGADD
x33 = b'\x02' + X1                                                                       # a 33-byte "pubkey": unknown type
xbad = bytes([0xff] * 32)                                                                # not a valid x coordinate
leaves2 = [
    (0xc0, notif), (0xc0, csep_mid), (0xc0, csep_skip), (0xc0, csep_two), (0xc0, csep_after),
    (0xc0, csadd_n(ps(b'\xff\xff\xff\x7f')) + ps(b'\x00\x00\x00\x80\x00') + bytes([OP_EQUAL])),   # 2^31-1 + 1 → 5 bytes
    (0xc0, csadd_n(ps(b'\x00\x00\x00\x00\x01')) + bytes([OP_DROP, OP_1])),                        # 5-byte n
    (0xc0, csadd_n(bytes([OP_1]))),                                                              # 1 + success
    (0xc0, ps(b'\x01') + ps(x33) + bytes([OP_CHECKSIGADD])),                                     # unknown key type
    (0xc0, ps(x33) + bytes([OP_CHECKSIG])),
    (0xc0, ps(b'') + bytes([OP_CHECKSIG])),                                                      # empty pubkey
    (0xc0, ps(xbad) + bytes([OP_CHECKSIG])),                                                     # invalid x
    (0xc0, bytes([OP_1, OP_IF, OP_0, OP_0, OP_CHECKMULTISIG, OP_ENDIF])),                        # executed CMS
    (0xc0, bytes([OP_0, OP_IF, OP_0, OP_0, OP_CHECKMULTISIG, OP_ENDIF, OP_1])),                  # skipped CMS
    (0xc0, bytes([OP_0, OP_IF, OP_RESERVED, OP_ENDIF, OP_1])),                                   # OP_SUCCESS80 skipped
    (0xc0, bytes([OP_RESERVED, OP_PUSHDATA1])),                                                  # success before a bad push
    (0xc0, bytes([OP_PUSHDATA1, OP_RESERVED])),                                                  # bad push before success
    (0xc0, bytes([OP_0, OP_IF, OP_INVALIDOPCODE, OP_ENDIF, OP_1])),                              # 0xff skipped
    (0xc0, bytes([OP_1, OP_IF, OP_INVALIDOPCODE, OP_ENDIF, OP_1])),                              # 0xff executed
    (0xc0, bytes([OP_0, OP_IF, OP_VERIF, OP_ENDIF, OP_1])),                                      # OP_VERIF skipped
    (0xc0, bytes([OP_NOP]) * 300 + bytes([OP_1])),                                               # no op count
    (0xc0, bytes([OP_CODESEPARATOR]) * 250 + bytes([OP_1])),
    (0xc0, bytes([OP_DROP]) * 999 + bytes([OP_1])),                                              # 1000-element stacks
    (0xc0, bytes([OP_2DROP]) * 1 + bytes([OP_1])),
    (0xc0, bytes([OP_DROP, OP_1])),
    (0xc0, bytes([OP_1, OP_IF, OP_1, OP_ENDIF])),                                                # IF on [01]
    (0xc0, bytes([OP_CHECKSIGADD])),                                                             # too few elements
    (0xc0, bytes([OP_CHECKSIGVERIFY, OP_1])),                                                    # CHECKSIGVERIFY
    (0xc2, b'\x4c'),                                                                             # unknown leaf version, garbage script
    (0xfe, csig1),                                                                               # leaf version 0xfe
    (0xc0, bytes([OP_CHECKSIG, OP_NOT])),                                                        # CHECKSIG with witness pubkey
    (0xc0, ps(b'\xff\xff\xff\x7f') + ps(b'\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00') + bytes([OP_CHECKSIGADD, OP_DROP, OP_1])),  # 33-byte key, CHECKSIGADD
]
O2 = Output(leaves2)
I = {name: i for i, name in enumerate(['notif', 'csep_mid', 'csep_skip', 'csep_two', 'csep_after', 'csadd_big', 'csadd_5b', 'csadd_1',
                                       'csadd_x33', 'cs_x33', 'cs_empty', 'cs_xbad', 'cms_exec', 'cms_skip', 'succ_skip', 'succ_badpush',
                                       'badpush_succ', 'ff_skip', 'ff_exec', 'verif_skip', 'nops', 'cseps', 'drop999', 'drop2', 'drop1',
                                       'if01', 'csadd_short', 'csv', 'leaf_c2', 'leaf_fe', 'cs_not', 'csadd_x33b'])}
spk1_hex = O1.spk.hex()

L.append('-- 1. key path: signature sizes, hash types, the output key, SIGHASH_SINGLE out of range at input 1')
H(O1, [sig_key(O1)], 'key path, SIGHASH_DEFAULT')
H(O1, [sig_key(O1, 0x81)], 'ALL|ANYONECANPAY')
H(O1, [sig_key(O1, 0x82)], 'NONE|ANYONECANPAY')
H(O1, [sig_key(O1, 2)], 'NONE')
H(O1, [sig_key(O1)[:63]], '63 bytes')
H(O1, [sig_key(O1) + b'\x01\x01'], '66 bytes')
H(O1, [sig_key(O1, 1)[:64] + b'\x04'], 'hash type 0x04')
H(O1, [sig_key(O1, 1)[:64] + b'\x80'], 'hash type 0x80')
H(O1, [sig_key(O1, 1)[:64] + b'\x00'], 'explicit hash type 0x00')
H(O1, [sig_key(O1, 1)[:64]], 'a SIGHASH_ALL signature without its byte is checked as DEFAULT: the hash_type byte differs → false')
H(O1, [sig_key(O1)], 'the program is the internal key, not the tweaked one', program=xonly(Pint))
H(O1, [sig_key(O1, 3, nIn=0)], 'SINGLE at input 0: output 0 exists')
H(O1, [sig_key(O1, 1, nIn=1)], 'input 1, ALL', nIn=1)
H(O1, [sig_key(O1, 0x81, nIn=1)], 'input 1, ALL|ANYONECANPAY (spent output 1 serialized)', nIn=1)
H(O1, [sig_key(O1, 2, nIn=1)[:64] + b'\x03'], 'input 1, SINGLE: no output 1 → SCHNORR_SIG_HASHTYPE', nIn=1)
H(O1, [sig_key(O1, 2, nIn=1)[:64] + b'\x83'], 'input 1, SINGLE|ANYONECANPAY: likewise', nIn=1)
L.append('-- 2. the annex: at least two elements, the last non-empty and starting with 0x50')
H(O1, [sig_key(O1, annex=b'\x50'), b'\x50'], 'one-byte annex')
H(O1, [sig_key(O1), b'\x50'], 'the annex must be committed')
H(O1, [sig_key(O1, annex=b'\x50'), b'\x50\x00'], 'annex [50,00] with a signature over annex [50]')
H(O1, [sig_key(O1), b''], 'an empty last element is not an annex: script path with an empty control block')
H(O1, [sig_key(O1), b'\x51'], 'last element [51]: not an annex, control block too short')
H(O1, [b'\x50' + bytes(63)], 'a single element starting with 0x50 is a (bad) signature, not an annex')
H(O1, [b'\x50', sig_key(O1)], 'the annex must be last: [50] then a signature is a script path with a 64-byte control')
a20 = b'\x50' + bytes(range(1, 20))
H(O1, [sig_leaf(d1, O1, 0, annex=a20), csig1, O1.control(0), a20], 'script path with a 20-byte annex')
H(O1, [sig_leaf(d1, O1, 0), csig1, O1.control(0), a20], 'script path, annex not committed')
H(O1, [sig_leaf(d1, O1, 0, annex=a20), csig1, O1.control(0)], 'annex committed but absent')
L.append('-- 3. control block size and the commitment')
H(O1, [sig_leaf(d1, O1, 0), csig1, O1.control(0)], 'single leaf, 33-byte control')
H(O1, [sig_leaf(d1, O1, 0), csig1, O1.control(0) + b'\x00'], '34 bytes')
H(O1, [sig_leaf(d1, O1, 0), csig1, O1.control(0)[:32]], '32 bytes')
H(O1, [sig_leaf(d1, O1, 0), csig1, O1.control(0)[:1] + xbad + O1.control(0)[33:]], 'internal key is not a valid x coordinate')
H(O1, [sig_leaf(d1, O1, 0), csig1, O1.control(0)[:1] + X2 + O1.control(0)[33:]], 'another internal key')
H(O1, [sig_leaf(d1, O1, 0), csig1, bytes([O1.control(0)[0] ^ 1]) + O1.control(0)[1:]], 'wrong parity bit')
H(O1, [sig_leaf(d1, O1, 0), csig1 + b'\x61', O1.control(0)], 'a different script: leaf hash mismatch')
H(O1, [sig_leaf(d1, O1, 0), csig1, O1.control(0)], 'the program of another output', program=O2.program)
# a 128-deep path: one real leaf with 128 arbitrary sibling hashes
leaf_h = tapleaf_hash(0xc0, csig1); k = leaf_h; path = b''
for i in range(128):
    sib = sha256(bytes([i]) * 4); path += sib; k = tapbranch_hash(k, sib)
Qd, pard, td = taproot_tweak(Pint, k)
deep = Output([(0xc0, csig1)]); deep.root = k; deep.paths = [path]; deep.Q, deep.parity, deep.t = Qd, pard, td
deep.program = xonly(Qd); deep.spk = b'\x51\x20' + deep.program; deep.dq = (N - (d_int + td) % N) if pard else (d_int + td) % N
H(deep, [sig_leaf(d1, deep, 0), csig1, deep.control(0)], '128 path nodes: 4129-byte control block')
H(deep, [sig_leaf(d1, deep, 0), csig1, deep.control(0) + sha256(b'x')], '129 nodes: 4161 bytes → WRONG_CONTROL_SIZE')
H(deep, [sig_leaf(d1, deep, 0), csig1, deep.control(0)[:-32]], '127 nodes: commitment fails')
L.append('-- 4. leaf versions: the low bit is the parity; unknown versions succeed without executing')
H(O2, [b'\x4c', O2.control(I['leaf_c2'])], 'leaf version 0xc2 with an unparsable script: true')
H(O2, [b'\x4c', O2.control(I['leaf_c2'], 0xc0)], 'the same leaf claimed as 0xc0: commitment fails')
H(O2, [csig1, O2.control(I['leaf_fe'])], 'leaf version 0xfe (control byte 0xfe|parity): true')
H(O2, [b'', csig1, O2.control(I['leaf_fe'], 0xc0)], 'claimed as 0xc0: commitment fails')
H(O1, [sig_leaf(d1, O1, 0), csig1, bytes([0xc0 | O1.parity]) + O1.control(0)[1:]], 'control byte c0|parity')
L.append('-- 5. OP_SUCCESSx: the scan precedes everything, a malformed push before it fails')
H(O2, [O2.leaves[I['succ_skip']][1], O2.control(I['succ_skip'])], 'OP_SUCCESS80 in an unexecuted branch: true')
H(O2, [O2.leaves[I['succ_badpush']][1], O2.control(I['succ_badpush'])], 'OP_SUCCESS80 then a truncated PUSHDATA1: true')
H(O2, [O2.leaves[I['badpush_succ']][1], O2.control(I['badpush_succ'])], 'truncated push first → BAD_OPCODE')
H(O2, [b'\x01'] * 1200 + [O2.leaves[I['succ_skip']][1], O2.control(I['succ_skip'])], '1200 witness elements with OP_SUCCESS: true')
H(O2, [bytes(1000)] + [O2.leaves[I['succ_skip']][1], O2.control(I['succ_skip'])], 'a 1000-byte element with OP_SUCCESS: true')
H(O2, [O2.leaves[I['ff_skip']][1], O2.control(I['ff_skip'])], '0xff is not OP_SUCCESS; skipped: true')
H(O2, [O2.leaves[I['ff_exec']][1], O2.control(I['ff_exec'])], '0xff executed → BAD_OPCODE')
H(O2, [O2.leaves[I['verif_skip']][1], O2.control(I['verif_skip'])], 'OP_VERIF skipped: still BAD_OPCODE (IF..ENDIF range)')
L.append('-- 6. no operation count, 1000-element limit on the initial stack, 520-byte elements')
H(O2, [O2.leaves[I['nops']][1], O2.control(I['nops'])], '300 NOPs: no op count in Tapscript')
H(O2, [O2.leaves[I['cseps']][1], O2.control(I['cseps'])], '250 CODESEPARATORs')
H(O2, [b'\x01'] * 999 + [O2.leaves[I['drop999']][1], O2.control(I['drop999'])], '999 initial elements, 999 DROPs, then OP_1')
H(O2, [b'\x01'] * 1000 + [O2.leaves[I['drop999']][1], O2.control(I['drop999'])], '1000 initial elements: 999 DROP leaves 1, then OP_1: two elements → CLEANSTACK')
H(O2, [b'\x01'] * 1001 + [O2.leaves[I['drop2']][1], O2.control(I['drop2'])], '1001 initial elements → STACK_SIZE before execution')
H(O2, [b'\x01'] * 1000 + [O2.leaves[I['drop2']][1], O2.control(I['drop2'])], '1000: 2DROP then OP_1 leaves 999 → CLEANSTACK')
H(O2, [b'\x01', b'\x01'] + [O2.leaves[I['drop2']][1], O2.control(I['drop2'])], '2DROP of two then OP_1')
H(O2, [bytes(520), O2.leaves[I['drop1']][1], O2.control(I['drop1'])], 'a 520-byte element dropped')
H(O2, [bytes(521), O2.leaves[I['drop1']][1], O2.control(I['drop1'])], 'a 521-byte element → PUSH_SIZE')
L.append('-- 7. MINIMALIF is consensus in Tapscript (IF and NOTIF)')
H(O2, [O2.leaves[I['if01']][1], O2.control(I['if01'])], 'IF on the OP_1 push [01]')
nf = I['notif']; sn = sig_leaf(d1, O2, nf)
H(O2, [sn, b'', notif, O2.control(nf)], 'NOTIF on []: takes the CHECKSIG branch')
H(O2, [b'\x01', notif, O2.control(nf)], 'NOTIF on [01]: the ELSE branch')
H(O2, [b'\x02', notif, O2.control(nf)], 'NOTIF on [02] → TAPSCRIPT_MINIMALIF')
H(O2, [b'\x00', notif, O2.control(nf)], 'NOTIF on [00] → MINIMALIF')
H(O2, [b'\x01\x00', notif, O2.control(nf)], 'NOTIF on [01,00] → MINIMALIF')
H(O2, [b'\x80', notif, O2.control(nf)], 'NOTIF on [80] → MINIMALIF')
H(O2, [notif, O2.control(nf)], 'NOTIF on an empty stack → fail')
L.append('-- 8. OP_CODESEPARATOR positions count every instruction; only executed separators count; the last one wins')
cm = I['csep_mid']
H(O2, [sig_leaf(d1, O2, cm, codesep=2), csep_mid, O2.control(cm)], 'OP_1 OP_DROP CODESEP <X1> CHECKSIG: position 2')
H(O2, [sig_leaf(d1, O2, cm, codesep=0xFFFFFFFF), csep_mid, O2.control(cm)], 'signature over no separator → false')
H(O2, [sig_leaf(d1, O2, cm, codesep=1), csep_mid, O2.control(cm)], 'position 1 → false')
ck = I['csep_skip']
H(O2, [sig_leaf(d1, O2, ck, codesep=0xFFFFFFFF), csep_skip, O2.control(ck)], 'separator inside a skipped branch: position stays 0xFFFFFFFF')
H(O2, [sig_leaf(d1, O2, ck, codesep=2), csep_skip, O2.control(ck)], 'signature over position 2 → false')
ct = I['csep_two']
H(O2, [sig_leaf(d1, O2, ct, codesep=1), csep_two, O2.control(ct)], 'two separators: position 1')
H(O2, [sig_leaf(d1, O2, ct, codesep=0), csep_two, O2.control(ct)], 'position 0 → false')
ca = I['csep_after']
H(O2, [sig_leaf(d1, O2, ca, codesep=0xFFFFFFFF), csep_after, O2.control(ca)], 'a separator after CHECKSIG: irrelevant')
L.append('-- 9. OP_CHECKSIGADD: stack order, the 4-byte n, 5-byte results, unknown key types, empty/invalid keys')
cb = I['csadd_big']
H(O2, [sig_leaf(d1, O2, cb), O2.leaves[cb][1], O2.control(cb)], 'n = 2^31-1 (4 bytes) + 1 = 2^31 (5 bytes) compared bytewise')
c5 = I['csadd_5b']
H(O2, [sig_leaf(d1, O2, c5), O2.leaves[c5][1], O2.control(c5)], 'n of 5 bytes → SCRIPTNUM even with a valid signature')
c1 = I['csadd_1']
H(O2, [sig_leaf(d1, O2, c1), O2.leaves[c1][1], O2.control(c1)], '1 + valid signature = 2: true (2 is true)')
H(O2, [b'', O2.leaves[c1][1], O2.control(c1)], '1 + empty signature = 1: true')
H(O2, [sig_leaf(d2, O2, c1), O2.leaves[c1][1], O2.control(c1)], 'a non-empty signature by another key → SCHNORR_SIG')
H(O2, [bytes(64), O2.leaves[c1][1], O2.control(c1)], '64 zero bytes → SCHNORR_SIG')
H(O2, [b'\x01', O2.leaves[c1][1], O2.control(c1)], 'a 1-byte signature → SCHNORR_SIG_SIZE')
cx = I['csadd_x33']
H(O2, [b'\x01', O2.leaves[cx][1], O2.control(cx)], '33-byte key, 1-byte signature: no check, counts as success: 1+1 = 2')
H(O2, [b'', O2.leaves[cx][1], O2.control(cx)], '33-byte key, empty signature: 1+0 = 1')
H(O2, [b'', b'', O2.leaves[cx][1], O2.control(cx)], 'two elements left → CLEANSTACK')
ce = I['cs_empty']
H(O2, [b'', O2.leaves[ce][1], O2.control(ce)], 'empty pubkey, empty signature → TAPSCRIPT_EMPTY_PUBKEY')
H(O2, [b'\x01', O2.leaves[ce][1], O2.control(ce)], 'empty pubkey, 1-byte signature → EMPTY_PUBKEY')
cxb = I['cs_xbad']
H(O2, [b'', O2.leaves[cxb][1], O2.control(cxb)], 'invalid x, empty signature: no check → CHECKSIG false → EVAL_FALSE')
H(O2, [bytes(64), O2.leaves[cxb][1], O2.control(cxb)], 'invalid x, 64-byte signature → SCHNORR_SIG')
c33 = I['cs_x33']
H(O2, [b'\x01', O2.leaves[c33][1], O2.control(c33)], 'CHECKSIG with a 33-byte key and a 1-byte signature: true')
H(O2, [b'', O2.leaves[c33][1], O2.control(c33)], 'CHECKSIG with a 33-byte key and an empty signature: false')
cs_ = I['csadd_short']
H(O2, [b'', b'', O2.leaves[cs_][1], O2.control(cs_)], 'CHECKSIGADD with two elements → INVALID_STACK_OPERATION')
cv = I['csv']
H(O2, [sig_leaf(d1, O2, cv), X1, O2.leaves[cv][1], O2.control(cv)], 'CHECKSIGVERIFY with the key from the witness, then OP_1')
H(O2, [b'', X1, O2.leaves[cv][1], O2.control(cv)], 'CHECKSIGVERIFY with an empty signature → CHECKSIGVERIFY')
cn = I['cs_not']
H(O2, [b'', X1, O2.leaves[cn][1], O2.control(cn)], 'CHECKSIG NOT with an empty signature: true')
cb33 = I['csadd_x33b']
H(O2, [b'\x01', O2.leaves[cb33][1], O2.control(cb33)], 'CHECKSIGADD with a 33-byte zero key and 4-byte n: no check, drop, OP_1')
L.append('-- 10. OP_CHECKMULTISIG(VERIFY) fail only when executed')
H(O2, [O2.leaves[I['cms_exec']][1], O2.control(I['cms_exec'])], 'executed → TAPSCRIPT_CHECKMULTISIG')
H(O2, [O2.leaves[I['cms_skip']][1], O2.control(I['cms_skip'])], 'skipped: fine')
L.append('-- 11. the validation-weight budget: witness size (annex included) + 50; unknown key types count')
def budget_out(k, key):
    sc = bytes([OP_DUP]) * k + (ps(key) + bytes([OP_CHECKSIGVERIFY])) * k + ps(key) + bytes([OP_CHECKSIG])
    return Output([(0xc0, sc)]), sc
for k in [9, 10]:
    ob, sc = budget_out(k, X1)
    s = sig_leaf(d1, ob, 0)
    wit = [s, sc, ob.control(0)]
    size = len(ser_vector(wit, ser_bytes)); H(ob, wit, '%d checks cost %d, budget %d+50' % (k + 1, 50 * (k + 1), size))
ob, sc = budget_out(10, X1)
ann = b'\x50' + bytes(20)
s = sig_leaf(d1, ob, 0, annex=ann); wit = [s, sc, ob.control(0), ann]
H(ob, wit, 'the same 11 checks with a 21-byte annex: budget %d+50 ≥ 550' % len(ser_vector(wit, ser_bytes)))
ob, sc = budget_out(12, x33)
wit = [b'\x01', sc, ob.control(0)]
H(ob, wit, '13 checks with a 33-byte key and a 1-byte signature: no verification but 650 > %d+50' % len(ser_vector(wit, ser_bytes)))
ob, sc = budget_out(4, x33)
wit = [b'\x01', sc, ob.control(0)]
H(ob, wit, '5 such checks: 250 ≤ %d+50' % len(ser_vector(wit, ser_bytes)))
sc = (ps(b'') + ps(b'') + ps(X1) + bytes([OP_CHECKSIGADD, OP_DROP])) * 30 + bytes([OP_1])
ob = Output([(0xc0, sc)])
H(ob, [sc, ob.control(0)], '30 CHECKSIGADDs with empty signatures: no weight consumed')
L.append('-- 12. end to end through verifyScriptFull')
L.append('def spent1 : List TxOut := %s' % lean_spent(spent_for(O1)))
def E(scriptSig, spk, witness, comment, nIn=0):
    tx = make_tx(); spent = spent_for(O1, nIn)
    ok, err = verify_script(scriptSig, spk, witness, CONSENSUS_FLAGS, RealChecker(TxChecker(tx, nIn, AMOUNT, spent)))
    line = '#eval verifyScriptFull spent1 (⟨allF, txT, %d, %d⟩ : Ctx) (%s) (%s) %s == %s   -- %s' % (
        nIn, AMOUNT, lean_hx(scriptSig), lean_hx(spk), lean_wit(witness), str(ok).lower(), comment)
    if not ok: line += ' [' + err + ']'
    L.append(line)
E(b'', O1.spk, [sig_key(O1)], 'key path through VerifyScript')
E(b'', O1.spk, [sig_leaf(d1, O1, 0), csig1, O1.control(0)], 'script path through VerifyScript')
E(b'\x00', O1.spk, [sig_key(O1)], 'non-empty scriptSig → WITNESS_MALLEATED')
E(b'', O1.spk, [], 'empty witness → WITNESS_PROGRAM_WITNESS_EMPTY')
E(push_bytes(O1.spk), bytes([OP_HASH160]) + push_bytes(hash160(O1.spk)) + bytes([OP_EQUAL]), [b'\x01'], 'P2SH-wrapped: no taproot, anyone can spend')
L.append('-- 13. sigHashSchnorr directly: SINGLE at input 1 is none, the ext_flag/key_version bytes differ between key and script path')
tx = make_tx(); ed = ExecData(); ed.annex_present = False
for ht in [0, 1, 3, 0x83]:
    h = sighash_schnorr(tx, spent_for(O1, 1), 1, ht, TAPROOT, ed)
    L.append('#eval sigHashSchnorr txT %s 1 %d false ⟨false, [], [], 0xFFFFFFFF⟩ == %s   -- input 1, hash type %d' % (
        lean_spent(spent_for(O1, 1)), ht, ('some (hx "%s")' % h.hex()) if h else 'none', ht))
ed.tapleaf_hash = tapleaf_hash(0xc0, csig1); ed.codeseparator_pos = 7
h = sighash_schnorr(tx, spent_for(O1, 1), 1, 0x82, TAPSCRIPT, ed)
L.append('#eval sigHashSchnorr txT %s 1 0x82 true ⟨false, [], hx "%s", 7⟩ == some (hx "%s")   -- tapscript, NONE|ANYONECANPAY, codeseparator 7' % (
    lean_spent(spent_for(O1, 1)), ed.tapleaf_hash.hex(), h.hex()))
h0 = sighash_schnorr(tx, spent_for(O1, 1), 1, 0, TAPROOT, ed); h1 = sighash_schnorr(tx, spent_for(O1, 1), 1, 1, TAPROOT, ed)
L.append('#eval (sigHashSchnorr txT %s 1 0 false ⟨false, [], [], 0xFFFFFFFF⟩ == sigHashSchnorr txT %s 1 1 false ⟨false, [], [], 0xFFFFFFFF⟩) == false   -- DEFAULT and ALL hash differently (the hash_type byte)' % (
    lean_spent(spent_for(O1, 1)), lean_spent(spent_for(O1, 1))))
assert h0 != h1

out = os.path.join(HERE, '..', 'SecondReviewTaprootVectors.lean')
open(out, 'w').write('\n'.join(L) + '\n')
print(sum(1 for l in L if l.startswith('#eval')), 'vectors ->', out)
