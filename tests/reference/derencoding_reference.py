import importlib.util, sys
spec=importlib.util.spec_from_file_location("base", "/tmp/claude-0/-home-user/a41a205d-c91a-5c07-937e-add1cb5cb340/scratchpad/der/base.py")
# reuse the signer by exec'ing the top part of base.py (before vector tables)
src=open(spec.origin).read().split("sigs=[")[0]
g={}; exec(src, g)
rb,sb,n,s,der,derint,comp=g['rb'],g['sb'],g['n'],g['s'],g['der'],g['derint'],g['comp']
strict=der(rb,sb)+b'\x01'   # with hash type ALL
def mut(i,v): b=bytearray(strict); b[i]=v; return bytes(b)
cases=[
 ("strict DER + hashtype", strict, True),
 ("8 bytes", strict[:8], False),
 ("74 bytes", strict+b'\x00', False),
 ("tag 0x31", mut(0,0x31), False),
 ("sequence length off by one", mut(1,strict[1]+1), False),
 ("R tag 0x03", mut(2,0x03), False),
 ("lenR covering the rest", mut(3,len(strict)-5), False),
 ("lenR + lenS + 7 != size (lenS - 1, length fixed)", mut(5+strict[3], strict[5+strict[3]]-1), False),
 ("lenR = 0 (rebuilt)", der(b'',sb)+b'\x01', False),
 ("R negative (high bit)", der(rb.lstrip(b'\x00') if rb[0]==0 else b'\x80'+rb[1:], sb)+b'\x01', False),
 ("R padded unnecessarily", der(b'\x00'+rb, sb)+b'\x01', False),
 ("S tag 0x03", mut(4+strict[3],0x03), False),
 ("lenS = 0 (rebuilt)", der(rb,b'')+b'\x01', False),
 ("S negative (high bit)", der(rb, b'\x80'+sb[1:])+b'\x01', False),
 ("S padded unnecessarily", der(rb, b'\x00'+sb)+b'\x01', False),
 ("high S is still valid DER", der(rb, derint(n-s))+b'\x01', True),
 ("hash type byte arbitrary (0xff)", strict[:-1]+b'\xff', True),
 ("minimal 9-byte signature", bytes.fromhex('300602010102010101'), True),
 ("73-byte maximal signature", bytes.fromhex('3046022100')+b'\xff'*32+bytes.fromhex('022100')+b'\xff'*32+b'\x01', True),
]
L=['import Definitions.Def_BitcoinSig','open BitcoinSig BitcoinSer',
'def hexDigit (c : Char) : Nat := if c.isDigit then c.toNat - 48 else if c.isLower then c.toNat - 87 else c.toNat - 55',
'def hx (s : String) : Bytes := let cs := s.toList; (List.range (cs.length / 2)).map fun i => BitVec.ofNat 8 (hexDigit (cs.getD (2*i) \'0\') * 16 + hexDigit (cs.getD (2*i+1) \'0\'))',
'def dersig : SigFlags := ⟨true, false, false, false⟩',
'def nofl : SigFlags := ⟨false, false, false, false⟩',
'/-! Spot 5 vectors (generator tests/reference/derencoding_reference.py): IsValidSignatureEncoding rule by rule. Every line prints `true`. -/']
for name,sig,exp in cases:
    L.append(f'#eval isValidSignatureEncoding (hx "{sig.hex()}") == {str(exp).lower()}   -- {name}')
L += ['-- CheckSignatureEncoding: the empty signature always passes; with DERSIG off nothing is checked; LOW_S and STRICTENC are policy',
 '#eval checkSignatureEncoding dersig [] == true',
 f'#eval checkSignatureEncoding dersig (hx "{mut(0,0x31).hex()}") == false',
 f'#eval checkSignatureEncoding nofl (hx "{mut(0,0x31).hex()}") == true',
 f'#eval checkSignatureEncoding nofl (hx "deadbeef") == true',
 f'#eval checkSignatureEncoding ⟨true, true, false, false⟩ (hx "{(der(rb, derint(n-s))+bytes([1])).hex()}") == false   -- LOW_S (policy) rejects a high S',
 f'#eval checkSignatureEncoding ⟨true, false, true, false⟩ (hx "{(strict[:-1]+bytes([0])).hex()}") == false   -- STRICTENC (policy) rejects hash type 0',
 f'#eval checkSignatureEncoding ⟨true, false, true, false⟩ (hx "{(strict[:-1]+bytes([0x83])).hex()}") == true    -- SINGLE|ANYONECANPAY is defined',
 '-- CheckPubKeyEncoding: consensus never sets STRICTENC or WITNESS_PUBKEYTYPE',
 f'#eval checkPubKeyEncoding dersig .base (hx "{(bytes([6])+comp[1:]+bytes([0])*32).hex()}") == true',
 f'#eval checkPubKeyEncoding ⟨true, false, true, false⟩ .base (hx "{(bytes([6])+comp[1:]+bytes([0])*32).hex()}") == false   -- hybrid rejected only by STRICTENC',
 f'#eval checkPubKeyEncoding ⟨true, false, false, true⟩ .witnessV0 (hx "{(bytes([4])+comp[1:]+bytes([0])*32).hex()}") == false   -- uncompressed rejected only by WITNESS_PUBKEYTYPE under v0',
 f'#eval checkPubKeyEncoding ⟨true, false, false, true⟩ .base (hx "{(bytes([4])+comp[1:]+bytes([0])*32).hex()}") == true',
]
open('/home/user/prove2me/tests/DerEncodingVectors.lean','w').write("\n".join(L)+"\n")
print(len(cases)+12)
