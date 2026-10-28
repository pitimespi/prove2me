import hashlib
p=0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
n=0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
G=(0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798,0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8)
def inv(a,m): return pow(a,m-2,m)
def padd(P,Q):
    if P is None: return Q
    if Q is None: return P
    if P[0]==Q[0] and (P[1]+Q[1])%p==0: return None
    if P==Q: l=3*P[0]*P[0]*inv(2*P[1],p)%p
    else: l=(Q[1]-P[1])*inv(Q[0]-P[0],p)%p
    x=(l*l-P[0]-Q[0])%p; return (x,(l*(P[0]-x)-P[1])%p)
def pmul(k,P):
    R=None
    while k:
        if k&1: R=padd(R,P)
        P=padd(P,P); k>>=1
    return R
d=0x1E99423A4ED27608A15A2616A2B0E9E52CED330AC530EDCC32C8FFC6A526AEDD
Q=pmul(d,G)
z=int.from_bytes(hashlib.sha256(b"spot 4").digest(),'big')
k=0x5F3B1C2D4E6F708192A3B4C5D6E7F8091A2B3C4D5E6F708192A3B4C5D6E7F809
R=pmul(k,G); r=R[0]%n; s=inv(k,n)*(z+r*d)%n
if s>n//2: s=n-s   # low-S original
def be(x,l=None):
    b=x.to_bytes((x.bit_length()+7)//8 or 1,'big'); return b
def derint(v, pad=0, hi=False):
    b=be(v)
    if b[0]&0x80 or pad: b=b'\x00'*max(pad, 1 if (b[0]&0x80 and not hi) else 0)+b
    return b
def der(rb,sb,seqlen=None,rlenenc=None,slenenc=None,tag=b'\x30'):
    rl = rlenenc if rlenenc is not None else bytes([len(rb)])
    sl = slenenc if slenenc is not None else bytes([len(sb)])
    body=b'\x02'+rl+rb+b'\x02'+sl+sb
    return tag+(seqlen if seqlen is not None else bytes([len(body)]))+body
comp=(b'\x03' if Q[1]&1 else b'\x02')+Q[0].to_bytes(32,'big')
unc=b'\x04'+Q[0].to_bytes(32,'big')+Q[1].to_bytes(32,'big')
hyb_ok=(b'\x07' if Q[1]&1 else b'\x06')+unc[1:]
hyb_bad=(b'\x06' if Q[1]&1 else b'\x07')+unc[1:]
rb=derint(r); sb=derint(s)
sigs=[
 ("strict", der(rb,sb), True),
 ("high-S normalized", der(rb,derint(n-s)), True),
 ("overlong seq length 81", der(rb,sb,seqlen=b'\x81'+bytes([len(rb)+len(sb)+4])), True),
 ("seq length value ignored", der(rb,sb,seqlen=b'\x05'), True),
 ("overlong R length 82 00 xx", der(rb,sb,rlenenc=b'\x82\x00'+bytes([len(rb)])), True),
 ("R padded with three zero bytes", der(b'\x00\x00\x00'+rb.lstrip(b'\x00'),sb), True),
 ("R unpadded with high bit (negative in strict DER)", der(rb.lstrip(b'\x00'),sb), rb[0]==0),  # verifies iff original needed padding
 ("trailing garbage", der(rb,sb)+b'\xde\xad', True),
 ("wrong sequence tag", der(rb,sb,tag=b'\x31'), False),
 ("R too long: 33 significant bytes", der(b'\x01'+r.to_bytes(32,'big'),sb), False),
 ("R equals n (overflow)", der(derint(n),sb), False),
 ("S equals n (overflow)", der(rb,derint(n)), False),
 ("S zero", der(rb,b'\x00'), False),
 ("R zero", der(b'\x00',sb), False),
 ("truncated", der(rb,sb)[:-1], False),
 ("length byte 84 with three zero bytes stripped", der(rb,sb,rlenenc=b'\x84\x00\x00\x00'+bytes([len(rb)])), True),
 ("length byte 84 with four significant bytes", der(rb,sb,rlenenc=b'\x84\x01\x00\x00'+bytes([len(rb)])), False),
 ("length byte 85 with four zero bytes stripped", der(rb,sb,rlenenc=b'\x85\x00\x00\x00\x00'+bytes([len(rb)])), True),
 ("length byte 83 with zeros stripped", der(rb,sb,rlenenc=b'\x83\x00\x00'+bytes([len(rb)])), True),
 ("empty", b'', False),
 ("wrong message", None, False),
]
keys=[("compressed",comp,True),("uncompressed",unc,True),("hybrid matching parity",hyb_ok,True),("hybrid wrong parity",hyb_bad,False),
      ("x >= p", b'\x02'+(p+1).to_bytes(32,'big'), False),("not on curve", b'\x04'+Q[0].to_bytes(32,'big')+((Q[1]+1)%p).to_bytes(32,'big'), False),
      ("wrong length", comp+b'\x00', False),("tag 05", b'\x05'+comp[1:], False)]
lines=['import Definitions.Def_BitcoinSig','open BitcoinSig BitcoinSer',
'def hexDigit (c : Char) : Nat := if c.isDigit then c.toNat - 48 else if c.isLower then c.toNat - 87 else c.toNat - 55',
'def hx (s : String) : Bytes := let cs := s.toList; (List.range (cs.length / 2)).map fun i => BitVec.ofNat 8 (hexDigit (cs.getD (2*i) \'0\') * 16 + hexDigit (cs.getD (2*i+1) \'0\'))',
f'def z : Bytes := hx "{z.to_bytes(32,"big").hex()}"', f'def pk : Bytes := hx "{comp.hex()}"',
'/-! Spot 4 vectors (generator scratchpad/lax/gen.py): lax DER parsing, S normalization, key encodings. Every line prints `true`. -/']
for name,sig,exp in sigs:
    if sig is None:
        lines.append(f'#eval pubkeyVerify pk (0 :: z.drop 1) (hx "{der(rb,sb).hex()}") == {str(exp).lower()}   -- {name}')
    else:
        lines.append(f'#eval pubkeyVerify pk z (hx "{sig.hex()}") == {str(exp).lower()}   -- {name}')
for name,key,exp in keys:
    lines.append(f'#eval pubkeyVerify (hx "{key.hex()}") z (hx "{der(rb,sb).hex()}") == {str(exp).lower()}   -- key: {name}')
open('/home/user/prove2me/tests/LaxDerVectors.lean','w').write("\n".join(lines)+"\n")
print(len(sigs)+len(keys), "r pad needed:", rb[0]==0)
