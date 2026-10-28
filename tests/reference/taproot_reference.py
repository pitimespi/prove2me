import hashlib, struct, json
p=0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
n=0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
G=(0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798,0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8)
def inv(a,m): return pow(a,m-2,m)
def padd(P,Q):
    if P is None: return Q
    if Q is None: return P
    if P[0]==Q[0] and (P[1]+Q[1])%p==0: return None
    l = 3*P[0]*P[0]*inv(2*P[1],p)%p if P==Q else (Q[1]-P[1])*inv(Q[0]-P[0],p)%p
    x=(l*l-P[0]-Q[0])%p; return (x,(l*(P[0]-x)-P[1])%p)
def pmul(k,P):
    R=None
    while k:
        if k&1: R=padd(R,P)
        P=padd(P,P); k>>=1
    return R
def sha(b): return hashlib.sha256(b).digest()
def tagged(tag,m): t=sha(tag.encode()); return sha(t+t+m)
def cs(k): return bytes([k]) if k<253 else b'\xfd'+struct.pack('<H',k)
def ser_bytes(b): return cs(len(b))+b
def xb(P): return P[0].to_bytes(32,'big')
def even(d,P): return (n-d, (P[0],(p-P[1])%p)) if P[1]&1 else (d,P)
def schnorr_sign(d, msg, k):
    d,P=even(d,pmul(d,G)); k,R=even(k,pmul(k,G))
    e=int.from_bytes(tagged("BIP0340/challenge", xb(R)+xb(P)+msg),'big')%n
    return xb(R)+((k+e*d)%n).to_bytes(32,'big')
def tapleaf(ver,script): return tagged("TapLeaf", bytes([ver])+ser_bytes(script))
def tweak(P, root):   # P even-y internal point; returns (Q, parity)
    t=int.from_bytes(tagged("TapTweak", xb(P)+root),'big'); Q=padd(P,pmul(t,G)); return Q, Q[1]&1, t
# transaction
prev=bytes(range(32)); seq=0xffffffff
def ser_outpoint(): return prev+struct.pack('<I',0)
def ser_txout(v,spk): return struct.pack('<q',v)+ser_bytes(spk)
def sighash(spk_spent, amount_spent, vout, hash_type, ext_flag, annex, tapleaf_hash=None, codesep=0xffffffff):
    out_type = 1 if hash_type==0 else hash_type&3
    in_type = hash_type&0x80
    m=b'\x00'+bytes([hash_type])+struct.pack('<I',2)+struct.pack('<I',0)
    if in_type!=0x80:
        m+=sha(ser_outpoint())+sha(struct.pack('<q',amount_spent))+sha(ser_bytes(spk_spent))+sha(struct.pack('<I',seq))
    if out_type==1: m+=sha(b''.join(ser_txout(*o) for o in vout))
    m+=bytes([(ext_flag<<1)+(1 if annex is not None else 0)])
    if in_type==0x80: m+=ser_outpoint()+ser_txout(amount_spent,spk_spent)+struct.pack('<I',seq)
    else: m+=struct.pack('<I',0)
    if annex is not None: m+=sha(ser_bytes(annex))
    if out_type==3:
        if len(vout)<1: return None
        m+=sha(ser_txout(*vout[0]))
    if ext_flag==1: m+=tapleaf_hash+b'\x00'+struct.pack('<I',codesep)
    return tagged("TapSighash", m)
d1=0x1E99423A4ED27608A15A2616A2B0E9E52CED330AC530EDCC32C8FFC6A526AEDD; d2=0x2B7E151628AED2A6ABF7158809CF4F3C762E7160F38B4DA56A784D9045190CFE
dint=0x3C6EF372FE94F82BE73EFB2F8A0F2BD4BBE2C3A3C42F2D1A1B2C3D4E5F607182
k1=0x5F3B1C2D4E6F708192A3B4C5D6E7F8091A2B3C4D5E6F708192A3B4C5D6E7F809
_,P1=even(d1,pmul(d1,G)); _,P2=even(d2,pmul(d2,G)); _,Pint=even(dint,pmul(dint,G))
vout=[(90000, b'\x51\x20'+bytes(32))]
L=['import Definitions.Def_BitcoinTaproot','open BitcoinSer BitcoinSig BitcoinVerify BitcoinTaproot',
'def hexDigit (c : Char) : Nat := if c.isDigit then c.toNat - 48 else if c.isLower then c.toNat - 87 else c.toNat - 55',
'def hx (s : String) : Bytes := let cs := s.toList; (List.range (cs.length / 2)).map fun i => BitVec.ofNat 8 (hexDigit (cs.getD (2*i) \'0\') * 16 + hexDigit (cs.getD (2*i+1) \'0\'))',
'def rng (a b : Nat) : Bytes := (List.range (b - a)).map fun i => BitVec.ofNat 8 (a + i)',
'def allF : BitcoinActivation.ScriptFlags := ⟨true, true, true, true, true, true, true⟩',
'def tx : Tx := ⟨2, [⟨⟨rng 0 32, 0⟩, [], 0xffffffff, []⟩], [⟨90000, hx "5120" ++ List.replicate 32 0⟩], 0⟩',
'/-! Spot 8/9 vectors (generator tests/reference/taproot_reference.py): BIP341 sighash, key path, script path, Tapscript. Every line prints `true`. -/']
def ctx(spk): return f'(⟨allF, tx, 0, 100000⟩ : Ctx)'
def spent(spk): return f'[⟨100000, hx "{spk.hex()}"⟩]'
# ---- (A) sighash vectors against sigHashSchnorr: key-path context
Q1,par1,_=tweak(Pint, b'')   # unused root form: BIP341 key-path with no script uses tagged(P) only; we use a leaf root below
# use a real script tree for the output: single leaf
script_a=b'\x20'+xb(P1)+b'\xac'
leaf_a=tapleaf(0xc0,script_a)
Q,par,t=tweak(Pint, leaf_a)
spk=b'\x51\x20'+xb(Q)
control=bytes([0xc0|par])+xb(Pint)
annex=b'\x50\x01\x02'
for ht in [0,1,2,3,0x81,0x82,0x83]:
    for tap in [False,True]:
        for an in [None,annex]:
            h=sighash(spk,100000,vout,ht,1 if tap else 0,an,leaf_a,0xffffffff)
            edann = 'true' if an is not None else 'false'
            annh = f'sha256 (serBytes (hx "{an.hex()}"))' if an is not None else '[]'
            L.append(f'#eval sigHashSchnorr tx {spent(spk)} 0 {ht} {str(tap).lower()} ⟨{edann}, {annh}, hx "{leaf_a.hex()}", 0xFFFFFFFF⟩ == some (hx "{h.hex()}")')
L.append('#eval sigHashSchnorr tx '+spent(spk)+' 0 4 false ⟨false, [], [], 0xFFFFFFFF⟩ == none   -- undefined hash type')
L.append('#eval sigHashSchnorr tx '+spent(spk)+' 0 0x80 false ⟨false, [], [], 0xFFFFFFFF⟩ == none')
# ---- (B) key path through the handler (tweaked private key)
dQ = (dint + t) % n   # Pint has even y by construction
if Q[1]&1: dQ = n - dQ
def keysig(ht, an):
    h=sighash(spk,100000,vout,ht,0,an)
    s=schnorr_sign(dQ,h,k1)
    return s if ht==0 else s+bytes([ht])
H=f'taprootHandler {spent(spk)} {ctx(spk)}'
L.append(f'#eval {H} [hx "{keysig(0,None).hex()}"] (hx "{xb(Q).hex()}") == true   -- key path, SIGHASH_DEFAULT')
L.append(f'#eval {H} [hx "{keysig(1,None).hex()}"] (hx "{xb(Q).hex()}") == true   -- key path, SIGHASH_ALL')
L.append(f'#eval {H} [hx "{keysig(0x83,None).hex()}"] (hx "{xb(Q).hex()}") == true   -- SINGLE|ANYONECANPAY')
L.append(f'#eval {H} [hx "{keysig(0,annex).hex()}", hx "{annex.hex()}"] (hx "{xb(Q).hex()}") == true   -- with annex')
L.append(f'#eval {H} [hx "{keysig(0,None).hex()}", hx "{annex.hex()}"] (hx "{xb(Q).hex()}") == false   -- annex not committed')
L.append(f'#eval {H} [hx "{(schnorr_sign(dQ,sighash(spk,100000,vout,0,0,None),k1)+bytes([0])).hex()}"] (hx "{xb(Q).hex()}") == false   -- 65 bytes with hash type 0')
L.append(f'#eval {H} [hx "{keysig(1,None).hex()}"] (hx "{xb(Pint).hex()}") == false   -- internal key is not the output key')
L.append(f'#eval {H} [] (hx "{xb(Q).hex()}") == false   -- empty witness')
# ---- (C) script path: <P1> CHECKSIG
def leafsig(d, script, ht, codesep=0xffffffff, an=None, k=k1):
    h=sighash(spk,100000,vout,ht,1,an,tapleaf(0xc0,script),codesep); s=schnorr_sign(d,h,k); return s if ht==0 else s+bytes([ht])
sig1=leafsig(d1,script_a,0)
L.append(f'#eval {H} [hx "{sig1.hex()}", hx "{script_a.hex()}", hx "{control.hex()}"] (hx "{xb(Q).hex()}") == true   -- script path CHECKSIG')
L.append(f'#eval {H} [hx "{leafsig(d2,script_a,0).hex()}", hx "{script_a.hex()}", hx "{control.hex()}"] (hx "{xb(Q).hex()}") == false   -- wrong key')
L.append(f'#eval {H} [[], hx "{script_a.hex()}", hx "{control.hex()}"] (hx "{xb(Q).hex()}") == false   -- empty sig leaves false')
L.append(f'#eval {H} [hx "{sig1.hex()}", hx "{script_a.hex()}", hx "{(bytes([0xc0|(1-par)])+xb(Pint)).hex()}"] (hx "{xb(Q).hex()}") == false   -- wrong parity bit')
L.append(f'#eval {H} [hx "{sig1.hex()}", hx "{script_a.hex()}", hx "{(control+bytes(32)).hex()}"] (hx "{xb(Q).hex()}") == false   -- extra path node breaks the commitment')
L.append(f'#eval {H} [hx "{sig1.hex()}", hx "{script_a.hex()}", hx "{(control+bytes(31)).hex()}"] (hx "{xb(Q).hex()}") == false   -- control size not 33+32k')
# a two-leaf tree so a path node is exercised: leaves a and b, b = <P2> CHECKSIG
script_b=b'\x20'+xb(P2)+b'\xac'; leaf_b=tapleaf(0xc0,script_b)
def branch(a,b): return tagged("TapBranch", a+b if a<b else b+a)
root2=branch(leaf_a,leaf_b); Q2,par2,t2=tweak(Pint,root2); spk2=b'\x51\x20'+xb(Q2)
ctrl_a=bytes([0xc0|par2])+xb(Pint)+leaf_b; ctrl_b=bytes([0xc0|par2])+xb(Pint)+leaf_a
def sighash2(script, ht=0, codesep=0xffffffff): return sighash(spk2,100000,vout,ht,1,None,tapleaf(0xc0,script),codesep)
H2=f'taprootHandler {spent(spk2)} {ctx(spk2)}'
sa=schnorr_sign(d1,sighash2(script_a),k1); sb=schnorr_sign(d2,sighash2(script_b),k1)
L.append(f'#eval {H2} [hx "{sa.hex()}", hx "{script_a.hex()}", hx "{ctrl_a.hex()}"] (hx "{xb(Q2).hex()}") == true   -- two-leaf tree, leaf a')
L.append(f'#eval {H2} [hx "{sb.hex()}", hx "{script_b.hex()}", hx "{ctrl_b.hex()}"] (hx "{xb(Q2).hex()}") == true   -- leaf b')
L.append(f'#eval {H2} [hx "{sb.hex()}", hx "{script_b.hex()}", hx "{ctrl_a.hex()}"] (hx "{xb(Q2).hex()}") == false  -- leaf b with a\'s path')
# ---- (D) CHECKSIGADD 2-of-2 and 1-of-2 under spk2's tree? need the script in the tree: build a third tree with leaf c
script_c=b'\x20'+xb(P1)+b'\xac'+b'\x20'+xb(P2)+b'\xba'+b'\x52\x9c'   # <P1> CHECKSIG <P2> CHECKSIGADD OP_2 NUMEQUAL
script_d=b'\x20'+xb(P1)+b'\xac'+b'\x20'+xb(P2)+b'\xba'+b'\x51\x9c'   # ... OP_1 NUMEQUAL
script_e=b'\x63'+b'\x20'+xb(P1)+b'\xac'+b'\x67\x51\x68'                 # IF <P1> CHECKSIG ELSE OP_1 ENDIF
script_f=b'\xab'+b'\x20'+xb(P1)+b'\xac'                                   # CODESEPARATOR <P1> CHECKSIG
script_g=b'\x50'                                                           # OP_SUCCESS80
script_h=b'\x20'+xb(P1)+b'\xac'                                            # same as a but leaf version 0xc2
leaves={'c':script_c,'d':script_d,'e':script_e,'f':script_f,'g':script_g}
# build a 5-leaf tree: ((c,d),(e,f)), g
def mk():
    lh={k:tapleaf(0xc0,v) for k,v in leaves.items()}; lh['h']=tapleaf(0xc2,script_h)
    n1=branch(lh['c'],lh['d']); n2=branch(lh['e'],lh['f']); n3=branch(n1,n2); n4=branch(lh['g'],lh['h']); root=branch(n3,n4)
    paths={'c':[lh['d'],n2,n4],'d':[lh['c'],n2,n4],'e':[lh['f'],n1,n4],'f':[lh['e'],n1,n4],'g':[lh['h'],n3],'h':[lh['g'],n3]}
    return root,paths,lh
root3,paths,lh=mk(); Q3,par3,t3=tweak(Pint,root3); spk3=b'\x51\x20'+xb(Q3)
def ctrl(k, ver=0xc0): return bytes([ver|par3])+xb(Pint)+b''.join(paths[k])
H3=f'taprootHandler {spent(spk3)} {ctx(spk3)}'
def sh3(script, ver=0xc0, codesep=0xffffffff): return sighash(spk3,100000,vout,0,1,None,tapleaf(ver,script),codesep)
s1c=schnorr_sign(d1,sh3(script_c),k1); s2c=schnorr_sign(d2,sh3(script_c),k1)
# stack order: CHECKSIGADD pops pubkey, num, sig; CHECKSIG pops pubkey, sig. witness (bottom..top): sig2, sig1
W=lambda items,k: '[' + ', '.join(f'hx "{i.hex()}"' if i else '[]' for i in items) + f', hx "{leaves[k].hex()}", hx "{ctrl(k).hex()}"]'
L.append(f'#eval {H3} {W([s2c,s1c],"c")} (hx "{xb(Q3).hex()}") == true    -- CHECKSIGADD 2-of-2')
L.append(f'#eval {H3} {W([b"",s1c],"c")} (hx "{xb(Q3).hex()}") == false   -- 2-of-2 with one empty signature: 1 ≠ 2')
s1d=schnorr_sign(d1,sh3(script_d),k1); s2d=schnorr_sign(d2,sh3(script_d),k1)
L.append(f'#eval {H3} {W([b"",s1d],"d")} (hx "{xb(Q3).hex()}") == true    -- 1-of-2 with the second signature empty')
L.append(f'#eval {H3} {W([s2d,b""],"d")} (hx "{xb(Q3).hex()}") == true    -- 1-of-2 with the first empty')
L.append(f'#eval {H3} {W([s2d,s1d],"d")} (hx "{xb(Q3).hex()}") == false   -- both valid: 2 ≠ 1')
L.append(f'#eval {H3} {W([s2c,s1d],"d")} (hx "{xb(Q3).hex()}") == false   -- non-empty invalid signature fails the script')
s1e=schnorr_sign(d1,sh3(script_e),k1)
L.append(f'#eval {H3} {W([s1e,bytes([1])],"e")} (hx "{xb(Q3).hex()}") == true    -- MINIMALIF: [01] takes the branch')
L.append(f'#eval {H3} {W([s1e,bytes([2])],"e")} (hx "{xb(Q3).hex()}") == false   -- [02] is not minimal')
L.append(f'#eval {H3} {W([s1e,bytes([1,0])],"e")} (hx "{xb(Q3).hex()}") == false   -- two bytes')
L.append(f'#eval {H3} {W([b""],"e")} (hx "{xb(Q3).hex()}") == true    -- [] takes the ELSE branch')
s1f=schnorr_sign(d1,sh3(script_f,codesep=0),k1); s1f_bad=schnorr_sign(d1,sh3(script_f),k1)
L.append(f'#eval {H3} {W([s1f],"f")} (hx "{xb(Q3).hex()}") == true    -- OP_CODESEPARATOR at position 0 is committed')
L.append(f'#eval {H3} {W([s1f_bad],"f")} (hx "{xb(Q3).hex()}") == false   -- signature over position 0xFFFFFFFF')
L.append(f'#eval {H3} [hx "{(bytes(600)).hex()}", hx "{script_g.hex()}", hx "{ctrl("g").hex()}"] (hx "{xb(Q3).hex()}") == true   -- OP_SUCCESS80: even a 600-byte element passes')
L.append(f'#eval {H3} [hx "{script_h.hex()}", hx "{ctrl("h",0xc2).hex()}"] (hx "{xb(Q3).hex()}") == true   -- unknown leaf version 0xc2 succeeds')
L.append(f'#eval {H3} [hx "{script_h.hex()}", hx "{ctrl("h",0xc0).hex()}"] (hx "{xb(Q3).hex()}") == false  -- same leaf under 0xc0: commitment fails')
# ---- (E) weight budget: k copies of OP_DUP <P1> CHECKSIGVERIFY then <P1> CHECKSIG, one signature duplicated
def budget_script(k): return b'\x76'*k + (b'\x20'+xb(P1)+b'\xad')*k + b'\x20'+xb(P1)+b'\xac'
for k in [9,10,11]:
    sc=budget_script(k); lhk=tapleaf(0xc0,sc); Qk,park,_=tweak(Pint,lhk); spkk=b'\x51\x20'+xb(Qk); ck=bytes([0xc0|park])+xb(Pint)
    sk=schnorr_sign(d1,sighash(spkk,100000,vout,0,1,None,lhk),k1)
    wit=[sk,sc,ck]; size=len(cs(3))+sum(len(ser_bytes(w)) for w in wit); budget=size+50; cost=50*(k+1)
    L.append(f'#eval taprootHandler {spent(spkk)} {ctx(spkk)} [hx "{sk.hex()}", hx "{sc.hex()}", hx "{ck.hex()}"] (hx "{xb(Qk).hex()}") == {str(cost<=budget).lower()}   -- {k+1} checks cost {cost}, budget {budget}')
open('/home/user/prove2me/tests/TapscriptVectors.lean','w').write("\n".join(L)+"\n")
print(len(L)-8)
