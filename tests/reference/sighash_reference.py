import hashlib, struct, json
def sha256d(b): return hashlib.sha256(hashlib.sha256(b).digest()).digest()
def cs(n):
    if n < 253: return bytes([n])
    if n <= 0xffff: return b'\xfd'+struct.pack('<H',n)
    return b'\xfe'+struct.pack('<I',n)
def ser_bytes(b): return cs(len(b))+b
def ser_outpoint(h,n): return h+struct.pack('<I',n)
def ser_txout(v,spk): return struct.pack('<q',v)+ser_bytes(spk)
# Core-faithful legacy SignatureHash (SerializeScriptCode without codeseparators)
def strip_codesep(sc):
    out=b''; i=0
    while i < len(sc):
        op=sc[i]; j=i+1
        if op<=0x4e:
            if op<0x4c: n=op
            elif op==0x4c: n=sc[j]; j+=1
            elif op==0x4d: n=struct.unpack('<H',sc[j:j+2])[0]; j+=2
            else: n=struct.unpack('<I',sc[j:j+4])[0]; j+=4
            j+=n
        if op!=0xab: out+=sc[i:j]
        i=j
    return out
def sighash_legacy(tx, sc, nIn, ht):
    if (ht & 0x1f)==3 and nIn >= len(tx['vout']): return (b'\x01'+b'\x00'*31)
    acp = ht & 0x80; single=(ht&0x1f)==3; none=(ht&0x1f)==2
    s=struct.pack('<I',tx['version'])
    nInputs = 1 if acp else len(tx['vin'])
    s+=cs(nInputs)
    for k in range(nInputs):
        i = nIn if acp else k
        vin=tx['vin'][i]
        s+=ser_outpoint(vin['hash'],vin['n'])
        s+= (ser_bytes(strip_codesep(sc)) if i==nIn else ser_bytes(b''))
        s+= struct.pack('<I',0) if (i!=nIn and (single or none)) else struct.pack('<I',vin['seq'])
    nOutputs = 0 if none else (nIn+1 if single else len(tx['vout']))
    s+=cs(nOutputs)
    for k in range(nOutputs):
        if single and k!=nIn: s+=ser_txout(-1,b'')
        else: s+=ser_txout(*tx['vout'][k])
    s+=struct.pack('<I',tx['locktime'])
    return sha256d(s+struct.pack('<i',ht))
def sighash_v0(tx, sc, nIn, ht, amount):
    acp = ht & 0x80; single=(ht&0x1f)==3; none=(ht&0x1f)==2
    zero=b'\x00'*32
    hp = sha256d(b''.join(ser_outpoint(v['hash'],v['n']) for v in tx['vin'])) if not acp else zero
    hs = sha256d(b''.join(struct.pack('<I',v['seq']) for v in tx['vin'])) if (not acp and not single and not none) else zero
    if not single and not none: ho=sha256d(b''.join(ser_txout(*o) for o in tx['vout']))
    elif single and nIn < len(tx['vout']): ho=sha256d(ser_txout(*tx['vout'][nIn]))
    else: ho=zero
    vin=tx['vin'][nIn]
    s=struct.pack('<I',tx['version'])+hp+hs+ser_outpoint(vin['hash'],vin['n'])+ser_bytes(sc)+struct.pack('<q',amount)+struct.pack('<I',vin['seq'])+ho+struct.pack('<I',tx['locktime'])+struct.pack('<i',ht)
    return sha256d(s)
tx={'version':2,'locktime':500123,
    'vin':[{'hash':bytes(range(32)),'n':1,'seq':0xfffffffe},{'hash':bytes(range(32,64)),'n':0,'seq':0xffffffff},{'hash':bytes(range(64,96)),'n':7,'seq':12345}],
    'vout':[(100000,bytes.fromhex('76a914')+bytes(20)+bytes.fromhex('88ac')),(0,bytes.fromhex('6a04deadbeef'))]}
# script code with a codeseparator and a push: OP_DUP OP_HASH160 <20> OP_EQUALVERIFY OP_CODESEPARATOR OP_CHECKSIG
sc=bytes.fromhex('76a914')+bytes(range(1,21))+bytes.fromhex('88abac')
vec=[]
for ht in [1,2,3,0x81,0x82,0x83]:
    for nIn in [0,2]:
        vec.append(('legacy',nIn,ht,sighash_legacy(tx,sc,nIn,ht).hex()))
        vec.append(('v0',nIn,ht,sighash_v0(tx,sc,nIn,ht,5000).hex()))
print(json.dumps({'sc':sc.hex(),'vec':vec}))
