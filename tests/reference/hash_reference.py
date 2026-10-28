"""Independent reference for spot 17 (REVIEW_SPOT17.md): SHA-256 (crypto/sha256.cpp), RIPEMD-160
(crypto/ripemd160.cpp), SHA-1 (crypto/sha1.cpp), Hash() = SHA-256d and Hash160() = RIPEMD-160 of SHA-256
(hash.h). The expected digests come from Python's hashlib (OpenSSL), checked here against the
published test vectors of each algorithm, so nothing comes from the Lean. Emits tests/HashVectors.lean.

Usage: python3 -I hash_reference.py OUT_LEAN [--million]
"""
import hashlib, sys

def sha256(b): return hashlib.sha256(b).digest()
def ripemd160(b): return hashlib.new("ripemd160", b).digest()
def sha1(b): return hashlib.sha1(b).digest()
def hash256(b): return sha256(sha256(b))
def hash160(b): return ripemd160(sha256(b))

# published vectors: FIPS 180-2 (SHA-256, SHA-1) and the RIPEMD-160 paper (Dobbertin, Bosselaers, Preneel)
PUB = {
    "sha256": {b"": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
               b"abc": "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad",
               b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq": "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1",
               b"a" * 1000000: "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0"},
    "ripemd160": {b"": "9c1185a5c5e9fc54612808977ee8f548b2258d31",
                  b"a": "0bdc9d2d256b3ee9daae347be6f4dc835a467ffe",
                  b"abc": "8eb208f7e05d987a9b044a8e98c6b087f15a0bfc",
                  b"message digest": "5d0689ef49d2fae572b881b123a85ffa21595f36",
                  b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq": "12a053384a9c0c88e405a06c27dcf49ada62eb2b",
                  b"a" * 1000000: "52783243c1697bdbe16d37f97f68f08325dc1528"},
    "sha1": {b"abc": "a9993e364706816aba3e25717850c26c9cd0d89d",
             b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq": "84983e441c3bd26ebaae4aa1f95129e5e54670f1"},
}
for name, f in (("sha256", sha256), ("ripemd160", ripemd160), ("sha1", sha1)):
    for m, d in PUB[name].items(): assert f(m).hex() == d, (name, m[:10])

def lean_msg(m):
    if all(32 <= c < 127 and c not in (34, 92) for c in m) and 0 < len(m) <= 64: return f'(ascii "{m.decode()}")'
    if len(m) == 0: return "[]"
    if len(set(m)) == 1: return f"(List.replicate {len(m)} {m[0]})"
    return "(ofHex \"" + m.hex() + "\")"

def main(out_path, million):
    msgs = [(b"", "empty"), (b"a", "1 byte"), (b"abc", "3 bytes"), (b"message digest", "14 bytes"),
            (b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq", "56 bytes: the length no longer fits the first block"),
            (b"a" * 55, "55 bytes: 0x80 and the length fill exactly one block"),
            (b"a" * 63, "63 bytes"), (b"a" * 64, "64 bytes: one full block, padding is a whole second block"),
            (b"a" * 65, "65 bytes"), (b"a" * 119, "119 bytes: two blocks exactly after padding"), (b"a" * 120, "120 bytes: three blocks"),
            (b"a" * 128, "128 bytes"), (bytes([0x80]), "the single byte 0x80 (must not be confused with padding)"),
            (bytes([0xff]) * 32, "32 bytes of 0xff"), (bytes(range(256)), "all 256 byte values"),
            (b"a" * 1000, "1000 bytes of 'a'")]
    if million: msgs.append((b"a" * 1000000, "1,000,000 bytes of 'a' (FIPS 180-2 / RIPEMD-160 paper vector)"))
    L = ["import Definitions.Def_BitcoinSer", "open BitcoinSer",
         "/-! Spot 17 vectors (`REVIEW_SPOT17.md`): SHA-256, RIPEMD-160, SHA-1, Hash (SHA-256d) and Hash160 on the",
         "standard test vectors and on messages around the padding boundaries (55/56/63/64/65/119/120 bytes).",
         "Expectations computed by `tests/reference/hash_reference.py` (hashlib, checked against the published",
         "vectors). Every line prints `true`. -/",
         "def hexVal (c : Char) : Nat := if c.isDigit then c.toNat - 48 else c.toLower.toNat - 87",
         "def ofHexL : List Char → Bytes", "  | a :: b :: r => BitVec.ofNat 8 (hexVal a * 16 + hexVal b) :: ofHexL r", "  | _ => []",
         "def ofHex (s : String) : Bytes := ofHexL s.toList",
         'def hex (b : Bytes) : String := String.join (b.map fun x => let s := (Nat.toDigits 16 x.toNat); String.ofList (if s.length = 1 then \'0\' :: s else s))',
         "def ascii (s : String) : Bytes := s.toUTF8.toList.map fun c => BitVec.ofNat 8 c.toNat"]
    for m, note in msgs:
        lm = lean_msg(m)
        L.append(f"-- {note}")
        L.append(f'#eval hex (sha256 {lm}) == "{sha256(m).hex()}"')
        L.append(f'#eval hex (ripemd160 {lm}) == "{ripemd160(m).hex()}"')
        if len(m) <= 1000:
            L.append(f'#eval hex (sha1 {lm}) == "{sha1(m).hex()}"')
            L.append(f'#eval hex (hash256 {lm}) == "{hash256(m).hex()}"')
            L.append(f'#eval hex (hash160 {lm}) == "{hash160(m).hex()}"')
    L.append("-- Hash160 of the genesis output public key (65 bytes), the P2PKH hash of 1A1zP1eP5QGefi2DMPTfTL5SLmv7DivfNa")
    pk = bytes.fromhex("04678afdb0fe5548271967f1a67130b7105cd6a828e03909a67962e0ea1f61deb649f6bc3f4cef38c4f35504e51ec112de5c384df7ba0b8d578a4c702b6bf11d5f")
    assert hash160(pk).hex() == "62e907b15cbf27d5425399ebf6f0fb50ebb88f18"
    L.append(f'#eval hex (hash160 (genesisOutputScript.drop 1 |>.take 65)) == "{hash160(pk).hex()}"')
    L.append("-- output length and the hash of a hash")
    L.append("#eval (sha256 (ascii \"abc\")).length == 32")
    L.append("#eval (ripemd160 (ascii \"abc\")).length == 20")
    L.append(f'#eval hex (sha256 (sha256 (ascii "abc"))) == "{hash256(b"abc").hex()}"')
    open(out_path, "w").write("\n".join(L) + "\n")
    print("wrote", out_path, "evals", sum(1 for l in L if l.startswith("#eval")))

if __name__ == "__main__":
    main(sys.argv[1], "--million" in sys.argv[2:])
