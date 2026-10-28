import Definitions.Def_BitcoinSer
open BitcoinSer
/-! Spot 17 vectors (`REVIEW_SPOT17.md`): SHA-256, RIPEMD-160, SHA-1, Hash (SHA-256d) and Hash160 on the
standard test vectors and on messages around the padding boundaries (55/56/63/64/65/119/120 bytes).
Expectations computed by `tests/reference/hash_reference.py` (hashlib, checked against the published
vectors). Every line prints `true`. -/
def hexVal (c : Char) : Nat := if c.isDigit then c.toNat - 48 else c.toLower.toNat - 87
def ofHexL : List Char → Bytes
  | a :: b :: r => BitVec.ofNat 8 (hexVal a * 16 + hexVal b) :: ofHexL r
  | _ => []
def ofHex (s : String) : Bytes := ofHexL s.toList
def hex (b : Bytes) : String := String.join (b.map fun x => let s := (Nat.toDigits 16 x.toNat); String.ofList (if s.length = 1 then '0' :: s else s))
def ascii (s : String) : Bytes := s.toUTF8.toList.map fun c => BitVec.ofNat 8 c.toNat
-- empty
#eval hex (sha256 []) == "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
#eval hex (ripemd160 []) == "9c1185a5c5e9fc54612808977ee8f548b2258d31"
#eval hex (sha1 []) == "da39a3ee5e6b4b0d3255bfef95601890afd80709"
#eval hex (hash256 []) == "5df6e0e2761359d30a8275058e299fcc0381534545f55cf43e41983f5d4c9456"
#eval hex (hash160 []) == "b472a266d0bd89c13706a4132ccfb16f7c3b9fcb"
-- 1 byte
#eval hex (sha256 (ascii "a")) == "ca978112ca1bbdcafac231b39a23dc4da786eff8147c4e72b9807785afee48bb"
#eval hex (ripemd160 (ascii "a")) == "0bdc9d2d256b3ee9daae347be6f4dc835a467ffe"
#eval hex (sha1 (ascii "a")) == "86f7e437faa5a7fce15d1ddcb9eaeaea377667b8"
#eval hex (hash256 (ascii "a")) == "bf5d3affb73efd2ec6c36ad3112dd933efed63c4e1cbffcfa88e2759c144f2d8"
#eval hex (hash160 (ascii "a")) == "994355199e516ff76c4fa4aab39337b9d84cf12b"
-- 3 bytes
#eval hex (sha256 (ascii "abc")) == "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
#eval hex (ripemd160 (ascii "abc")) == "8eb208f7e05d987a9b044a8e98c6b087f15a0bfc"
#eval hex (sha1 (ascii "abc")) == "a9993e364706816aba3e25717850c26c9cd0d89d"
#eval hex (hash256 (ascii "abc")) == "4f8b42c22dd3729b519ba6f68d2da7cc5b2d606d05daed5ad5128cc03e6c6358"
#eval hex (hash160 (ascii "abc")) == "bb1be98c142444d7a56aa3981c3942a978e4dc33"
-- 14 bytes
#eval hex (sha256 (ascii "message digest")) == "f7846f55cf23e14eebeab5b4e1550cad5b509e3348fbc4efa3a1413d393cb650"
#eval hex (ripemd160 (ascii "message digest")) == "5d0689ef49d2fae572b881b123a85ffa21595f36"
#eval hex (sha1 (ascii "message digest")) == "c12252ceda8be8994d5fa0290a47231c1d16aae3"
#eval hex (hash256 (ascii "message digest")) == "0b9731e12cfdc96ebb07e4a96d6dff767c20682c120743c177715033ce747c12"
#eval hex (hash160 (ascii "message digest")) == "c0f5356420849b03a32ddfa5f9204f41392bad94"
-- 56 bytes: the length no longer fits the first block
#eval hex (sha256 (ascii "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq")) == "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
#eval hex (ripemd160 (ascii "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq")) == "12a053384a9c0c88e405a06c27dcf49ada62eb2b"
#eval hex (sha1 (ascii "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq")) == "84983e441c3bd26ebaae4aa1f95129e5e54670f1"
#eval hex (hash256 (ascii "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq")) == "0cffe17f68954dac3a84fb1458bd5ec99209449749b2b308b7cb55812f9563af"
#eval hex (hash160 (ascii "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq")) == "69dda8a60e0cfc2353aa776864092c0e5ccb4834"
-- 55 bytes: 0x80 and the length fill exactly one block
#eval hex (sha256 (ascii "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")) == "9f4390f8d30c2dd92ec9f095b65e2b9ae9b0a925a5258e241c9f1e910f734318"
#eval hex (ripemd160 (ascii "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")) == "0d8a8c9063a48576a7c97e9f95253a6e53ff6765"
#eval hex (sha1 (ascii "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")) == "c1c8bbdc22796e28c0e15163d20899b65621d65a"
#eval hex (hash256 (ascii "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")) == "566dbb7f0f129482d449b7a4b971b1302f13a1a5e1faee904a0a270b2b6f5a7d"
#eval hex (hash160 (ascii "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")) == "e23716d6140e7f616ed0784636820792fc66e0ba"
-- 63 bytes
#eval hex (sha256 (ascii "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")) == "7d3e74a05d7db15bce4ad9ec0658ea98e3f06eeecf16b4c6fff2da457ddc2f34"
#eval hex (ripemd160 (ascii "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")) == "e640041293fe663b9bf3f8c21ffecac03819e6b2"
#eval hex (sha1 (ascii "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")) == "03f09f5b158a7a8cdad920bddc29b81c18a551f5"
#eval hex (hash256 (ascii "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")) == "54f57e8b7d0ed00e442facf36dfa95ce6eb5df391bb7b198a4a3c728b8ba6e76"
#eval hex (hash160 (ascii "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")) == "ef2fc29f583db8d0cdb43916d0c6f46a3ae0b9bb"
-- 64 bytes: one full block, padding is a whole second block
#eval hex (sha256 (ascii "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")) == "ffe054fe7ae0cb6dc65c3af9b61d5209f439851db43d0ba5997337df154668eb"
#eval hex (ripemd160 (ascii "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")) == "9dfb7d374ad924f3f88de96291c33e9abed53e32"
#eval hex (sha1 (ascii "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")) == "0098ba824b5c16427bd7a1122a5a442a25ec644d"
#eval hex (hash256 (ascii "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")) == "64d28424725a6f219efb17d6f8e4036719bf9e1a8ec2388c22cfb5fc412d46bc"
#eval hex (hash160 (ascii "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")) == "57591c6b8f00df7d36a642cc94021dda9ccd43fc"
-- 65 bytes
#eval hex (sha256 (List.replicate 65 97)) == "635361c48bb9eab14198e76ea8ab7f1a41685d6ad62aa9146d301d4f17eb0ae0"
#eval hex (ripemd160 (List.replicate 65 97)) == "99724bb11811e7166af38f671b6a082d8ab4960b"
#eval hex (sha1 (List.replicate 65 97)) == "11655326c708d70319be2610e8a57d9a5b959d3b"
#eval hex (hash256 (List.replicate 65 97)) == "fb183eb69ec26b94dbc6ae9ee468e26237cf006ab23823e9d58b818397ec7193"
#eval hex (hash160 (List.replicate 65 97)) == "5afdde537970926b24accdf2895d8be96545f6d7"
-- 119 bytes: two blocks exactly after padding
#eval hex (sha256 (List.replicate 119 97)) == "31eba51c313a5c08226adf18d4a359cfdfd8d2e816b13f4af952f7ea6584dcfb"
#eval hex (ripemd160 (List.replicate 119 97)) == "23e398ff2bac815aa1bbb57ca2a669c841872919"
#eval hex (sha1 (List.replicate 119 97)) == "ee971065aaa017e0632a8ca6c77bb3bf8b1dfc56"
#eval hex (hash256 (List.replicate 119 97)) == "3ae6a2ecf88f87d2ba38220c7208d58559daf7aaef7aa800ec118eac805567c6"
#eval hex (hash160 (List.replicate 119 97)) == "6c34b9e5f634dcdf42c6841102f786169b088b06"
-- 120 bytes: three blocks
#eval hex (sha256 (List.replicate 120 97)) == "2f3d335432c70b580af0e8e1b3674a7c020d683aa5f73aaaedfdc55af904c21c"
#eval hex (ripemd160 (List.replicate 120 97)) == "c476770a6dae31fcee8d25efe6559a05c8024595"
#eval hex (sha1 (List.replicate 120 97)) == "f34c1488385346a55709ba056ddd08280dd4c6d6"
#eval hex (hash256 (List.replicate 120 97)) == "09a712ac2347b5d613f9f3ad81a4659795a8c33070346be6891417a0932092e4"
#eval hex (hash160 (List.replicate 120 97)) == "656f97843ef5f33015d24e84156a1203ca716b03"
-- 128 bytes
#eval hex (sha256 (List.replicate 128 97)) == "6836cf13bac400e9105071cd6af47084dfacad4e5e302c94bfed24e013afb73e"
#eval hex (ripemd160 (List.replicate 128 97)) == "8dfdfb32b2ed5cb41a73478b4fd60cc5b4648b15"
#eval hex (sha1 (List.replicate 128 97)) == "ad5b3fdbcb526778c2839d2f151ea753995e26a0"
#eval hex (hash256 (List.replicate 128 97)) == "0fb4ba94ecf6f40f31757fab9f796e26595d45f0e143b7e97e376763031da930"
#eval hex (hash160 (List.replicate 128 97)) == "73641306aa8ea957e0a59897595aceecf405546b"
-- the single byte 0x80 (must not be confused with padding)
#eval hex (sha256 (List.replicate 1 128)) == "76be8b528d0075f7aae98d6fa57a6d3c83ae480a8469e668d7b0af968995ac71"
#eval hex (ripemd160 (List.replicate 1 128)) == "b436441e6bb882fe0a0fa0320cb2d97d96b4d1bc"
#eval hex (sha1 (List.replicate 1 128)) == "c78ebd3c85a39a596d9f5cfd2b8d240bc1b9c125"
#eval hex (hash256 (List.replicate 1 128)) == "c9403978dea583c63181682f425701778ada1310ae83140fec08e95efbf9f523"
#eval hex (hash160 (List.replicate 1 128)) == "78362be37dac06833d2d01c4d20dcd394494148f"
-- 32 bytes of 0xff
#eval hex (sha256 (List.replicate 32 255)) == "af9613760f72635fbdb44a5a0a63c39f12af30f950a6ee5c971be188e89c4051"
#eval hex (ripemd160 (List.replicate 32 255)) == "1cf4e77f5966e13e109703cd8a0df7ceda7f3dc3"
#eval hex (sha1 (List.replicate 32 255)) == "9e5175008751d08f361488c9927086b276b965fa"
#eval hex (hash256 (List.replicate 32 255)) == "71ca5049661b67d2babaf306cd9bc8090a93324c2d4ff1bb12a371a02cc23eb8"
#eval hex (hash160 (List.replicate 32 255)) == "54c4e063db298729e792f272db89297593e27115"
-- all 256 byte values
#eval hex (sha256 (ofHex "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f404142434445464748494a4b4c4d4e4f505152535455565758595a5b5c5d5e5f606162636465666768696a6b6c6d6e6f707172737475767778797a7b7c7d7e7f808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9fa0a1a2a3a4a5a6a7a8a9aaabacadaeafb0b1b2b3b4b5b6b7b8b9babbbcbdbebfc0c1c2c3c4c5c6c7c8c9cacbcccdcecfd0d1d2d3d4d5d6d7d8d9dadbdcdddedfe0e1e2e3e4e5e6e7e8e9eaebecedeeeff0f1f2f3f4f5f6f7f8f9fafbfcfdfeff")) == "40aff2e9d2d8922e47afd4648e6967497158785fbd1da870e7110266bf944880"
#eval hex (ripemd160 (ofHex "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f404142434445464748494a4b4c4d4e4f505152535455565758595a5b5c5d5e5f606162636465666768696a6b6c6d6e6f707172737475767778797a7b7c7d7e7f808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9fa0a1a2a3a4a5a6a7a8a9aaabacadaeafb0b1b2b3b4b5b6b7b8b9babbbcbdbebfc0c1c2c3c4c5c6c7c8c9cacbcccdcecfd0d1d2d3d4d5d6d7d8d9dadbdcdddedfe0e1e2e3e4e5e6e7e8e9eaebecedeeeff0f1f2f3f4f5f6f7f8f9fafbfcfdfeff")) == "9c4fa072db2c871a5635e37f791e93ab45049676"
#eval hex (sha1 (ofHex "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f404142434445464748494a4b4c4d4e4f505152535455565758595a5b5c5d5e5f606162636465666768696a6b6c6d6e6f707172737475767778797a7b7c7d7e7f808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9fa0a1a2a3a4a5a6a7a8a9aaabacadaeafb0b1b2b3b4b5b6b7b8b9babbbcbdbebfc0c1c2c3c4c5c6c7c8c9cacbcccdcecfd0d1d2d3d4d5d6d7d8d9dadbdcdddedfe0e1e2e3e4e5e6e7e8e9eaebecedeeeff0f1f2f3f4f5f6f7f8f9fafbfcfdfeff")) == "4916d6bdb7f78e6803698cab32d1586ea457dfc8"
#eval hex (hash256 (ofHex "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f404142434445464748494a4b4c4d4e4f505152535455565758595a5b5c5d5e5f606162636465666768696a6b6c6d6e6f707172737475767778797a7b7c7d7e7f808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9fa0a1a2a3a4a5a6a7a8a9aaabacadaeafb0b1b2b3b4b5b6b7b8b9babbbcbdbebfc0c1c2c3c4c5c6c7c8c9cacbcccdcecfd0d1d2d3d4d5d6d7d8d9dadbdcdddedfe0e1e2e3e4e5e6e7e8e9eaebecedeeeff0f1f2f3f4f5f6f7f8f9fafbfcfdfeff")) == "60bd11c69262f84ddfea5f0d116d40af862c4dd8c2a92fb90e368b132e8fa89c"
#eval hex (hash160 (ofHex "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f404142434445464748494a4b4c4d4e4f505152535455565758595a5b5c5d5e5f606162636465666768696a6b6c6d6e6f707172737475767778797a7b7c7d7e7f808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9fa0a1a2a3a4a5a6a7a8a9aaabacadaeafb0b1b2b3b4b5b6b7b8b9babbbcbdbebfc0c1c2c3c4c5c6c7c8c9cacbcccdcecfd0d1d2d3d4d5d6d7d8d9dadbdcdddedfe0e1e2e3e4e5e6e7e8e9eaebecedeeeff0f1f2f3f4f5f6f7f8f9fafbfcfdfeff")) == "07a536d93e0b9a779874e1287a226b8230cda46e"
-- 1000 bytes of 'a'
#eval hex (sha256 (List.replicate 1000 97)) == "41edece42d63e8d9bf515a9ba6932e1c20cbc9f5a5d134645adb5db1b9737ea3"
#eval hex (ripemd160 (List.replicate 1000 97)) == "aa69deee9a8922e92f8105e007f76110f381e9cf"
#eval hex (sha1 (List.replicate 1000 97)) == "291e9a6c66994949b57ba5e650361e98fc36b1ba"
#eval hex (hash256 (List.replicate 1000 97)) == "f2b6fd3c03e69a9201ec5826310c02da24d154d2fe3c9041527696bb1f693dce"
#eval hex (hash160 (List.replicate 1000 97)) == "7c2b902bbfae7c54f2498f50bc78fa46c0693802"
-- 1,000,000 bytes of 'a' (FIPS 180-2 / RIPEMD-160 paper vector)
#eval hex (sha256 (List.replicate 1000000 97)) == "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0"
#eval hex (ripemd160 (List.replicate 1000000 97)) == "52783243c1697bdbe16d37f97f68f08325dc1528"
-- Hash160 of the genesis output public key (65 bytes), the P2PKH hash of 1A1zP1eP5QGefi2DMPTfTL5SLmv7DivfNa
#eval hex (hash160 (genesisOutputScript.drop 1 |>.take 65)) == "62e907b15cbf27d5425399ebf6f0fb50ebb88f18"
-- output length and the hash of a hash
#eval (sha256 (ascii "abc")).length == 32
#eval (ripemd160 (ascii "abc")).length == 20
#eval hex (sha256 (sha256 (ascii "abc"))) == "4f8b42c22dd3729b519ba6f68d2da7cc5b2d606d05daed5ad5128cc03e6c6358"
