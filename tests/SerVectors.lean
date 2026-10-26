import Definitions.Def_BitcoinSer
open BitcoinSer
def hex (b : Bytes) : String := String.join (b.map fun x => let s := (Nat.toDigits 16 x.toNat); String.ofList (if s.length = 1 then '0' :: s else s))
def ascii (s : String) : Bytes := s.toUTF8.toList.map fun c => BitVec.ofNat 8 c.toNat
#eval hex (sha256 (ascii "abc"))          -- ba7816bf...
#eval hex (sha256 [])                     -- e3b0c442...
#eval hex (sha256 (ascii "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq")) -- 248d6a61...
#eval hex (ripemd160 (ascii "abc"))       -- 8eb208f7...
#eval hex (ripemd160 [])                  -- 9c1185a5...
#eval hex (sha1 (ascii "abc"))            -- a9993e36...
#eval hex (txid genesisCoinbase) == hex genesisMerkleRoot
#eval hex (headerHash genesisHeader) == hex genesisHash
#eval (serHeader genesisHeader).length
#eval readCompactSize true (writeCompactSize 252 ++ [1]) 
#eval readCompactSize true (writeCompactSize 253 ++ [1])
#eval readCompactSize true (writeCompactSize 70000 ++ [1])
#eval readCompactSize false (writeCompactSize 5000000000 ++ [1])
#eval readCompactSize true (writeCompactSize 5000000000 ++ [1])   -- none (range)
#eval readCompactSize true [0xfd, 0x10, 0x00]  -- non canonical → none
#eval readTx false (serTx false genesisCoinbase ++ [9]) == some (genesisCoinbase, [9])
#eval readBlock true (serBlock true genesisBlock) == some (genesisBlock, [])
def wtx : Tx := { genesisCoinbase with vin := [⟨⟨List.replicate 32 0, 0xffffffff⟩, genesisScriptSig, 0xffffffff, [[1,2],[]]⟩] }
#eval readTx true (serTx true wtx ++ [7]) == some (wtx, [7])
#eval readTx false (serTx false wtx ++ [7]) == some (wtx.stripWitness, [7])
#eval (serTx true wtx).take 6
#eval txWeight genesisCoinbase == 4 * (serTx false genesisCoinbase).length
#eval (serBlock false genesisBlock).length  -- 285
