import Definitions.Def_BitcoinFunding
open BitcoinScript BitcoinFunding BitcoinToLocal

def k1 : Bytes := [0x02, 0x11]
def k2 : Bytes := [0x03, 0x22]
def sigFor (pk : Bytes) : Bytes := 0x30 :: pk
def stub : Oracle where
  ripemd160 := id; sha1 := id; sha256 := id; hash160 := id; hash256 := id
  checkSig := fun sig pk => some (decide (sig = sigFor pk))
  checkLockTime := fun _ => true; checkSequence := fun _ => true
def fOn : Flags := ⟨true, true, true⟩
def fNoDummy : Flags := ⟨true, true, false⟩

-- the BOLT witness `0 sig1 sig2`: stack top first [sig2, sig1, []]
example : evalScript fOn stub [sigFor k2, sigFor k1, []] (fundingScript k1 k2) = some [[1]] := by decide +kernel
-- signatures swapped: fails (loop cannot match sig2 to k1 first... it yields false)
example : evalScript fOn stub [sigFor k1, sigFor k2, []] (fundingScript k1 k2) = some [[]] := by decide +kernel
-- non-empty dummy under NULLDUMMY fails; without NULLDUMMY it passes
example : evalScript fOn stub [sigFor k2, sigFor k1, [1]] (fundingScript k1 k2) = none := by decide +kernel
example : evalScript fNoDummy stub [sigFor k2, sigFor k1, [1]] (fundingScript k1 k2) = some [[1]] := by decide +kernel
-- too few elements
example : evalScript fOn stub [sigFor k2, sigFor k1] (fundingScript k1 k2) = none := by decide +kernel
-- byte form
example : fundingBytes k1 k2 = [0x52, 0x02, 0x02, 0x11, 0x02, 0x03, 0x22, 0x52, 0xae] := by decide +kernel
example : BitcoinSig.parseScript (fundingBytes k1 k2) = some (fundingScript k1 k2) := by decide +kernel
