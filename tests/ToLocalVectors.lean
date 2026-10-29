import Definitions.Def_BitcoinToLocal

/-! Concrete checks of the `to_local` script against a stub oracle: the signature check accepts a
signature exactly when it equals the key's "expected" byte string, `checkSequence` accepts delays
up to 144. -/

open BitcoinScript BitcoinToLocal

def revKey : Bytes := [0x02, 0xaa, 0xbb]
def delKey : Bytes := [0x03, 0xcc, 0xdd]
def sigFor (pk : Bytes) : Bytes := 0x30 :: pk

def stubOracle : Oracle where
  ripemd160 := id
  sha1 := id
  sha256 := id
  hash160 := id
  hash256 := id
  checkSig := fun sig pk => some (decide (sig = sigFor pk))
  checkLockTime := fun _ => true
  checkSequence := fun n => decide (n ≤ 144)

def flagsOn : Flags := ⟨true, true, true⟩
def flagsNoCsv : Flags := ⟨true, false, true⟩

def S (d : Int) : Script := toLocalScript revKey d delKey

-- revocation path: any true selector, signature for the revocation key
example : evalScript flagsOn stubOracle [[1], sigFor revKey] (S 144) = some [[1]] := by decide +kernel
example : evalScript flagsOn stubOracle [[7], sigFor revKey] (S 144) = some [[1]] := by decide +kernel
-- wrong key on the revocation path: a clean false
example : evalScript flagsOn stubOracle [[1], sigFor delKey] (S 144) = some [[]] := by decide +kernel
-- delayed path: empty selector, delay accepted, signature for the delayed key
example : evalScript flagsOn stubOracle [[], sigFor delKey] (S 144) = some [[1]] := by decide +kernel
example : evalScript flagsOn stubOracle [[], sigFor delKey] (S 16) = some [[1]] := by decide +kernel   -- OP_16 encoding
example : evalScript flagsOn stubOracle [[], sigFor delKey] (S 1) = some [[1]] := by decide +kernel    -- OP_1 encoding
-- delay too large for the stub checker: CSV fails the script
example : evalScript flagsOn stubOracle [[], sigFor delKey] (S 145) = none := by decide +kernel
-- CSV flag off: the opcode is a NOP and the delayed path opens regardless
example : evalScript flagsNoCsv stubOracle [[], sigFor delKey] (S 145) = some [[1]] := by decide +kernel
-- negative delay with CSV on: fails
example : evalScript flagsOn stubOracle [[], sigFor delKey] (S (-1)) = none := by decide +kernel
-- wrong shapes: too few or too many elements
example : evalScript flagsOn stubOracle [] (S 144) = none := by decide +kernel
example : evalScript flagsOn stubOracle [[1]] (S 144) = none := by decide +kernel
example : evalScript flagsOn stubOracle [[1], sigFor revKey, [9]] (S 144) = some [[1], [9]] := by decide +kernel
-- the byte form parses back to the instruction form
example : BitcoinSig.parseScript (toLocalBytes revKey 144 delKey) = some (S 144) := by decide +kernel
example : BitcoinSig.parseScript (toLocalBytes revKey 16 delKey) = some (S 16) := by decide +kernel
example : toLocalBytes revKey 144 delKey =
    [0x63, 0x03, 0x02, 0xaa, 0xbb, 0x67, 0x02, 0x90, 0x00, 0xb2, 0x75, 0x03, 0x03, 0xcc, 0xdd, 0x68, 0xac] := by decide +kernel
example : toLocalBytes revKey 16 delKey =
    [0x63, 0x03, 0x02, 0xaa, 0xbb, 0x67, 0x60, 0xb2, 0x75, 0x03, 0x03, 0xcc, 0xdd, 0x68, 0xac] := by decide +kernel
