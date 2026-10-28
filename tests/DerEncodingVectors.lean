import Definitions.Def_BitcoinSig
open BitcoinSig BitcoinSer
def hexDigit (c : Char) : Nat := if c.isDigit then c.toNat - 48 else if c.isLower then c.toNat - 87 else c.toNat - 55
def hx (s : String) : Bytes := let cs := s.toList; (List.range (cs.length / 2)).map fun i => BitVec.ofNat 8 (hexDigit (cs.getD (2*i) '0') * 16 + hexDigit (cs.getD (2*i+1) '0'))
def dersig : SigFlags := ⟨true, false, false, false⟩
def nofl : SigFlags := ⟨false, false, false, false⟩
/-! Spot 5 vectors (generator tests/reference/derencoding_reference.py): IsValidSignatureEncoding rule by rule. Every line prints `true`. -/
#eval isValidSignatureEncoding (hx "3045022100f32b989e38ed201385e65eb434227b07c764ae8e5b5e4d9059fb240c02e4a97e02207e5e687185f1a06ceae87cc7b8d5d426e6770f9cf6138ac442825a58b259c5b201") == true   -- strict DER + hashtype
#eval isValidSignatureEncoding (hx "3045022100f32b98") == false   -- 8 bytes
#eval isValidSignatureEncoding (hx "3045022100f32b989e38ed201385e65eb434227b07c764ae8e5b5e4d9059fb240c02e4a97e02207e5e687185f1a06ceae87cc7b8d5d426e6770f9cf6138ac442825a58b259c5b20100") == false   -- 74 bytes
#eval isValidSignatureEncoding (hx "3145022100f32b989e38ed201385e65eb434227b07c764ae8e5b5e4d9059fb240c02e4a97e02207e5e687185f1a06ceae87cc7b8d5d426e6770f9cf6138ac442825a58b259c5b201") == false   -- tag 0x31
#eval isValidSignatureEncoding (hx "3046022100f32b989e38ed201385e65eb434227b07c764ae8e5b5e4d9059fb240c02e4a97e02207e5e687185f1a06ceae87cc7b8d5d426e6770f9cf6138ac442825a58b259c5b201") == false   -- sequence length off by one
#eval isValidSignatureEncoding (hx "3045032100f32b989e38ed201385e65eb434227b07c764ae8e5b5e4d9059fb240c02e4a97e02207e5e687185f1a06ceae87cc7b8d5d426e6770f9cf6138ac442825a58b259c5b201") == false   -- R tag 0x03
#eval isValidSignatureEncoding (hx "3045024300f32b989e38ed201385e65eb434227b07c764ae8e5b5e4d9059fb240c02e4a97e02207e5e687185f1a06ceae87cc7b8d5d426e6770f9cf6138ac442825a58b259c5b201") == false   -- lenR covering the rest
#eval isValidSignatureEncoding (hx "3045022100f32b989e38ed201385e65eb434227b07c764ae8e5b5e4d9059fb240c02e4a97e021f7e5e687185f1a06ceae87cc7b8d5d426e6770f9cf6138ac442825a58b259c5b201") == false   -- lenR + lenS + 7 != size (lenS - 1, length fixed)
#eval isValidSignatureEncoding (hx "3024020002207e5e687185f1a06ceae87cc7b8d5d426e6770f9cf6138ac442825a58b259c5b201") == false   -- lenR = 0 (rebuilt)
#eval isValidSignatureEncoding (hx "30440220f32b989e38ed201385e65eb434227b07c764ae8e5b5e4d9059fb240c02e4a97e02207e5e687185f1a06ceae87cc7b8d5d426e6770f9cf6138ac442825a58b259c5b201") == false   -- R negative (high bit)
#eval isValidSignatureEncoding (hx "304602220000f32b989e38ed201385e65eb434227b07c764ae8e5b5e4d9059fb240c02e4a97e02207e5e687185f1a06ceae87cc7b8d5d426e6770f9cf6138ac442825a58b259c5b201") == false   -- R padded unnecessarily
#eval isValidSignatureEncoding (hx "3045022100f32b989e38ed201385e65eb434227b07c764ae8e5b5e4d9059fb240c02e4a97e03207e5e687185f1a06ceae87cc7b8d5d426e6770f9cf6138ac442825a58b259c5b201") == false   -- S tag 0x03
#eval isValidSignatureEncoding (hx "3025022100f32b989e38ed201385e65eb434227b07c764ae8e5b5e4d9059fb240c02e4a97e020001") == false   -- lenS = 0 (rebuilt)
#eval isValidSignatureEncoding (hx "3045022100f32b989e38ed201385e65eb434227b07c764ae8e5b5e4d9059fb240c02e4a97e0220805e687185f1a06ceae87cc7b8d5d426e6770f9cf6138ac442825a58b259c5b201") == false   -- S negative (high bit)
#eval isValidSignatureEncoding (hx "3046022100f32b989e38ed201385e65eb434227b07c764ae8e5b5e4d9059fb240c02e4a97e0221007e5e687185f1a06ceae87cc7b8d5d426e6770f9cf6138ac442825a58b259c5b201") == false   -- S padded unnecessarily
#eval isValidSignatureEncoding (hx "3046022100f32b989e38ed201385e65eb434227b07c764ae8e5b5e4d9059fb240c02e4a97e02210081a1978e7a0e5f9315178338472a2bd7d437cd49b93515777d5004341ddc7b8f01") == true   -- high S is still valid DER
#eval isValidSignatureEncoding (hx "3045022100f32b989e38ed201385e65eb434227b07c764ae8e5b5e4d9059fb240c02e4a97e02207e5e687185f1a06ceae87cc7b8d5d426e6770f9cf6138ac442825a58b259c5b2ff") == true   -- hash type byte arbitrary (0xff)
#eval isValidSignatureEncoding (hx "300602010102010101") == true   -- minimal 9-byte signature
#eval isValidSignatureEncoding (hx "3046022100ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff022100ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01") == true   -- 73-byte maximal signature
-- CheckSignatureEncoding: the empty signature always passes; with DERSIG off nothing is checked; LOW_S and STRICTENC are policy
#eval checkSignatureEncoding dersig [] == true
#eval checkSignatureEncoding dersig (hx "3145022100f32b989e38ed201385e65eb434227b07c764ae8e5b5e4d9059fb240c02e4a97e02207e5e687185f1a06ceae87cc7b8d5d426e6770f9cf6138ac442825a58b259c5b201") == false
#eval checkSignatureEncoding nofl (hx "3145022100f32b989e38ed201385e65eb434227b07c764ae8e5b5e4d9059fb240c02e4a97e02207e5e687185f1a06ceae87cc7b8d5d426e6770f9cf6138ac442825a58b259c5b201") == true
#eval checkSignatureEncoding nofl (hx "deadbeef") == true
#eval checkSignatureEncoding ⟨true, true, false, false⟩ (hx "3046022100f32b989e38ed201385e65eb434227b07c764ae8e5b5e4d9059fb240c02e4a97e02210081a1978e7a0e5f9315178338472a2bd7d437cd49b93515777d5004341ddc7b8f01") == false   -- LOW_S (policy) rejects a high S
#eval checkSignatureEncoding ⟨true, false, true, false⟩ (hx "3045022100f32b989e38ed201385e65eb434227b07c764ae8e5b5e4d9059fb240c02e4a97e02207e5e687185f1a06ceae87cc7b8d5d426e6770f9cf6138ac442825a58b259c5b200") == false   -- STRICTENC (policy) rejects hash type 0
#eval checkSignatureEncoding ⟨true, false, true, false⟩ (hx "3045022100f32b989e38ed201385e65eb434227b07c764ae8e5b5e4d9059fb240c02e4a97e02207e5e687185f1a06ceae87cc7b8d5d426e6770f9cf6138ac442825a58b259c5b283") == true    -- SINGLE|ANYONECANPAY is defined
-- CheckPubKeyEncoding: consensus never sets STRICTENC or WITNESS_PUBKEYTYPE
#eval checkPubKeyEncoding dersig .base (hx "06f028892bad7ed57d2fb57bf33081d5cfcf6f9ed3d3d7f159c2e2fff579dc341a0000000000000000000000000000000000000000000000000000000000000000") == true
#eval checkPubKeyEncoding ⟨true, false, true, false⟩ .base (hx "06f028892bad7ed57d2fb57bf33081d5cfcf6f9ed3d3d7f159c2e2fff579dc341a0000000000000000000000000000000000000000000000000000000000000000") == false   -- hybrid rejected only by STRICTENC
#eval checkPubKeyEncoding ⟨true, false, false, true⟩ .witnessV0 (hx "04f028892bad7ed57d2fb57bf33081d5cfcf6f9ed3d3d7f159c2e2fff579dc341a0000000000000000000000000000000000000000000000000000000000000000") == false   -- uncompressed rejected only by WITNESS_PUBKEYTYPE under v0
#eval checkPubKeyEncoding ⟨true, false, false, true⟩ .base (hx "04f028892bad7ed57d2fb57bf33081d5cfcf6f9ed3d3d7f159c2e2fff579dc341a0000000000000000000000000000000000000000000000000000000000000000") == true
