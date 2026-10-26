import Definitions.Def_BitcoinVerify
open BitcoinVerify BitcoinSer BitcoinSig
open BitcoinScript hiding Bytes Byte

theorem BitcoinVerify.isPayToScriptHash_iff (s : Bytes) :
    BitcoinVerify.isPayToScriptHash s = true ↔ ∃ h : Bytes, h.length = 20 ∧ s = BitcoinVerify.p2shBytes h := by sorry
