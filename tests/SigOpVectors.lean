import Definitions.Def_BitcoinBlock
open BitcoinBlock BitcoinSer BitcoinSig BitcoinVerify
/-! Spot 11 vectors (`REVIEW_SPOT11.md`): sigop accounting, expectations derived by hand from
`GetSigOpCount`, `GetP2SHSigOpCount`, `CountWitnessSigOps`, `GetTransactionSigOpCost`. Every line prints `true`. -/
def allF : BitcoinActivation.ScriptFlags := ⟨true, true, true, true, true, true, true⟩
def noWit : BitcoinActivation.ScriptFlags := ⟨true, false, false, true, true, true, true⟩
def noP2sh : BitcoinActivation.ScriptFlags := ⟨false, true, true, true, true, true, true⟩
def pk33 : Bytes := 0x02 :: List.replicate 32 5
def p2pkh : Bytes := [0x76, 0xa9] ++ pushBytes (List.replicate 20 1) ++ [0x88, 0xac]
def ms23 : Bytes := [0x52] ++ pushBytes pk33 ++ pushBytes pk33 ++ pushBytes pk33 ++ [0x53, 0xae]   -- 2 <pk> <pk> <pk> 3 CHECKMULTISIG
-- CScript::GetSigOpCount(fAccurate)
#eval getSigOpCount false [0xac] == 1
#eval getSigOpCount false [0xac, 0xad, 0xae, 0xaf] == 42                    -- 1 + 1 + 20 + 20
#eval getSigOpCount true [0xac, 0xad, 0xae, 0xaf] == 42                     -- no OP_n before the multisigs
#eval getSigOpCount true ms23 == 3                                          -- accurate: OP_3 precedes CHECKMULTISIG
#eval getSigOpCount false ms23 == 20
#eval getSigOpCount true ([0x52] ++ pushBytes pk33 ++ [0x60, 0xae]) == 16   -- OP_16 → 16
#eval getSigOpCount true ([0x51, 0x00, 0xae]) == 20                         -- a push (OP_0) between OP_1 and CHECKMULTISIG resets lastOpcode
#eval getSigOpCount true ([0x51] ++ pushBytes [9] ++ [0xae]) == 20
#eval getSigOpCount true ([0x4f, 0xae]) == 20                               -- OP_1NEGATE is below OP_1
#eval getSigOpCount true ([0x61, 0xae]) == 20                               -- OP_NOP is above OP_16
#eval getSigOpCount false (p2pkh ++ [0x4c]) == 1                            -- a truncated push ends the count, keeping it
#eval getSigOpCount false ([0xac, 0x02, 0xac]) == 1                         -- CHECKSIG inside a truncated push is not reached
#eval getSigOpCount false (pushBytes [0xac, 0xae]) == 0                     -- opcodes inside push data do not count
-- GetLegacySigOpCount: scriptSigs and scriptPubKeys, inaccurate
def txA : Tx := ⟨2, [⟨⟨List.replicate 32 7, 0⟩, pushesBytes [[0x30, 0x01], pk33], 0xffffffff, []⟩, ⟨⟨List.replicate 32 8, 1⟩, pushBytes ms23, 0xffffffff, []⟩],
  [⟨1, p2pkh⟩, ⟨2, ms23⟩, ⟨3, [0x6a]⟩], 0⟩
#eval legacySigOpCount txA == 21                                            -- outputs: 1 + 20 + 0; scriptSigs: pushes only
#eval legacySigOpCount ⟨2, [⟨⟨List.replicate 32 7, 0⟩, [0xac, 0xac], 0xffffffff, []⟩], [], 0⟩ == 2   -- scriptSig opcodes count too
-- GetP2SHSigOpCount per input: only P2SH spent outputs contribute
#eval p2shSigOpCount p2pkh (pushesBytes [[0x30, 0x01], pk33]) == 0          -- spent output not P2SH: nothing (F1)
#eval p2shSigOpCount (p2shBytes (hash160 ms23)) (pushesBytes [[], [0x30], [0x30], ms23]) == 3
#eval p2shSigOpCount (p2shBytes (hash160 ms23)) (pushesBytes [[], [0x30], ms23] ++ [0x51]) == 0   -- last "push" is OP_1: data empty
#eval p2shSigOpCount (p2shBytes (hash160 ms23)) (pushesBytes [ms23] ++ [0x61]) == 0               -- not push-only
#eval p2shSigOpCount (p2shBytes (hash160 ms23)) (pushBytes ms23 ++ [0x4c]) == 0                  -- malformed
-- CountWitnessSigOps
#eval countWitnessSigOps allF [] (witnessBytes 0 (List.replicate 20 1)) [[1], [2]] == 1
#eval countWitnessSigOps allF [] (witnessBytes 0 (sha256 ms23)) [[], [0x30], [0x30], ms23] == 3   -- last witness element is the script
#eval countWitnessSigOps allF [] (witnessBytes 0 (sha256 ms23)) [] == 0                            -- empty witness: nothing
#eval countWitnessSigOps allF [] (witnessBytes 1 (List.replicate 32 1)) [[1]] == 0                -- version 1 counts nothing
#eval countWitnessSigOps allF [] (witnessBytes 0 (List.replicate 25 1)) [[1]] == 0
#eval countWitnessSigOps allF (pushBytes (witnessBytes 0 (List.replicate 20 1))) (p2shBytes (hash160 (witnessBytes 0 (List.replicate 20 1)))) [[1], [2]] == 1   -- P2SH-P2WPKH
#eval countWitnessSigOps allF (pushBytes (witnessBytes 0 (sha256 ms23))) (p2shBytes (hash160 (witnessBytes 0 (sha256 ms23)))) [ms23] == 3                 -- P2SH-P2WSH
#eval countWitnessSigOps allF (pushBytes (witnessBytes 0 (sha256 ms23)) ++ [0x61]) (p2shBytes (hash160 (witnessBytes 0 (sha256 ms23)))) [ms23] == 0     -- not push-only
#eval countWitnessSigOps allF (pushesBytes [ms23]) (p2shBytes (hash160 ms23)) [ms23] == 0                                                              -- redeem script not a witness program
#eval countWitnessSigOps noWit [] (witnessBytes 0 (List.replicate 20 1)) [[1], [2]] == 0          -- WITNESS flag off
-- GetTransactionSigOpCost
def coinP2pkh : Coin := ⟨⟨5, p2pkh⟩, 9, false⟩
def coinP2sh : Coin := ⟨⟨5, p2shBytes (hash160 ms23)⟩, 9, false⟩
def coinWpkh : Coin := ⟨⟨5, witnessBytes 0 (List.replicate 20 1)⟩, 9, false⟩
def u : Ledger := [(⟨List.replicate 32 7, 0⟩, coinP2pkh), (⟨List.replicate 32 8, 1⟩, coinP2sh), (⟨List.replicate 32 9, 2⟩, coinWpkh)]
def txB : Tx := ⟨2, [⟨⟨List.replicate 32 7, 0⟩, pushesBytes [[0x30, 0x01], pk33], 0xffffffff, []⟩,
                     ⟨⟨List.replicate 32 8, 1⟩, pushesBytes [[], [0x30], [0x30], ms23], 0xffffffff, []⟩,
                     ⟨⟨List.replicate 32 9, 2⟩, [], 0xffffffff, [[0x30], pk33]⟩],
  [⟨1, p2pkh⟩], 0⟩
#eval txSigOpCost allF u txB == 4 + 12 + 1                                  -- legacy 1 (the output) ×4; P2SH 3 ×4; witness 1
#eval txSigOpCost noP2sh u txB == 4 + 0 + 1                                 -- P2SH count only with the flag
#eval txSigOpCost noWit u txB == 4 + 12 + 0
#eval txSigOpCost allF u ⟨2, [⟨⟨List.replicate 32 0, 0xffffffff⟩, [0x03, 1, 2, 3], 0xffffffff, []⟩], [⟨1, p2pkh⟩, ⟨1, ms23⟩], 0⟩ == 84   -- coinbase: legacy only, (1 + 20) × 4
#eval txSigOpCost allF u ⟨2, [⟨⟨List.replicate 32 7, 0⟩, pushesBytes [[0x30, 0x01], pk33], 0xffffffff, []⟩], [⟨1, p2pkh⟩], 0⟩ == 4   -- the probe: 4, not 8
