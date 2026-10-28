import Definitions.Def_BitcoinVerify
open BitcoinSer BitcoinSig BitcoinVerify
def pk : Bytes := [0x03, 0x68, 0xcc, 0xcc, 0xaa, 0x8a, 0xa1, 0x59, 0xbc, 0x49, 0xbc, 0x17, 0x52, 0x5b, 0x20, 0x87, 0x42, 0x89, 0x99, 0xce, 0xaa, 0x90, 0x28, 0x85, 0xd4, 0xd6, 0x14, 0x05, 0xed, 0xde, 0x23, 0x1f, 0x76]
def h160 : Bytes := [0x19, 0x9c, 0xbf, 0xa5, 0x42, 0xc3, 0xe8, 0x44, 0x5f, 0x47, 0x58, 0xf2, 0x1e, 0x40, 0xc5, 0x29, 0xf3, 0x6a, 0xf7, 0x05]
def sigw : Bytes := [0x30, 0x45, 0x02, 0x21, 0x00, 0xbb, 0xdc, 0x44, 0xd2, 0x0d, 0xfd, 0x9a, 0xad, 0xb2, 0x10, 0xc5, 0x97, 0x3b, 0x17, 0x35, 0x7e, 0x45, 0xd7, 0x58, 0xc1, 0xd5, 0x87, 0x5d, 0xcc, 0x8c, 0x5e, 0x6a, 0xd6, 0xba, 0x51, 0x4b, 0xd9, 0x02, 0x20, 0x5b, 0x59, 0x38, 0x9a, 0xbd, 0x3e, 0xd9, 0xee, 0x16, 0xf2, 0x24, 0x67, 0x4e, 0xd7, 0x40, 0xb3, 0x99, 0x86, 0x5d, 0x67, 0x7c, 0xe1, 0x4e, 0x52, 0x8b, 0x49, 0x7c, 0x68, 0xe4, 0xf5, 0xd7, 0x6f, 0x01]
def redeem : Bytes := [0x21, 0x03, 0x68, 0xcc, 0xcc, 0xaa, 0x8a, 0xa1, 0x59, 0xbc, 0x49, 0xbc, 0x17, 0x52, 0x5b, 0x20, 0x87, 0x42, 0x89, 0x99, 0xce, 0xaa, 0x90, 0x28, 0x85, 0xd4, 0xd6, 0x14, 0x05, 0xed, 0xde, 0x23, 0x1f, 0x76, 0xac]
def sigl : Bytes := [0x30, 0x44, 0x02, 0x20, 0x38, 0xee, 0xac, 0xfd, 0x88, 0x33, 0x62, 0x76, 0x0d, 0x2c, 0x42, 0x96, 0x8b, 0x09, 0xde, 0x1a, 0xa6, 0x94, 0xa5, 0x56, 0xdf, 0x80, 0xd2, 0x41, 0xa2, 0x3f, 0x97, 0xb7, 0xdc, 0xcd, 0x53, 0x25, 0x02, 0x20, 0x19, 0xf7, 0x98, 0x86, 0x23, 0x96, 0xc1, 0x9f, 0xcf, 0xcc, 0x9c, 0x13, 0xcd, 0xff, 0xe7, 0x2e, 0xe1, 0x2c, 0xca, 0x77, 0xda, 0x72, 0xb6, 0x7f, 0xc6, 0x33, 0x45, 0x6f, 0xc3, 0x8a, 0xb2, 0x02, 0x01]
def h160r : Bytes := [0x7b, 0x91, 0xf5, 0x64, 0xa1, 0xfa, 0x83, 0xb1, 0x31, 0x3a, 0xd8, 0x9e, 0x29, 0x63, 0xa9, 0x7b, 0x4a, 0xc5, 0x45, 0xb7]
def allF : BitcoinActivation.ScriptFlags := ⟨true, true, true, true, true, true, true⟩
def txW : Tx := ⟨2, [⟨⟨List.replicate 32 0x22, 1⟩, [], 0xfffffffe, []⟩], [⟨900, [0x76,0xa9,0x14] ++ List.replicate 20 0 ++ [0x88,0xac]⟩], 0⟩
def c : Ctx := ⟨allF, txW, 0, 1000⟩
def noTap : TaprootHandler := fun _ _ _ => false
-- native P2WPKH
#eval verifyScript noTap c [] (witnessBytes 0 h160) [sigw, pk]            -- true
#eval verifyScript noTap c [] (witnessBytes 0 h160) [sigw, pk.reverse]    -- false
#eval verifyScript noTap c [0x00] (witnessBytes 0 h160) [sigw, pk]        -- false (scriptSig must be empty)
#eval verifyScript noTap c [] (witnessBytes 0 h160) [sigw]                -- false (2 items needed)
-- P2SH-P2WPKH: redeem = witnessBytes 0 h160, scriptSig = push redeem, spk = p2sh(hash160 redeem)
#eval verifyScript noTap c (pushBytes (witnessBytes 0 h160)) (p2shBytes (hash160 (witnessBytes 0 h160))) [sigw, pk]   -- true
#eval verifyScript noTap c (pushBytes (witnessBytes 0 h160)) (p2shBytes (hash160 (witnessBytes 0 h160))) []           -- false
-- legacy P2SH with p2pk redeem
#eval verifyScript noTap c (pushesBytes [sigl, redeem]) (p2shBytes h160r) []     -- true
#eval verifyScript noTap c (pushesBytes [sigw, redeem]) (p2shBytes h160r) []     -- false (wrong sighash)
#eval verifyScript noTap c (pushesBytes [sigl, redeem]) (p2shBytes h160r) [[1]]  -- false (unexpected witness)
#eval verifyScript noTap c (pushesBytes [sigl, redeem] ++ [0x76]) (p2shBytes h160r) []  -- false (not push-only: OP_DUP)
-- P2SH flag off: p2sh script is just hash check
#eval verifyScript noTap ⟨{ allF with p2sh := false, witness := false }, txW, 0, 1000⟩ (pushesBytes [[1], redeem]) (p2shBytes h160r) []   -- true
-- unknown witness version, P2A
#eval verifyScript noTap c [] (witnessBytes 2 (List.replicate 32 9)) [[5]]   -- true
#eval verifyScript noTap c [] (witnessBytes 2 (List.replicate 32 0)) [[5]]   -- false (program all zero → EVAL_FALSE)
#eval verifyScript noTap c [] (witnessBytes 1 [0x4e, 0x73]) [[5]]           -- true (P2A)
#eval verifyScript noTap c [] (witnessBytes 1 (List.replicate 32 9)) [[5]]  -- false (taproot handler false)
#eval verifyScript noTap ⟨{ allF with taproot := false }, txW, 0, 1000⟩ [] (witnessBytes 1 (List.replicate 32 9)) [[5]]  -- true (taproot flag off)
-- P2WSH with script OP_1
#eval verifyScript noTap c [] (witnessBytes 0 (sha256 [0x51])) [[0x51]]   -- true
#eval verifyScript noTap c [] (witnessBytes 0 (sha256 [0x51])) [[1], [0x51]]   -- false (cleanstack: 2 elements left)
#eval isWitnessProgram (witnessBytes 0 h160)
#eval isPayToScriptHash (p2shBytes h160r) && isPushOnly (pushesBytes [sigl, redeem])

/-! ### Adversarial dispatch vectors from the spot 7 review (`REVIEW_SPOT7.md`). Every line prints `true`. -/
def wsTrue : Bytes := [0x51]                                  -- witness script `OP_1`
def p2wshTrue : Bytes := witnessBytes 0 (sha256 wsTrue)
def noWit : Ctx := ⟨{ allF with witness := false }, txW, 0, 1000⟩
def noP2sh : Ctx := ⟨{ allF with p2sh := false }, txW, 0, 1000⟩
-- native P2WSH: script hash match, execution, clean stack, empty witness, oversized element
#eval verifyScript noTap c [] p2wshTrue [wsTrue] == true
#eval verifyScript noTap c [] p2wshTrue [[1], wsTrue] == false            -- two elements left
#eval verifyScript noTap c [] p2wshTrue [[0x52]] == false                 -- hash mismatch
#eval verifyScript noTap c [] p2wshTrue [] == false                       -- empty witness
#eval verifyScript noTap c [] (witnessBytes 0 (sha256 [0x75, 0x51])) [List.replicate 521 1, [0x75, 0x51]] == false   -- element over 520 bytes
#eval verifyScript noTap c [] (witnessBytes 0 (sha256 [0x75, 0x51])) [List.replicate 520 1, [0x75, 0x51]] == true    -- OP_DROP OP_1 with a 520-byte element
#eval verifyScript noTap c [] (witnessBytes 0 (sha256 [0x00])) [[0x00]] == false                                     -- script `OP_0` leaves false
#eval verifyScript noTap c [] (witnessBytes 0 (sha256 [])) [[]] == false                                             -- empty script leaves nothing
-- version 0 with a program that is neither 20 nor 32 bytes
#eval verifyScript noTap c [] (witnessBytes 0 (List.replicate 25 7)) [[1]] == false
-- P2WPKH needs exactly two elements; the implied script is DUP HASH160 <h> EQUALVERIFY CHECKSIG
#eval verifyScript noTap c [] (witnessBytes 0 h160) [sigw, pk, []] == false
#eval verifyScript noTap c [] (witnessBytes 0 h160) [[], pk] == false                 -- empty signature: CHECKSIG false
-- unknown versions and P2SH-wrapped version 1 are anyone-can-spend; pay-to-anchor too
#eval verifyScript noTap c [] (witnessBytes 16 (List.replicate 40 1)) [[9], [8]] == true
#eval verifyScript noTap c [] (witnessBytes 1 (List.replicate 20 1)) [] == true       -- v1 with a 20-byte program is unknown, not taproot
#eval verifyScript noTap c [] (witnessBytes 1 [0x4e, 0x73]) [[1]] == true             -- pay-to-anchor
#eval verifyScript noTap c (pushBytes (witnessBytes 1 (List.replicate 32 1))) (p2shBytes (hash160 (witnessBytes 1 (List.replicate 32 1)))) [[1]] == true   -- P2SH-wrapped v1: handler not consulted
#eval verifyScript noTap c [] (witnessBytes 1 (List.replicate 32 1)) [[1]] == false   -- native v1 with TAPROOT flag: the (false) handler decides
#eval verifyScript noTap ⟨{ allF with taproot := false }, txW, 0, 1000⟩ [] (witnessBytes 1 (List.replicate 32 1)) [[1]] == true   -- TAPROOT flag off: success
-- malleability rules
#eval verifyScript noTap c (pushBytes (witnessBytes 0 h160) ++ [0x51]) (p2shBytes (hash160 (witnessBytes 0 h160))) [sigw, pk] == false   -- wrapped: scriptSig must be exactly the push
#eval verifyScript noTap c (pushBytes [] ++ pushBytes (witnessBytes 0 h160)) (p2shBytes (hash160 (witnessBytes 0 h160))) [sigw, pk] == false
#eval verifyScript noTap c [0x51] (witnessBytes 0 h160) [sigw, pk] == false          -- native: scriptSig must be empty
#eval verifyScript noTap c [] (witnessBytes 0 h160) [sigw, pk] == true
-- P2SH: push-only, empty scriptSig, the stack copy, unexpected witness after a P2SH redeem
#eval verifyScript noTap c [] (p2shBytes h160r) [] == false                            -- empty scriptSig fails at OP_HASH160
#eval verifyScript noTap c (pushesBytes [[1], [0x51]]) (p2shBytes (hash160 [0x51])) [] == true        -- redeem `OP_1` on the restored stack
#eval verifyScript noTap c (pushesBytes [[1], [0x51]]) (p2shBytes (hash160 [0x51])) [[1]] == false   -- unexpected witness
#eval verifyScript noTap c (pushesBytes [[0x51]]) (p2shBytes (hash160 [0x51])) [[1]] == false
#eval verifyScript noTap c (pushesBytes [[], [0x51]]) (p2shBytes (hash160 [0x51])) [] == true        -- the restored stack keeps the pushed `[]`
#eval verifyScript noTap c (pushesBytes [[0x75, 0x51]]) (p2shBytes (hash160 [0x75, 0x51])) [] == false   -- redeem `OP_DROP OP_1` on an empty restored stack
#eval verifyScript noTap c (pushesBytes [[7], [0x75, 0x51]]) (p2shBytes (hash160 [0x75, 0x51])) [] == true
#eval verifyScript noTap c ([0x51] ++ pushesBytes [[0x51]]) (p2shBytes (hash160 [0x51])) [] == true   -- OP_1 is at most OP_16: push-only
#eval verifyScript noTap c ([0x61] ++ pushesBytes [[0x51]]) (p2shBytes (hash160 [0x51])) [] == false  -- OP_NOP is not
-- flags off: without WITNESS a program output is a plain script and a witness is never unexpected; without P2SH the hash test is all
#eval verifyScript noTap noWit [0x51] (witnessBytes 0 h160) [sigw, pk] == true
#eval verifyScript noTap noWit (pushesBytes [[1], [0x51]]) (p2shBytes (hash160 [0x51])) [[1]] == true
#eval verifyScript noTap noP2sh (pushesBytes [[0x51]]) (p2shBytes (hash160 [0x51])) [] == true
#eval verifyScript noTap noP2sh (pushesBytes [[0x51]]) (p2shBytes (hash160 [0x51])) [[1]] == false   -- witness unexpected still applies
-- scripts over 10,000 bytes fail before evaluation
#eval verifyScript noTap c [] (List.replicate 10001 0x61 ++ [0x51]) [] == false
#eval verifyScript noTap c [] (List.replicate 10000 0x61) [] == false                 -- 10,000 NOPs: within size, over the op count
#eval verifyScript noTap c [] (List.replicate 199 0x61 ++ [0x51]) [] == true
