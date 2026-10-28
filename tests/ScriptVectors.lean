import Definitions.Def_BitcoinScript
open BitcoinScript
def O : Oracle where
  ripemd160 := id
  sha1 := id
  sha256 := id
  hash160 := fun b => b.map (fun x => x + 1)
  hash256 := id
  checkSig := fun sig pk => some (sig == pk.map (fun x => x + 2))
  checkLockTime := fun _ => true
  checkSequence := fun _ => true
def F : Flags := ⟨true, true, true⟩
#eval serialize 0 == [] && serialize 1 == [1] && serialize (-1) == [0x81] && serialize 127 == [0x7f] && serialize 128 == [0x80, 0x00] && serialize (-128) == [0x80, 0x80] && serialize 255 == [0xff, 0x00] && serialize 256 == [0x00, 0x01] && serialize (-256) == [0x00, 0x81]
#eval (List.range 1000).all fun i => let v : Int := i - 500; setVch (serialize v) == v
#eval [castToBool [], castToBool [0], castToBool [0x80], castToBool [0,0x80], castToBool [1], castToBool [0x80, 0], castToBool [0,1]]  -- F F F F T T T
#eval [nonMinimal [0], nonMinimal [0x80], nonMinimal [1,0], nonMinimal [0xff,0], nonMinimal [1], nonMinimal [0x7f, 0x80], nonMinimal [0x80, 0x80]]  -- T T T F F F T
-- P2PKH: pk=[5], h=hash160 pk=[6], sig = pk+2 = [7]
#eval verifyScriptPlain F O [.push [7], .push [5]] (p2pkhScript [6])        -- true
#eval verifyScriptPlain F O [.push [8], .push [5]] (p2pkhScript [6])        -- false (bad sig)
#eval verifyScriptPlain F O [.push [7], .push [5]] (p2pkhScript [9])        -- false (bad hash)
#eval evalScript F O [] [.push [2], .push [3], .op OP_ADD]                   -- some [[5]]
#eval evalScript F O [] [.push [5], .push [3], .op OP_SUB]                   -- some [[2]]
#eval evalScript F O [] [.push [3], .push [5], .op OP_SUB]                   -- some [[0x82]]  (-2)
#eval evalScript F O [] [.op OP_1, .op OP_IF, .op (0x52 : Byte), .op OP_ELSE, .op (0x53 : Byte), .op OP_ENDIF]   -- some [[2]]
#eval evalScript F O [] [.op OP_1NEGATE, .op OP_IF, .op (0x52 : Byte), .op OP_ELSE, .op (0x53 : Byte), .op OP_ENDIF] -- some [[2]] (nonzero true)
#eval evalScript F O [] [.push [], .op OP_IF, .op (0x52 : Byte), .op OP_ELSE, .op (0x53 : Byte), .op OP_ENDIF]   -- some [[3]]
#eval evalScript F O [] [.push [], .op OP_IF, .op OP_CAT, .op OP_ENDIF]      -- none (disabled even unexecuted)
#eval evalScript F O [] [.push [], .op OP_IF, .op OP_RETURN, .op OP_ENDIF]   -- some [] (unexecuted RETURN ok)
#eval evalScript F O [] [.op OP_IF]                                           -- none (stack empty)
#eval evalScript F O [] [.op OP_1, .op OP_IF]                                 -- none (unbalanced)
#eval evalScript F O [] [.op OP_1, .op (0x52 : Byte), .op (0x53 : Byte), .op OP_ROT]            -- some [[1],[3],[2]]  (x2 x3 x1, top x1)
#eval evalScript F O [] [.op OP_1, .op (0x52 : Byte), .op (0x53 : Byte), .op (0x52 : Byte), .op OP_PICK] -- some [[1],[3],[2],[1]]
#eval evalScript F O [] [.op OP_1, .op (0x52 : Byte), .op (0x53 : Byte), .op (0x52 : Byte), .op OP_ROLL] -- some [[1],[3],[2]]
#eval evalScript F O [] [.op OP_1, .op (0x52 : Byte), .op OP_TUCK]                     -- some [[2],[1],[2]]
#eval evalScript F O [] [.op OP_16, .op OP_DEPTH]                             -- some [[1],[16]]
#eval evalScript F O [] [.push [1,2,3], .op OP_SIZE]                          -- some [[3],[1,2,3]]
#eval evalScript F O [] [.op OP_1, .op (0x52 : Byte), .op (0x53 : Byte), .op OP_WITHIN]         -- 1 in [2,3)? no → [[]]
#eval evalScript F O [] [.op (0x52 : Byte), .op OP_1, .op (0x53 : Byte), .op OP_WITHIN]         -- 2 in [1,3) yes → [[1]]
#eval evalScript F O [] [.push [0,0,0,0,1], .op OP_1ADD]                       -- none (5-byte operand)
#eval evalScript F O [] [.push [0xff,0xff,0xff,0x7f], .op OP_1ADD]              -- some [[0,0,0,0x80,0]] (2^31, 5 bytes ok as result)
-- 1-of-2 multisig: sigs [7] against keys [5],[9]; checkSig(sig,key) = sig == key+2 → matches key 5
#eval evalScript F O [] [.push [], .push [7], .op OP_1, .push [9], .push [5], .op (0x52 : Byte), .op OP_CHECKMULTISIG]  -- keys top-first: [5] then [9]... checker matches first key [5]? top key is nk-1... 
#eval evalScript F O [] [.push [], .push [7], .op OP_1, .push [5], .push [9], .op (0x52 : Byte), .op OP_CHECKMULTISIG]
#eval evalScript F O [] [.push [1], .push [7], .op OP_1, .push [5], .op OP_1, .op OP_CHECKMULTISIG]  -- nulldummy nonempty → none
#eval (evalScript F O [] ((List.replicate 201 (Instr.op OP_NOP)))).isSome    -- true (201 ops)
#eval (evalScript F O [] ((List.replicate 202 (Instr.op OP_NOP)))).isSome    -- false
#eval (evalScript F O [] ((List.replicate 1000 (Instr.push [1])))).isSome    -- true
#eval (evalScript F O [] ((List.replicate 1001 (Instr.push [1])))).isSome    -- false
#eval (evalScript F O [] (Instr.op OP_1 :: List.replicate 201 (Instr.op OP_NOP))).isSome    -- true: OP_1 not counted
#eval (evalScript F O [] (List.replicate 201 (Instr.op OP_NOP) ++ [Instr.op OP_1, Instr.op (0x52 : Byte), Instr.op OP_1NEGATE])).isSome    -- true
#eval (evalScript F O [] (List.replicate 202 (Instr.op OP_NOP))).isSome    -- false

/-! ### Adversarial vectors from the spot 1 review (`REVIEW_SPOT1.md`). Every line prints `true`. -/
def nop (n : Nat) : Script := List.replicate n (Instr.op OP_NOP)
def F0 : Flags := ⟨true, true, false⟩   -- NULLDUMMY off
def k (n : Nat) : Instr := .op (BitVec.ofNat 8 (0x50 + n))   -- OP_n
-- 1. operation count: 201 allowed, 202 not; OP_16 never counts
#eval (evalScript F O [] (nop 200 ++ [.op OP_1])).isSome == true
#eval (evalScript F O [] (nop 201 ++ [.op OP_1])).isSome == true
#eval (evalScript F O [] (nop 202 ++ [.op OP_1])).isSome == false
#eval (evalScript F O [] ((List.replicate 100 [Instr.op OP_NOP, Instr.op OP_16, Instr.op OP_DROP]).flatten ++ [.op OP_1])).isSome == true   -- 200 counted ops
#eval (evalScript F O [] ((List.replicate 101 [Instr.op OP_NOP, Instr.op OP_16, Instr.op OP_DROP]).flatten ++ [.op OP_1])).isSome == false  -- 202 counted ops
-- 2. disabled opcode in an unexecuted branch
#eval evalScript F O [] [.push [], .op OP_IF, .op OP_CAT, .op OP_ENDIF, .op OP_1] == none
-- 3. OP_VER skipped when unexecuted, OP_VERIF never
#eval evalScript F O [] [.push [], .op OP_IF, .op (0x62 : Byte), .op OP_ENDIF, .op OP_1] == some [[1]]
#eval evalScript F O [] [.push [], .op OP_IF, .op (0x65 : Byte), .op OP_ENDIF, .op OP_1] == none
#eval evalScript F O [] [.op (0x62 : Byte)] == none
-- 4. toggling a top that is not the first false, and one that is
#eval evalScript F O [] [.push [], .op OP_IF, .op OP_1, .op OP_IF, .op OP_ELSE, .op OP_ENDIF, .op OP_ELSE, k 2, .op OP_ENDIF] == some [[2]]
#eval evalScript F O [] [.op OP_1, .op OP_IF, .push [], .op OP_IF, .op OP_ELSE, k 3, .op OP_ENDIF, .op OP_ELSE, k 2, .op OP_ENDIF] == some [[3]]
#eval evalScript F O [] [.op OP_1, .op OP_IF, .op OP_ELSE, .op OP_ELSE, k 4, .op OP_ENDIF] == some [[4]]  -- double ELSE re-enables
-- 5. the 1000-element limit counts both stacks
#eval (evalScript F O [] (List.replicate 999 (Instr.push [1]) ++ [.op OP_TOALTSTACK, .op OP_1, .op OP_1])).isSome == false
#eval (evalScript F O [] (List.replicate 998 (Instr.push [1]) ++ [.op OP_TOALTSTACK, .op OP_1, .op OP_1])).isSome == true
-- 6. stack-shuffling order
#eval evalScript F O [] [.op OP_1, k 2, k 3, k 4, k 5, k 6, .op OP_2ROT] == some [[2],[1],[6],[5],[4],[3]]
#eval evalScript F O [] [.op OP_1, k 2, k 3, k 4, .op OP_2SWAP] == some [[2],[1],[4],[3]]
#eval evalScript F O [] [.op OP_1, k 2, k 3, k 4, .op OP_2OVER] == some [[2],[1],[4],[3],[2],[1]]
#eval evalScript F O [] [.op OP_1, k 2, k 3, .op OP_3DUP] == some [[3],[2],[1],[3],[2],[1]]
#eval evalScript F O [] [.op OP_1, k 2, k 3, .push [], .op OP_ROLL] == some [[3],[2],[1]]       -- roll 0 is a no-op
#eval evalScript F O [] [.op OP_1, k 2, k 3, k 3, .op OP_PICK] == none                           -- index out of range
#eval evalScript F O [] [.op OP_1, k 2, k 3, .op OP_1NEGATE, .op OP_PICK] == none                 -- negative index
-- 7. negative zero
#eval evalScript F O [] [.push [0x80], .op OP_NOT] == some [[1]]
#eval evalScript F O [] [.push [0x80], .op OP_IF, .push [], .op OP_ELSE, .op OP_1, .op OP_ENDIF] == some [[1]]
#eval evalScript F O [] [.push [0x80], .op OP_1, .op OP_NUMEQUAL] == some [[]]
#eval evalScript F O [] [.push [0x80], .push [], .op OP_NUMEQUAL] == some [[1]]
#eval evalScript F O [] [.push [0x80], .op OP_VERIFY] == none
-- 8. 4-byte numbers for arithmetic, 5-byte for the lock-time opcodes
#eval evalScript F O [] [.push [0,0,0,0,1], .op OP_1, .op OP_ADD] == none
#eval evalScript F O [] [.push [0,0,0,0,1], .op OP_CHECKLOCKTIMEVERIFY] == some [[0,0,0,0,1]]
#eval evalScript F O [] [.push [0,0,0,0,0x81], .op OP_CHECKLOCKTIMEVERIFY] == none
#eval evalScript F O [] [.push [0,0,0,0,0,1], .op OP_CHECKLOCKTIMEVERIFY] == none
#eval evalScript ⟨false, false, false⟩ O [] [.push [0,0,0,0,0x81], .op OP_CHECKLOCKTIMEVERIFY] == some [[0,0,0,0,0x81]]   -- flag off: NOP
#eval evalScript F O [] [.push [0,0,0,0x80], .op OP_CHECKSEQUENCEVERIFY] == some [[0,0,0,0x80]]   -- disable flag set: NOP
-- 9. OP_WITHIN boundaries: min inclusive, max exclusive
#eval evalScript F O [] [k 3, .op OP_1, k 3, .op OP_WITHIN] == some [[]]
#eval evalScript F O [] [.op OP_1, .op OP_1, k 3, .op OP_WITHIN] == some [[1]]
-- 10. multisig: keys [5],[9],[13] matched by sigs [7],[11],[15]; 2-of-3 in order, reversed, dummy, counts
#eval evalScript F O [] [.push [], .push [7], .push [11], k 2, .push [5], .push [9], .push [13], k 3, .op OP_CHECKMULTISIG] == some [[1]]
#eval evalScript F O [] [.push [], .push [11], .push [7], k 2, .push [5], .push [9], .push [13], k 3, .op OP_CHECKMULTISIG] == some [[]]
#eval evalScript F O [] [.push [], .push [7], .push [15], k 2, .push [5], .push [9], .push [13], k 3, .op OP_CHECKMULTISIG] == some [[1]]   -- skip the middle key
#eval evalScript F O [] [.push [1], .push [7], .push [11], k 2, .push [5], .push [9], .push [13], k 3, .op OP_CHECKMULTISIG] == none       -- NULLDUMMY on
#eval evalScript F0 O [] [.push [1], .push [7], .push [11], k 2, .push [5], .push [9], .push [13], k 3, .op OP_CHECKMULTISIG] == some [[1]] -- NULLDUMMY off
#eval evalScript F O [] [.push [7], .push [11], k 2, .push [5], .push [9], .push [13], k 3, .op OP_CHECKMULTISIG] == none                  -- no dummy
#eval evalScript F O [] [.push [], .push [7], .push [11], k 3, .push [5], .push [9], k 2, .op OP_CHECKMULTISIG] == none                    -- nSigs > nKeys
#eval evalScript F O [] ([.push []] ++ [.push [21]] ++ List.replicate 21 (Instr.push [5]) ++ [.push [21], .op OP_CHECKMULTISIG]) == none   -- 21 keys
#eval evalScript F O [] (nop 180 ++ [.push [], .push []] ++ List.replicate 20 (Instr.push [5]) ++ [.push [20], .op OP_CHECKMULTISIG]) == some [[1]]  -- count 180+1+20 = 201
#eval evalScript F O [] (nop 181 ++ [.push [], .push []] ++ List.replicate 20 (Instr.push [5]) ++ [.push [20], .op OP_CHECKMULTISIG]) == none        -- 202
#eval evalScript F O [] [.push [], .push [], k 1, .push [5], k 1, .op OP_CHECKMULTISIGVERIFY] == none            -- 1-of-1 with an empty signature fails
#eval evalScript F O [] [.push [], .push [], .push [5], k 1, .op OP_CHECKMULTISIGVERIFY] == some []                -- 0-of-1 succeeds, VERIFY pops the result
