import Solutions.Sol_BitcoinMiniscript_all

/-! Concrete checks of the Miniscript translation against a stub oracle: the signature check accepts
a signature exactly when it equals the key's "expected" byte string (and rejects the empty signature
cleanly), the hashes tag their input with a leading byte, `checkSequence` accepts delays up to 200
and `checkLockTime` lock times up to 2000. Witness stacks are written top first. -/

open BitcoinScript BitcoinMiniscript BitcoinToLocal BitcoinHtlc

def keyA : Bytes := [0x02, 0xaa, 0xaa]
def keyB : Bytes := [0x03, 0xbb, 0xbb]
def keyC : Bytes := [0x02, 0xcc, 0xcc]
def sigFor (pk : Bytes) : Bytes := 0x30 :: pk
def stubH (b : Bytes) : Bytes := 0xa9 :: b.take 3
def stubS (b : Bytes) : Bytes := 0xa8 :: b.take 3
def pre32 : Bytes := List.replicate 32 0x11
def other32 : Bytes := List.replicate 32 0x22

def stubOracle : Oracle where
  ripemd160 := id
  sha1 := id
  sha256 := stubS
  hash160 := stubH
  hash256 := id
  checkSig := fun sig pk => some (decide (sig = sigFor pk))
  checkLockTime := fun n => decide (n ≤ 2000)
  checkSequence := fun n => decide (n ≤ 200)

def flagsOn : Flags := ⟨true, true, true⟩
def flagsNoDummy : Flags := ⟨true, true, false⟩

/-- `pk(key)` is `c:pk_k(key)`. -/
def pk (key : Bytes) : Ms := .wrap_c (.pk_k key)
/-- `pkh(key)` is `c:pk_h(key)`. -/
def pkh (keyHash : Bytes) : Ms := .wrap_c (.pk_h keyHash)

/-! ### `andor(pk(A), older(144), pk(B))` -/

def P1 : Ms := .andor (pk keyA) (.older 144) (pk keyB)

example : typeOf P1 = some .B := by decide
example : compile P1 =
    [.push keyA, .op OP_CHECKSIG, .op OP_NOTIF, .push keyB, .op OP_CHECKSIG, .op OP_ELSE,
     .push [0x90, 0x00], .op OP_CHECKSEQUENCEVERIFY, .op OP_ENDIF] := by
  decide +kernel
-- `144` is not a small number: it is the push `02 90 00`; `10` would be `OP_10`
example : numInstr 144 = .push [0x90, 0x00] ∧ numInstr 10 = .op 0x5a := by decide +kernel
example : opsMax P1 ≤ MAX_OPS_PER_SCRIPT ∧ size P1 = 9 := by decide

-- A's signature: the `older(144)` branch, which leaves the (nonzero) delay on the stack
example : evalScript flagsOn stubOracle [sigFor keyA] (compile P1) = some [[0x90, 0x00]] := by decide +kernel
-- an empty signature for A then B's signature: the `pk(B)` branch
example : evalScript flagsOn stubOracle [[], sigFor keyB] (compile P1) = some [[1]] := by decide +kernel
-- dissatisfaction: empty signatures for A and B
example : evalScript flagsOn stubOracle [[], []] (compile P1) = some [[]] := by decide +kernel
-- the stack below is untouched
example : evalScript flagsOn stubOracle [sigFor keyA, [7], [8]] (compile P1) = some [[0x90, 0x00], [7], [8]] := by decide +kernel
-- the delay check failing: the script fails
def stubOracleLate : Oracle := { stubOracle with checkSequence := fun n => decide (n ≤ 100) }
example : evalScript flagsOn stubOracleLate [sigFor keyA] (compile P1) = none := by decide +kernel
-- with the CSV flag off nothing is checked
example : evalScript ⟨true, false, true⟩ stubOracleLate [sigFor keyA] (compile P1) = some [[0x90, 0x00]] := by decide +kernel
-- a wrong signature for B after an empty one for A: a clean false
example : evalScript flagsOn stubOracle [[], sigFor keyC] (compile P1) = some [[]] := by decide +kernel

/-! ### `or_d(pk(A), and_v(v:pk(B), after(1000)))` -/

def P2 : Ms := .or_d (pk keyA) (.and_v (.wrap_v (pk keyB)) (.after 1000))

example : typeOf P2 = some .B := by decide
example : compile P2 =
    [.push keyA, .op OP_CHECKSIG, .op OP_IFDUP, .op OP_NOTIF, .push keyB, .op OP_CHECKSIG, .op OP_VERIFY,
     .push [0xe8, 0x03], .op OP_CHECKLOCKTIMEVERIFY, .op OP_ENDIF] := by
  decide +kernel
example : evalScript flagsOn stubOracle [sigFor keyA] (compile P2) = some [[1]] := by decide +kernel
example : evalScript flagsOn stubOracle [[], sigFor keyB] (compile P2) = some [[0xe8, 0x03]] := by decide +kernel
-- `and_v` has no dissatisfaction: an empty signature for B fails at `OP_VERIFY`
example : evalScript flagsOn stubOracle [[], []] (compile P2) = none := by decide +kernel
-- lock time not reached: the script fails
def stubOracleEarly : Oracle := { stubOracle with checkLockTime := fun n => decide (n ≤ 500) }
example : evalScript flagsOn stubOracleEarly [[], sigFor keyB] (compile P2) = none := by decide +kernel

/-! ### `and_b`, `or_b` with the `s:` and `a:` wrappers -/

def P3 : Ms := .and_b (pk keyA) (.wrap_s (pk keyB))
def P4 : Ms := .or_b (pk keyA) (.wrap_a (pk keyB))

example : typeOf P3 = some .B ∧ typeOf P4 = some .B := by decide
example : compile P3 = [.push keyA, .op OP_CHECKSIG, .op OP_SWAP, .push keyB, .op OP_CHECKSIG, .op OP_BOOLAND] := by
  decide +kernel
example : evalScript flagsOn stubOracle [sigFor keyA, sigFor keyB] (compile P3) = some [[1]] := by decide +kernel
example : evalScript flagsOn stubOracle [sigFor keyA, []] (compile P3) = some [[]] := by decide +kernel
example : evalScript flagsOn stubOracle [[], sigFor keyB] (compile P3) = some [[]] := by decide +kernel
example : evalScript flagsOn stubOracle [sigFor keyA, []] (compile P4) = some [[1]] := by decide +kernel
example : evalScript flagsOn stubOracle [[], sigFor keyB] (compile P4) = some [[1]] := by decide +kernel
example : evalScript flagsOn stubOracle [[], []] (compile P4) = some [[]] := by decide +kernel
-- `s:` needs an `o` fragment: `s:pkh(…)` consumes two elements and is rejected by the type checker
example : typeOf (.and_b (pk keyA) (.wrap_s (pkh (stubH keyB)))) = none := by decide

/-! ### `pk_h`, hashes, `or_i`, `or_c`, `d:`, `j:`, `n:` -/

def P5 : Ms := .or_i (pkh (stubH keyA)) (.sha256 (stubS pre32))
example : typeOf P5 = some .B := by decide
example : evalScript flagsOn stubOracle [[1], keyA, sigFor keyA] (compile P5) = some [[1]] := by decide +kernel
example : evalScript flagsOn stubOracle [[1], keyA, []] (compile P5) = some [[]] := by decide +kernel
example : evalScript flagsOn stubOracle [[1], keyB, sigFor keyB] (compile P5) = none := by decide +kernel
example : evalScript flagsOn stubOracle [[], pre32] (compile P5) = some [[1]] := by decide +kernel
example : evalScript flagsOn stubOracle [[], other32] (compile P5) = some [[]] := by decide +kernel
example : evalScript flagsOn stubOracle [[], [0x11]] (compile P5) = none := by decide +kernel

-- `or_c(pk(A), v:older(10))` is of type `V`; `t:X` = `and_v(X, 1)` is not in the core, so test the `V` fragment directly
def P6 : Ms := .or_c (pk keyA) (.wrap_v (.older 10))
example : typeOf P6 = some .V := by decide
example : evalScript flagsOn stubOracle [sigFor keyA, [9]] (compile P6) = some [[9]] := by decide +kernel
example : evalScript flagsOn stubOracle [[], [9]] (compile P6) = some [[9]] := by decide +kernel
example : evalScript flagsOn stubOracleLate [[], [9]] (compile P6) = some [[9]] := by decide +kernel  -- 10 ≤ 100
example : evalScript flagsOn { stubOracle with checkSequence := fun _ => false } [[], [9]] (compile P6) = none := by
  decide +kernel

def P7 : Ms := .wrap_d (.wrap_v (.older 144))
example : typeOf P7 = some .B := by decide
example : evalScript flagsOn stubOracle [[1]] (compile P7) = some [[1]] := by decide +kernel
example : evalScript flagsOn stubOracle [[]] (compile P7) = some [[]] := by decide +kernel
example : evalScript flagsOn stubOracleLate [[1]] (compile P7) = none := by decide +kernel

def P8 : Ms := .wrap_j (pk keyA)
example : typeOf P8 = some .B := by decide
example : evalScript flagsOn stubOracle [sigFor keyA] (compile P8) = some [[1]] := by decide +kernel
example : evalScript flagsOn stubOracle [[]] (compile P8) = some [[]] := by decide +kernel
-- `n:older(144)` turns the delay into exactly `1`
def P9 : Ms := .wrap_n (.older 144)
example : evalScript flagsOn stubOracle [] (compile P9) = some [[1]] := by decide +kernel

/-! ### `multi(2, [A, B, C])` -/

def P10 : Ms := .multi 2 [keyA, keyB, keyC]
example : typeOf P10 = some .B := by decide
example : compile P10 =
    [.op 0x52, .push keyA, .push keyB, .push keyC, .op 0x53, .op OP_CHECKMULTISIG] := by decide +kernel
-- signatures in key order from the top: the keys are consumed top down (`C`, `B`, `A`)
example : evalScript flagsOn stubOracle [sigFor keyC, sigFor keyA, []] (compile P10) = some [[1]] := by decide +kernel
example : evalScript flagsOn stubOracle [sigFor keyB, sigFor keyA, []] (compile P10) = some [[1]] := by decide +kernel
-- out of order: false
example : evalScript flagsOn stubOracle [sigFor keyA, sigFor keyC, []] (compile P10) = some [[]] := by decide +kernel
-- dissatisfaction: `0 0 0`
example : evalScript flagsOn stubOracle [[], [], []] (compile P10) = some [[]] := by decide +kernel
-- the dummy under NULLDUMMY
example : evalScript flagsOn stubOracle [sigFor keyC, sigFor keyA, [1]] (compile P10) = none := by decide +kernel
example : evalScript flagsNoDummy stubOracle [sigFor keyC, sigFor keyA, [1]] (compile P10) = some [[1]] := by decide +kernel
example : typeOf (.multi 4 [keyA, keyB, keyC]) = none := by decide

/-! ### The soundness theorem on a concrete policy -/

-- `Sem` for the `older(144)` branch of `P1` with A's signature
theorem semP1 : Sem flagsOn stubOracle P1 [sigFor keyA] [serialize 144] :=
  ⟨[sigFor keyA], [1], ⟨keyA, sigFor keyA, true, ⟨sigFor keyA, rfl, rfl⟩, by decide, rfl⟩,
    Or.inl ⟨rfl, [], rfl, rfl, by decide, rfl⟩⟩

example (rest : List Bytes) (h : rest.length + 10 ≤ MAX_STACK_SIZE) :
    evalScript flagsOn stubOracle (sigFor keyA :: rest) (compile P1) = some (serialize 144 :: rest) :=
  BitcoinMiniscript.sem_sound flagsOn stubOracle P1 .B (BitcoinMiniscript.typeOf_sound P1 .B (by decide)) (by decide)
    [sigFor keyA] [serialize 144] rest semP1 (by decide)
    (by have hs : size P1 = 9 := by decide
        simp only [List.length_singleton, hs]; omega)
