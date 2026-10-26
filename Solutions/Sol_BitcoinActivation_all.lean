import Definitions.Def_BitcoinActivation

open BitcoinActivation

theorem BitcoinActivation.activeAt_mono (dep : BuriedDeployment) (h₁ h₂ : Nat) (h : h₁ ≤ h₂)
    (ha : BitcoinActivation.activeAt h₁ dep = true) : BitcoinActivation.activeAt h₂ dep = true := by
  unfold activeAt at *
  simp only [decide_eq_true_eq] at *
  omega

theorem BitcoinActivation.activeAfter_eq (dep : BuriedDeployment) (prevHeight : Nat) :
    BitcoinActivation.activeAfter prevHeight dep = BitcoinActivation.activeAt (prevHeight + 1) dep := rfl

/-- Soft forks only add script rules: the flag set of a non-exception block is monotone in height. -/
theorem BitcoinActivation.flags_mono (h₁ h₂ : Nat) (h : h₁ ≤ h₂) :
    BitcoinActivation.ScriptFlags.le (BitcoinActivation.blockScriptFlags h₁ .none)
      (BitcoinActivation.blockScriptFlags h₂ .none) := by
  unfold blockScriptFlags exceptionBase baseFlags ScriptFlags.le
  simp only [Bool.false_or]
  refine ⟨fun _ => trivial, fun _ => trivial, fun _ => trivial, ?_, ?_, ?_, ?_⟩ <;>
    exact BitcoinActivation.activeAt_mono _ h₁ h₂ h

/-- Before BIP66 a non-exception block enforces exactly the base flags. -/
theorem BitcoinActivation.flags_before_bip66 (height : Nat) (h : height < 363725) :
    BitcoinActivation.blockScriptFlags height .none = BitcoinActivation.baseFlags := by
  unfold blockScriptFlags exceptionBase baseFlags activeAt deploymentHeight
  simp only [Bool.false_or]
  have h1 : ¬ (363725 ≤ height) := by omega
  have h2 : ¬ (388381 ≤ height) := by omega
  have h3 : ¬ (419328 ≤ height) := by omega
  have h4 : ¬ (481824 ≤ height) := by omega
  simp [h1, h2, h3, h4]

/-- From SegWit activation on, a non-exception block enforces every flag. -/
theorem BitcoinActivation.flags_after_segwit (height : Nat) (h : 481824 ≤ height) :
    BitcoinActivation.blockScriptFlags height .none = ⟨true, true, true, true, true, true, true⟩ := by
  unfold blockScriptFlags exceptionBase baseFlags activeAt deploymentHeight
  have h1 : 363725 ≤ height := by omega
  have h2 : 388381 ≤ height := by omega
  have h3 : 419328 ≤ height := by omega
  simp [h, h1, h2, h3]

/-- The order in which the height-dependent flags switch on: DERSIG, then CLTV, then CSV, then
NULLDUMMY. -/
theorem BitcoinActivation.flags_order (height : Nat) :
    let f := BitcoinActivation.blockScriptFlags height .none
    (f.cltv = true → f.dersig = true) ∧ (f.csv = true → f.cltv = true) ∧
    (f.nulldummy = true → f.csv = true) := by
  intro f
  unfold f blockScriptFlags exceptionBase baseFlags activeAt deploymentHeight
  simp only [Bool.false_or, decide_eq_true_eq]
  omega

/-- The BIP16 exception block (height 170060, before BIP66) enforces no script flags at all. -/
theorem BitcoinActivation.bip16_exception (height : Nat) (h : height < 363725) :
    BitcoinActivation.blockScriptFlags height .bip16Block = BitcoinActivation.noFlags := by
  unfold blockScriptFlags exceptionBase noFlags activeAt deploymentHeight
  have h1 : ¬ (363725 ≤ height) := by omega
  have h2 : ¬ (388381 ≤ height) := by omega
  have h3 : ¬ (419328 ≤ height) := by omega
  have h4 : ¬ (481824 ≤ height) := by omega
  simp [h1, h2, h3, h4]

/-- The Taproot exception block (height 692261, after SegWit) enforces every flag except Taproot. -/
theorem BitcoinActivation.taproot_exception (height : Nat) (h : 481824 ≤ height) :
    BitcoinActivation.blockScriptFlags height .taprootBlock = ⟨true, true, false, true, true, true, true⟩ := by
  unfold blockScriptFlags exceptionBase activeAt deploymentHeight
  have h1 : 363725 ≤ height := by omega
  have h2 : 388381 ≤ height := by omega
  have h3 : 419328 ≤ height := by omega
  simp [h, h1, h2, h3]

/-- An exception never enforces a flag the default would not: exceptions only remove rules. -/
theorem BitcoinActivation.exception_le (height : Nat) (exc : ScriptException) :
    BitcoinActivation.ScriptFlags.le (BitcoinActivation.blockScriptFlags height exc)
      (BitcoinActivation.blockScriptFlags height .none) := by
  cases exc <;>
  · unfold blockScriptFlags exceptionBase baseFlags noFlags ScriptFlags.le
    simp

/-- Sequence locks are verified exactly from the CSV activation height. -/
theorem BitcoinActivation.lockTimeFlags_eq (height : Nat) :
    BitcoinActivation.lockTimeFlags height =
      if 419328 ≤ height then BitcoinActivation.LOCKTIME_VERIFY_SEQUENCE else 0 := by
  unfold lockTimeFlags activeAt deploymentHeight
  simp
