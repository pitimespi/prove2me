import Definitions.Def_BitcoinUtxo

open BitcoinUtxo

/-! ### The UTXO set as a keyed list -/

theorem BitcoinUtxo.getCoin_cons {T : Type} [DecidableEq T] (k : OutPoint T) (c : Coin) (rest : UtxoSet T) (op : OutPoint T) :
    getCoin ((k, c) :: rest) op = if k = op then some c else getCoin rest op := rfl

theorem BitcoinUtxo.totalValue_cons {T : Type} [DecidableEq T] (k : OutPoint T) (c : Coin) (rest : UtxoSet T) :
    totalValue ((k, c) :: rest) = c.out.value + totalValue rest := rfl

theorem BitcoinUtxo.keysNodup_cons {T : Type} [DecidableEq T] (k : OutPoint T) (c : Coin) (rest : UtxoSet T) :
    keysNodup ((k, c) :: rest) ↔ (∀ e ∈ rest, e.1 ≠ k) ∧ keysNodup rest := by
  unfold keysNodup
  simp only [List.map_cons, List.nodup_cons, List.mem_map]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨fun e he hek => h1 ⟨e, he, hek⟩, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨fun ⟨e, he, hek⟩ => h1 e he hek, h2⟩

theorem BitcoinUtxo.getCoin_none_of_keys {T : Type} [DecidableEq T] (u : UtxoSet T) (op : OutPoint T)
    (h : ∀ e ∈ u, e.1 ≠ op) : getCoin u op = none := by
  induction u with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨k, c⟩ := e
    unfold getCoin
    have hk : ¬ k = op := h (k, c) (List.mem_cons_self ..)
    rw [if_neg hk]
    exact ih (fun e he => h e (List.mem_cons_of_mem _ he))

theorem BitcoinUtxo.getCoin_spend_self {T : Type} [DecidableEq T] (u : UtxoSet T) (op : OutPoint T) :
    getCoin (spendCoin u op) op = none := by
  induction u with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨k, c⟩ := e
    unfold spendCoin
    by_cases hk : k = op
    · rw [if_pos hk]; exact ih
    · rw [if_neg hk]; unfold getCoin; rw [if_neg hk]; exact ih

theorem BitcoinUtxo.getCoin_spend_other {T : Type} [DecidableEq T] (u : UtxoSet T) (op op' : OutPoint T) (h : op' ≠ op) :
    getCoin (spendCoin u op) op' = getCoin u op' := by
  induction u with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨k, c⟩ := e
    unfold spendCoin
    by_cases hk : k = op
    · rw [if_pos hk]
      rw [BitcoinUtxo.getCoin_cons]
      have : ¬ k = op' := fun h' => h (h'.symm.trans hk)
      rw [if_neg this]; exact ih
    · rw [if_neg hk]
      rw [BitcoinUtxo.getCoin_cons, BitcoinUtxo.getCoin_cons]
      by_cases hk' : k = op'
      · rw [if_pos hk', if_pos hk']
      · rw [if_neg hk', if_neg hk']; exact ih

theorem BitcoinUtxo.spendCoin_of_none {T : Type} [DecidableEq T] (u : UtxoSet T) (op : OutPoint T) (h : getCoin u op = none) :
    spendCoin u op = u := by
  induction u with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨k, c⟩ := e
    unfold getCoin at h
    by_cases hk : k = op
    · rw [if_pos hk] at h; simp at h
    · rw [if_neg hk] at h
      unfold spendCoin
      rw [if_neg hk, ih h]

theorem BitcoinUtxo.mem_spendCoin {T : Type} [DecidableEq T] (u : UtxoSet T) (op : OutPoint T) (e : OutPoint T × Coin)
    (h : e ∈ spendCoin u op) : e ∈ u := by
  induction u with
  | nil => simp [spendCoin] at h
  | cons f rest ih =>
    obtain ⟨k, c⟩ := f
    unfold spendCoin at h
    by_cases hk : k = op
    · rw [if_pos hk] at h; exact List.mem_cons_of_mem _ (ih h)
    · rw [if_neg hk] at h
      rcases List.mem_cons.1 h with rfl | hm
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih hm)

theorem BitcoinUtxo.keysNodup_spend {T : Type} [DecidableEq T] (u : UtxoSet T) (op : OutPoint T) (h : keysNodup u) :
    keysNodup (spendCoin u op) := by
  induction u with
  | nil => exact h
  | cons e rest ih =>
    obtain ⟨k, c⟩ := e
    obtain ⟨hkeys, hrest⟩ := (BitcoinUtxo.keysNodup_cons k c rest).1 h
    unfold spendCoin
    by_cases hk : k = op
    · rw [if_pos hk]; exact ih hrest
    · rw [if_neg hk]
      apply (BitcoinUtxo.keysNodup_cons k c _).2
      exact ⟨fun e he => hkeys e (BitcoinUtxo.mem_spendCoin rest op e he), ih hrest⟩

theorem BitcoinUtxo.totalValue_spend {T : Type} [DecidableEq T] (u : UtxoSet T) (op : OutPoint T) (c : Coin)
    (hn : keysNodup u) (h : getCoin u op = some c) :
    totalValue (spendCoin u op) = totalValue u - c.out.value := by
  induction u with
  | nil => simp [getCoin] at h
  | cons e rest ih =>
    obtain ⟨k, c'⟩ := e
    obtain ⟨hkeys, hrest⟩ := (BitcoinUtxo.keysNodup_cons k c' rest).1 hn
    unfold getCoin at h
    unfold spendCoin
    by_cases hk : k = op
    · rw [if_pos hk] at h
      rw [if_pos hk]
      simp only [Option.some.injEq] at h
      subst h
      have hnone : getCoin rest op = none := BitcoinUtxo.getCoin_none_of_keys rest op (fun e he => hk ▸ hkeys e he)
      rw [BitcoinUtxo.spendCoin_of_none rest op hnone, BitcoinUtxo.totalValue_cons]; omega
    · rw [if_neg hk] at h
      rw [if_neg hk, BitcoinUtxo.totalValue_cons, BitcoinUtxo.totalValue_cons]
      have := ih hrest h
      omega

theorem BitcoinUtxo.getCoin_add_other {T : Type} [DecidableEq T] (u : UtxoSet T) (op op' : OutPoint T) (c : Coin) (h : op' ≠ op) :
    getCoin (addCoin u op c) op' = getCoin u op' := by
  unfold addCoin
  split
  · rfl
  · rw [BitcoinUtxo.getCoin_cons, if_neg (Ne.symm h)]
    exact BitcoinUtxo.getCoin_spend_other u op op' h

theorem BitcoinUtxo.keysNodup_add {T : Type} [DecidableEq T] (u : UtxoSet T) (op : OutPoint T) (c : Coin) (h : keysNodup u) :
    keysNodup (addCoin u op c) := by
  unfold addCoin
  split
  · exact h
  · apply (BitcoinUtxo.keysNodup_cons op c _).2
    refine ⟨?_, BitcoinUtxo.keysNodup_spend u op h⟩
    intro e he heq
    have : getCoin (spendCoin u op) op = none := BitcoinUtxo.getCoin_spend_self u op
    -- e is in the spent set with key op, contradicting the lookup
    have hmem : e.1 = op := heq
    have key : ∀ (v : UtxoSet T) (e : OutPoint T × Coin), e ∈ v → getCoin v e.1 ≠ none := by
      intro v e hev
      induction v with
      | nil => simp at hev
      | cons f rest ih =>
        unfold getCoin
        by_cases hf : f.1 = e.1
        · obtain ⟨fk, fc⟩ := f; simp only at hf; rw [if_pos hf]; simp
        · obtain ⟨fk, fc⟩ := f; simp only at hf; rw [if_neg hf]
          rcases List.mem_cons.1 hev with rfl | hm
          · exact absurd rfl hf
          · exact ih hm
    exact key _ e he (hmem ▸ this)

theorem BitcoinUtxo.totalValue_add_fresh {T : Type} [DecidableEq T] (u : UtxoSet T) (op : OutPoint T) (c : Coin)
    (h : getCoin u op = none) :
    totalValue (addCoin u op c) = totalValue u + (if c.out.unspendable then 0 else c.out.value) := by
  unfold addCoin
  split
  · omega
  · rw [BitcoinUtxo.spendCoin_of_none u op h, BitcoinUtxo.totalValue_cons]; omega

theorem BitcoinUtxo.haveCoin_false_iff {T : Type} [DecidableEq T] (u : UtxoSet T) (op : OutPoint T) :
    haveCoin u op = false ↔ getCoin u op = none := by
  unfold haveCoin
  cases getCoin u op <;> simp

theorem BitcoinUtxo.haveCoin_true_iff {T : Type} [DecidableEq T] (u : UtxoSet T) (op : OutPoint T) :
    haveCoin u op = true ↔ ∃ c, getCoin u op = some c := by
  unfold haveCoin
  cases getCoin u op <;> simp

/-! ### Spending the inputs -/

theorem BitcoinUtxo.getCoin_spendInputs_none {T : Type} [DecidableEq T] (u : UtxoSet T) :
    ∀ (ops : List (OutPoint T)) (op : OutPoint T), getCoin u op = none → getCoin (spendInputs u ops) op = none
  | [], op, h => h
  | op' :: rest, op, h => by
    unfold spendInputs
    apply BitcoinUtxo.getCoin_spendInputs_none (spendCoin u op') rest op
    by_cases hop : op = op'
    · subst hop; exact BitcoinUtxo.getCoin_spend_self u op
    · rw [BitcoinUtxo.getCoin_spend_other u op' op hop]; exact h

theorem BitcoinUtxo.keysNodup_spendInputs {T : Type} [DecidableEq T] (u : UtxoSet T) :
    ∀ (ops : List (OutPoint T)), keysNodup u → keysNodup (spendInputs u ops)
  | [], h => h
  | op :: rest, h => by
    unfold spendInputs
    exact BitcoinUtxo.keysNodup_spendInputs (spendCoin u op) rest (BitcoinUtxo.keysNodup_spend u op h)

theorem BitcoinUtxo.valueIn_spend_of_not_mem {T : Type} [DecidableEq T] (u : UtxoSet T) (op : OutPoint T) :
    ∀ (ops : List (OutPoint T)), op ∉ ops → valueIn (spendCoin u op) ops = valueIn u ops
  | [], _ => rfl
  | op' :: rest, h => by
    simp only [List.mem_cons, not_or] at h
    unfold valueIn
    rw [BitcoinUtxo.getCoin_spend_other u op op' (fun e => h.1 e.symm),
      BitcoinUtxo.valueIn_spend_of_not_mem u op rest h.2]

theorem BitcoinUtxo.totalValue_spendInputs {T : Type} [DecidableEq T] (u : UtxoSet T) :
    ∀ (ops : List (OutPoint T)), keysNodup u → ops.Nodup → (∀ op ∈ ops, haveCoin u op = true) →
      totalValue (spendInputs u ops) = totalValue u - valueIn u ops
  | [], _, _, _ => by simp [spendInputs, valueIn]
  | op :: rest, hn, hnd, hall => by
    unfold spendInputs valueIn
    obtain ⟨c, hc⟩ := (BitcoinUtxo.haveCoin_true_iff u op).1 (hall op (List.mem_cons_self ..))
    rw [hc]
    dsimp only
    simp only [List.nodup_cons] at hnd
    have hrest : ∀ op' ∈ rest, haveCoin (spendCoin u op) op' = true := by
      intro op' hop'
      have hne : op' ≠ op := fun h => hnd.1 (h ▸ hop')
      unfold haveCoin
      rw [BitcoinUtxo.getCoin_spend_other u op op' hne]
      exact hall op' (List.mem_cons_of_mem _ hop')
    rw [BitcoinUtxo.totalValue_spendInputs (spendCoin u op) rest (BitcoinUtxo.keysNodup_spend u op hn) hnd.2 hrest,
      BitcoinUtxo.totalValue_spend u op c hn hc, BitcoinUtxo.valueIn_spend_of_not_mem u op rest hnd.1]
    omega

/-! ### The input and output loops -/

theorem BitcoinUtxo.inputsLoop_some {T : Type} [DecidableEq T] (u : UtxoSet T) (h : Nat) :
    ∀ (ops : List (OutPoint T)) (acc v : Int), inputsLoop u h ops acc = some v →
      v = acc + valueIn u ops ∧ ∀ op ∈ ops, haveCoin u op = true
  | [], acc, v, hv => by
    simp only [inputsLoop, Option.some.injEq] at hv
    subst hv; simp [valueIn]
  | op :: rest, acc, v, hv => by
    unfold inputsLoop at hv
    cases hc : getCoin u op with
    | none => rw [hc] at hv; simp at hv
    | some coin =>
      rw [hc] at hv
      simp only [] at hv
      split at hv
      · simp at hv
      · split at hv
        · simp at hv
        · obtain ⟨ih1, ih2⟩ := BitcoinUtxo.inputsLoop_some u h rest _ v hv
          refine ⟨?_, ?_⟩
          · unfold valueIn; rw [hc]; dsimp only; omega
          · intro op' hop'
            rcases List.mem_cons.1 hop' with rfl | hmem
            · unfold haveCoin; rw [hc]; rfl
            · exact ih2 op' hmem

theorem BitcoinUtxo.outputsLoop_some :
    ∀ (outs : List TxOut) (acc v : Int), outputsLoop outs acc = some v →
      v = acc + sumValues outs ∧ ∀ o ∈ outs, 0 ≤ o.value ∧ o.value ≤ MAX_MONEY
  | [], acc, v, hv => by
    simp only [outputsLoop, Option.some.injEq] at hv
    subst hv; simp [sumValues]
  | o :: rest, acc, v, hv => by
    unfold outputsLoop at hv
    split at hv
    · simp at hv
    · split at hv
      · simp at hv
      · split at hv
        · simp at hv
        · obtain ⟨ih1, ih2⟩ := BitcoinUtxo.outputsLoop_some rest _ v hv
          refine ⟨by unfold sumValues; omega, ?_⟩
          intro o' ho'
          rcases List.mem_cons.1 ho' with rfl | hmem
          · constructor <;> omega
          · exact ih2 o' hmem

theorem BitcoinUtxo.checkTransaction_outputs {T : Type} [DecidableEq T] (tx : Tx T) (h : checkTransaction tx = true) :
    tx.vin.Nodup ∧ ∀ o ∈ tx.vout, 0 ≤ o.value ∧ o.value ≤ MAX_MONEY := by
  unfold checkTransaction at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨-, -⟩, hsome⟩, hnd⟩ := h
  refine ⟨hnd, ?_⟩
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hsome
  exact (BitcoinUtxo.outputsLoop_some tx.vout 0 v hv).2

/-- `CheckTxInputs` returns the fee `nValueIn - GetValueOut()`, in `MoneyRange`, with every input
present in the view. -/
theorem BitcoinUtxo.checkTxInputs_some {T : Type} [DecidableEq T] (u : UtxoSet T) (tx : Tx T) (h : Nat) (fee : Int)
    (hfee : checkTxInputs u tx h = some fee) :
    fee = valueIn u tx.vin - valueOut tx ∧ 0 ≤ fee ∧ fee ≤ MAX_MONEY ∧
    ∀ op ∈ tx.vin, haveCoin u op = true := by
  unfold checkTxInputs at hfee
  split at hfee
  · simp at hfee
  · cases hl : inputsLoop u h tx.vin 0 with
    | none => rw [hl] at hfee; simp at hfee
    | some vIn =>
      rw [hl] at hfee
      simp only [] at hfee
      split at hfee
      · simp at hfee
      · split at hfee
        · simp at hfee
        · rename_i hlt hmr
          simp only [Option.some.injEq] at hfee
          subst hfee
          obtain ⟨hv, hall⟩ := BitcoinUtxo.inputsLoop_some u h tx.vin 0 vIn hl
          have hm : moneyRange (vIn - valueOut tx) = true := by
            cases hmr' : moneyRange (vIn - valueOut tx)
            · rw [hmr'] at hmr; simp at hmr
            · rfl
          unfold moneyRange at hm
          simp only [decide_eq_true_eq] at hm
          exact ⟨by omega, hm.1, hm.2, hall⟩

/-! ### Adding the outputs -/

theorem BitcoinUtxo.outpoint_ne_of_ne_n {T : Type} [DecidableEq T] (txid : T) (i j : Nat) (h : j ≠ i) :
    (⟨txid, j⟩ : OutPoint T) ≠ ⟨txid, i⟩ := by
  intro e; cases e; exact h rfl

theorem BitcoinUtxo.getCoin_addCoinsFrom_other {T : Type} [DecidableEq T] (txid : T) (h : Nat) (cb : Bool) :
    ∀ (outs : List TxOut) (u : UtxoSet T) (i : Nat) (op : OutPoint T), op.txid ≠ txid →
      getCoin (addCoinsFrom txid h cb u i outs) op = getCoin u op
  | [], u, i, op, _ => rfl
  | o :: rest, u, i, op, hne => by
    unfold addCoinsFrom
    rw [BitcoinUtxo.getCoin_addCoinsFrom_other txid h cb rest _ (i + 1) op hne]
    apply BitcoinUtxo.getCoin_add_other
    intro e; cases e; exact hne rfl

theorem BitcoinUtxo.keysNodup_addCoinsFrom {T : Type} [DecidableEq T] (txid : T) (h : Nat) (cb : Bool) :
    ∀ (outs : List TxOut) (u : UtxoSet T) (i : Nat), keysNodup u → keysNodup (addCoinsFrom txid h cb u i outs)
  | [], u, i, hn => hn
  | o :: rest, u, i, hn => by
    unfold addCoinsFrom
    exact BitcoinUtxo.keysNodup_addCoinsFrom txid h cb rest _ (i + 1) (BitcoinUtxo.keysNodup_add u _ _ hn)

theorem BitcoinUtxo.totalValue_addCoinsFrom {T : Type} [DecidableEq T] (txid : T) (h : Nat) (cb : Bool) :
    ∀ (outs : List TxOut) (u : UtxoSet T) (i : Nat),
      (∀ j, i ≤ j → j < i + outs.length → getCoin u ⟨txid, j⟩ = none) →
      (∀ o ∈ outs, 0 ≤ o.value) →
      totalValue (addCoinsFrom txid h cb u i outs) ≤ totalValue u + sumValues outs
  | [], u, i, _, _ => by simp [addCoinsFrom, sumValues]
  | o :: rest, u, i, hfresh, hpos => by
    unfold addCoinsFrom
    have hfi : getCoin u ⟨txid, i⟩ = none := hfresh i (Nat.le_refl _) (by simp)
    have hadd := BitcoinUtxo.totalValue_add_fresh u ⟨txid, i⟩ ⟨o, h, cb⟩ hfi
    have hfresh' : ∀ j, i + 1 ≤ j → j < i + 1 + rest.length → getCoin (addCoin u ⟨txid, i⟩ ⟨o, h, cb⟩) ⟨txid, j⟩ = none := by
      intro j hj1 hj2
      rw [BitcoinUtxo.getCoin_add_other u _ _ _ (BitcoinUtxo.outpoint_ne_of_ne_n txid i j (by omega))]
      exact hfresh j (by omega) (by simp; omega)
    have ih := BitcoinUtxo.totalValue_addCoinsFrom txid h cb rest _ (i + 1) hfresh'
      (fun o' ho' => hpos o' (List.mem_cons_of_mem _ ho'))
    have ho : 0 ≤ o.value := hpos o (List.mem_cons_self ..)
    unfold sumValues
    simp only at hadd
    split at hadd <;> omega

/-! ### Updating the view with one transaction -/

theorem BitcoinUtxo.getCoin_updateCoins_other {T : Type} [DecidableEq T] (u : UtxoSet T) (tx : Tx T) (h : Nat) (op : OutPoint T)
    (hne : op.txid ≠ tx.txid) (hnone : getCoin u op = none) :
    getCoin (updateCoins u tx h) op = none := by
  unfold updateCoins
  rw [BitcoinUtxo.getCoin_addCoinsFrom_other tx.txid h tx.isCoinbase tx.vout _ 0 op hne]
  split
  · exact hnone
  · exact BitcoinUtxo.getCoin_spendInputs_none u tx.vin op hnone

theorem BitcoinUtxo.keysNodup_updateCoins {T : Type} [DecidableEq T] (u : UtxoSet T) (tx : Tx T) (h : Nat) (hn : keysNodup u) :
    keysNodup (updateCoins u tx h) := by
  unfold updateCoins
  apply BitcoinUtxo.keysNodup_addCoinsFrom
  split
  · exact hn
  · exact BitcoinUtxo.keysNodup_spendInputs u tx.vin hn

/-- An accepted ordinary transaction removes exactly its fee from the ledger, or more when it
has unspendable outputs: it cannot create value. -/
theorem BitcoinUtxo.tx_conservation {T : Type} [DecidableEq T] (u : UtxoSet T) (tx : Tx T) (h : Nat) (fee : Int)
    (hn : keysNodup u) (hnd : tx.vin.Nodup) (hcb : tx.isCoinbase = false)
    (hfee : checkTxInputs u tx h = some fee)
    (hfresh : ∀ j, j < tx.vout.length → getCoin u ⟨tx.txid, j⟩ = none)
    (hpos : ∀ o ∈ tx.vout, 0 ≤ o.value) :
    totalValue (updateCoins u tx h) ≤ totalValue u - fee := by
  obtain ⟨hfeeq, -, -, hall⟩ := BitcoinUtxo.checkTxInputs_some u tx h fee hfee
  unfold updateCoins
  rw [hcb]
  simp only [Bool.false_eq_true, ite_false]
  have hsp := BitcoinUtxo.totalValue_spendInputs u tx.vin hn hnd hall
  have hfresh' : ∀ j, 0 ≤ j → j < 0 + tx.vout.length → getCoin (spendInputs u tx.vin) ⟨tx.txid, j⟩ = none :=
    fun j _ hj => BitcoinUtxo.getCoin_spendInputs_none u tx.vin _ (hfresh j (by omega))
  have hadd := BitcoinUtxo.totalValue_addCoinsFrom tx.txid h false tx.vout (spendInputs u tx.vin) 0 hfresh' hpos
  unfold valueOut at hfeeq
  omega

/-- A coinbase adds at most its output value to the ledger. -/
theorem BitcoinUtxo.coinbase_bound {T : Type} [DecidableEq T] (u : UtxoSet T) (tx : Tx T) (h : Nat)
    (hcb : tx.isCoinbase = true)
    (hfresh : ∀ j, j < tx.vout.length → getCoin u ⟨tx.txid, j⟩ = none)
    (hpos : ∀ o ∈ tx.vout, 0 ≤ o.value) :
    totalValue (updateCoins u tx h) ≤ totalValue u + valueOut tx := by
  unfold updateCoins
  rw [hcb]
  simp only [ite_true]
  have hfresh' : ∀ j, 0 ≤ j → j < 0 + tx.vout.length → getCoin u ⟨tx.txid, j⟩ = none :=
    fun j _ hj => hfresh j (by omega)
  exact BitcoinUtxo.totalValue_addCoinsFrom tx.txid h true tx.vout u 0 hfresh' hpos

/-! ### Connecting a block -/

/-- Sum of the output values of the coinbase transactions of a list. -/
private def cbOut {T : Type} [DecidableEq T] : List (Tx T) → Int
  | [] => 0
  | tx :: rest => (if tx.isCoinbase then valueOut tx else 0) + cbOut rest

private theorem cbOut_of_no_coinbase {T : Type} [DecidableEq T] : ∀ (txs : List (Tx T)), (∀ tx ∈ txs, tx.isCoinbase = false) → cbOut txs = 0
  | [], _ => rfl
  | tx :: rest, h => by
    unfold cbOut
    rw [h tx (List.mem_cons_self ..)]
    simp only [Bool.false_eq_true, ite_false, Int.zero_add]
    exact cbOut_of_no_coinbase rest (fun tx' h' => h tx' (List.mem_cons_of_mem _ h'))

private theorem connectLoop_bound {T : Type} [DecidableEq T] (h : Nat) :
    ∀ (txs : List (Tx T)) (u : UtxoSet T) (fees : Int) (u' : UtxoSet T) (fees' : Int),
      keysNodup u → (∀ tx ∈ txs, checkTransaction tx = true) →
      (∀ tx ∈ txs, ∀ j, j < tx.vout.length → getCoin u ⟨tx.txid, j⟩ = none) →
      (txs.map Tx.txid).Nodup →
      connectLoop h u fees txs = some (u', fees') →
      totalValue u' + fees' ≤ totalValue u + fees + cbOut txs ∧ keysNodup u'
  | [], u, fees, u', fees', hn, _, _, _, hc => by
    simp only [connectLoop, Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    exact ⟨by unfold cbOut; omega, hn⟩
  | tx :: rest, u, fees, u', fees', hn, hchk, hfresh, hnd, hc => by
    unfold connectLoop at hc
    have hchk_tx := hchk tx (List.mem_cons_self ..)
    obtain ⟨hnd_in, hpos⟩ := BitcoinUtxo.checkTransaction_outputs tx hchk_tx
    have hpos' : ∀ o ∈ tx.vout, 0 ≤ o.value := fun o ho => (hpos o ho).1
    have hfresh_tx := hfresh tx (List.mem_cons_self ..)
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    obtain ⟨hnotin, hnd_rest⟩ := hnd
    have hfresh_rest : ∀ tx' ∈ rest, ∀ j, j < tx'.vout.length →
        getCoin (updateCoins u tx h) ⟨tx'.txid, j⟩ = none := by
      intro tx' htx' j hj
      apply BitcoinUtxo.getCoin_updateCoins_other
      · intro e; exact hnotin ⟨tx', htx', e⟩
      · exact hfresh tx' (List.mem_cons_of_mem _ htx') j hj
    have hn' := BitcoinUtxo.keysNodup_updateCoins u tx h hn
    have hchk_rest : ∀ tx' ∈ rest, checkTransaction tx' = true :=
      fun tx' h' => hchk tx' (List.mem_cons_of_mem _ h')
    split at hc
    · rename_i hcb
      obtain ⟨ih1, ih2⟩ := connectLoop_bound h rest _ fees u' fees' hn' hchk_rest hfresh_rest hnd_rest hc
      have hb := BitcoinUtxo.coinbase_bound u tx h hcb hfresh_tx hpos'
      unfold cbOut; rw [if_pos hcb]
      exact ⟨by omega, ih2⟩
    · rename_i hcb
      have hcb' : tx.isCoinbase = false := by
        cases e : tx.isCoinbase
        · rfl
        · exact absurd e hcb
      cases hf : checkTxInputs u tx h with
      | none => rw [hf] at hc; simp at hc
      | some fee =>
        rw [hf] at hc
        simp only [] at hc
        split at hc
        · simp at hc
        · obtain ⟨ih1, ih2⟩ := connectLoop_bound h rest _ (fees + fee) u' fees' hn' hchk_rest hfresh_rest hnd_rest hc
          have ht := BitcoinUtxo.tx_conservation u tx h fee hn hnd_in hcb' hf hfresh_tx hpos'
          unfold cbOut; rw [if_neg hcb]
          exact ⟨by omega, ih2⟩

/-- Connecting a block raises the ledger's total value by at most the block subsidy, and keeps
the outpoints distinct. -/
theorem BitcoinUtxo.block_bound {T : Type} [DecidableEq T] (subsidy : Nat → Int) (u : UtxoSet T) (h : Nat) (block : List (Tx T))
    (u' : UtxoSet T) (fees : Int) (hn : keysNodup u) (hnd : (block.map Tx.txid).Nodup)
    (hc : connectBlock subsidy u h block = some (u', fees)) :
    totalValue u' ≤ totalValue u + subsidy h ∧ keysNodup u' := by
  unfold connectBlock at hc
  split at hc
  · simp at hc
  rename_i hchk
  split at hc
  · simp at hc
  rename_i hbip
  have hchk' : checkBlockTxs block = true := by
    cases e : checkBlockTxs block
    · rw [e] at hchk; simp at hchk
    · rfl
  have hbip' : bip30Ok u block = true := by
    cases e : bip30Ok u block
    · rw [e] at hbip; simp at hbip
    · rfl
  cases hl : connectLoop h u 0 block with
  | none => rw [hl] at hc; simp at hc
  | some p =>
    obtain ⟨u1, fees1⟩ := p
    rw [hl] at hc
    cases block with
    | nil => simp [checkBlockTxs] at hchk'
    | cons cb rest =>
      simp only [] at hc
      split at hc
      · simp at hc
      rename_i hreward
      simp only [Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      -- structural facts
      unfold checkBlockTxs at hchk'
      simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hchk'
      obtain ⟨⟨hcbcb, hcbchk⟩, hrest⟩ := hchk'
      have hall_chk : ∀ tx ∈ cb :: rest, checkTransaction tx = true := by
        intro tx htx
        rcases List.mem_cons.1 htx with rfl | hm
        · exact hcbchk
        · exact (hrest tx hm).2
      have hno_cb : ∀ tx ∈ rest, tx.isCoinbase = false := fun tx hm => (hrest tx hm).1
      -- BIP30 freshness
      unfold bip30Ok at hbip'
      simp only [List.all_eq_true, List.mem_range, Bool.not_eq_true'] at hbip'
      have hfresh : ∀ tx ∈ cb :: rest, ∀ j, j < tx.vout.length → getCoin u ⟨tx.txid, j⟩ = none :=
        fun tx htx j hj => (BitcoinUtxo.haveCoin_false_iff u _).1 (hbip' tx htx j hj)
      obtain ⟨hb1, hb2⟩ := connectLoop_bound h (cb :: rest) u 0 _ _ hn hall_chk hfresh hnd hl
      have hcb0 : cbOut (cb :: rest) = valueOut cb := by
        unfold cbOut; rw [if_pos hcbcb, cbOut_of_no_coinbase rest hno_cb]; omega
      rw [hcb0] at hb1
      simp only [gt_iff_lt, Int.not_lt] at hreward
      exact ⟨by omega, hb2⟩

/-! ### Connecting a chain -/

theorem BitcoinUtxo.subsidySum_succ_left (s : Nat → Int) :
    ∀ (n h : Nat), subsidySum s h (n + 1) = s h + subsidySum s (h + 1) n
  | 0, h => by simp [subsidySum]
  | n + 1, h => by
    have ih := BitcoinUtxo.subsidySum_succ_left s n h
    unfold subsidySum
    rw [ih]
    have e : h + (n + 1) = h + 1 + n := by omega
    rw [e]
    unfold subsidySum
    omega

theorem BitcoinUtxo.chain_bound {T : Type} [DecidableEq T] (subsidy : Nat → Int) :
    ∀ (blocks : List (List (Tx T))) (u : UtxoSet T) (h : Nat) (u' : UtxoSet T),
      keysNodup u → (∀ b ∈ blocks, (b.map Tx.txid).Nodup) →
      connectChain subsidy u h blocks = some u' →
      totalValue u' ≤ totalValue u + subsidySum subsidy h blocks.length
  | [], u, h, u', _, _, hc => by
    simp only [connectChain, Option.some.injEq] at hc
    subst hc
    simp [subsidySum]
  | b :: rest, u, h, u', hn, hnd, hc => by
    unfold connectChain at hc
    cases hb : connectBlock subsidy u h b with
    | none => rw [hb] at hc; simp at hc
    | some p =>
      obtain ⟨u1, fees⟩ := p
      rw [hb] at hc
      simp only [] at hc
      obtain ⟨h1, hn1⟩ := BitcoinUtxo.block_bound subsidy u h b u1 fees hn (hnd b (List.mem_cons_self ..)) hb
      have ih := BitcoinUtxo.chain_bound subsidy rest u1 (h + 1) u' hn1
        (fun b' hb' => hnd b' (List.mem_cons_of_mem _ hb')) hc
      rw [List.length_cons, BitcoinUtxo.subsidySum_succ_left]
      omega

/-- From an empty ledger, the total value after any sequence of accepted blocks is at most the sum
of their subsidies. -/
theorem BitcoinUtxo.ledger_bound {T : Type} [DecidableEq T] (subsidy : Nat → Int) (blocks : List (List (Tx T))) (h : Nat)
    (u' : UtxoSet T) (hnd : ∀ b ∈ blocks, (b.map Tx.txid).Nodup)
    (hc : connectChain subsidy [] h blocks = some u') :
    totalValue u' ≤ subsidySum subsidy h blocks.length := by
  have := BitcoinUtxo.chain_bound subsidy blocks [] h u' List.nodup_nil hnd hc
  have h0 : totalValue ([] : UtxoSet T) = 0 := rfl
  rw [h0] at this
  omega
