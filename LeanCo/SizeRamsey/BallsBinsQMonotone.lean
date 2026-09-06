import LeanCo.SizeRamsey.PathLowerBound

/-!
# Monotonicity of the balls-and-bins weight in the number of bins

This file proves the second monotonicity assertion from Appendix A.2.  The
coupling deletes one of the `q + 1` bins and independently resamples every
ball which occupied it.  An auxiliary allocation records exactly the
information lost by this operation, giving a genuine finite equivalence and
hence an exact double-counting identity.
-/

namespace LeanCo.SizeRamsey

open Finset

noncomputable section

/-- Delete bin `j`, retaining the old label of a ball outside `j` and using
`r` as its new label when it was in `j`.  The order-preserving labelling of
the remaining bins is supplied by `j.succAbove`. -/
def resampleDeletedBin {q d : ℕ} (j : Fin (q + 1))
    (f : Fin d → Fin (q + 1)) (r : Fin d → Fin q) : Fin d → Fin q :=
  fun x ↦ Fin.succAboveCases j (r x) (fun i ↦ i) (f x)

@[simp] theorem resampleDeletedBin_eq {q d : ℕ} (j : Fin (q + 1))
    (f : Fin d → Fin (q + 1)) (r : Fin d → Fin q) (x : Fin d)
    (h : f x = j) :
    resampleDeletedBin j f r x = r x := by
  subst h
  simp [resampleDeletedBin]

@[simp] theorem resampleDeletedBin_succAbove {q d : ℕ} (j : Fin (q + 1))
    (f : Fin d → Fin (q + 1)) (r : Fin d → Fin q) (x : Fin d)
    (i : Fin q) (h : f x = j.succAbove i) :
    resampleDeletedBin j f r x = i := by
  rw [resampleDeletedBin, h]
  simp

/-- The auxiliary coordinate which makes `resampleDeletedBin` invertible. -/
private def resampleDeletedBinAux {q d : ℕ} (j : Fin (q + 1))
    (f : Fin d → Fin (q + 1)) (r : Fin d → Fin q) :
    Fin d → Fin (q + 1) :=
  fun x ↦ Fin.succAboveCases j j (fun _ ↦ j.succAbove (r x)) (f x)

/-- Per-allocation version of the finite coupling equivalence. -/
private def resampleDeletedBinEquiv (q d : ℕ) (j : Fin (q + 1)) :
    ((Fin d → Fin (q + 1)) × (Fin d → Fin q)) ≃
      ((Fin d → Fin q) × (Fin d → Fin (q + 1))) where
  toFun fr :=
    (resampleDeletedBin j fr.1 fr.2, resampleDeletedBinAux j fr.1 fr.2)
  invFun ga :=
    (fun x ↦ Fin.succAboveCases j j (fun _ ↦ j.succAbove (ga.1 x)) (ga.2 x),
     fun x ↦ Fin.succAboveCases j (ga.1 x) (fun i ↦ i) (ga.2 x))
  left_inv fr := by
    rcases fr with ⟨f, r⟩
    apply Prod.ext
    · funext x
      dsimp [resampleDeletedBin, resampleDeletedBinAux]
      rcases Fin.eq_self_or_eq_succAbove j (f x) with h | ⟨i, h⟩
      · rw [h]
        simp [resampleDeletedBin, resampleDeletedBinAux]
      · rw [h]
        simp [resampleDeletedBin, resampleDeletedBinAux]
    · funext x
      dsimp [resampleDeletedBin, resampleDeletedBinAux]
      rcases Fin.eq_self_or_eq_succAbove j (f x) with h | ⟨i, h⟩
      · rw [h]
        simp [resampleDeletedBin, resampleDeletedBinAux]
      · rw [h]
        simp [resampleDeletedBin, resampleDeletedBinAux]
  right_inv ga := by
    rcases ga with ⟨g, a⟩
    apply Prod.ext
    · funext x
      dsimp [resampleDeletedBin, resampleDeletedBinAux]
      rcases Fin.eq_self_or_eq_succAbove j (a x) with h | ⟨i, h⟩
      · rw [h]
        simp [resampleDeletedBin, resampleDeletedBinAux]
      · rw [h]
        simp [resampleDeletedBin, resampleDeletedBinAux]
    · funext x
      dsimp [resampleDeletedBin, resampleDeletedBinAux]
      rcases Fin.eq_self_or_eq_succAbove j (a x) with h | ⟨i, h⟩
      · rw [h]
        simp [resampleDeletedBin, resampleDeletedBinAux]
      · rw [h]
        simp [resampleDeletedBin, resampleDeletedBinAux]

/-- A bin which was not deleted retains all of its old balls. -/
theorem binLoad_le_resampleDeletedBin {q d : ℕ} (j : Fin (q + 1))
    (f : Fin d → Fin (q + 1)) (r : Fin d → Fin q) (i : Fin q) :
    binLoad f (j.succAbove i) ≤ binLoad (resampleDeletedBin j f r) i := by
  classical
  unfold binLoad
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact resampleDeletedBin_succAbove j f r x i hx

/-- Deleting any bin other than a selected maximizing bin cannot decrease
the maximum load. -/
theorem maxBinLoad_le_resampleDeletedBin_of_ne {q d : ℕ} (hq : 0 < q)
    (f : Fin d → Fin (q + 1)) (r : Fin d → Fin q) (j : Fin (q + 1))
    (hj : j ≠ maximizingBin (Nat.succ_pos q) f) :
    maxBinLoad f ≤ maxBinLoad (resampleDeletedBin j f r) := by
  have himax : maximizingBin (Nat.succ_pos q) f ≠ j := Ne.symm hj
  obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq himax
  calc
    maxBinLoad f = binLoad f (maximizingBin (Nat.succ_pos q) f) :=
      (binLoad_maximizingBin (Nat.succ_pos q) f).symm
    _ = binLoad f (j.succAbove i) := by rw [hi]
    _ ≤ binLoad (resampleDeletedBin j f r) i :=
      binLoad_le_resampleDeletedBin j f r i
    _ ≤ maxBinLoad (resampleDeletedBin j f r) :=
      binLoad_le_maxBinLoad _ _

/-- Of the `q + 1` possible deleted bins, at least `q` preserve a chosen
maximum-load bin. -/
theorem mul_maxBinLoad_le_sum_resampleDeletedBin {q d : ℕ} (hq : 0 < q)
    (f : Fin d → Fin (q + 1)) (r : Fin d → Fin q) :
    q * maxBinLoad f ≤
      ∑ j : Fin (q + 1), maxBinLoad (resampleDeletedBin j f r) := by
  classical
  let i := maximizingBin (Nat.succ_pos q) f
  have hcard :
      ((Finset.univ : Finset (Fin (q + 1))).filter (fun j ↦ j ≠ i)).card = q := by
    rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ i)]
    simp
  calc
    q * maxBinLoad f =
        ∑ j : Fin (q + 1), if j ≠ i then maxBinLoad f else 0 := by
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, hcard, Nat.cast_id, nsmul_eq_mul]
    _ ≤ ∑ j : Fin (q + 1), maxBinLoad (resampleDeletedBin j f r) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : j = i
      · simp [hj]
      · simp only [hj, ne_eq, not_false_eq_true, ↓reduceIte]
        exact maxBinLoad_le_resampleDeletedBin_of_ne hq f r j hj

/-- Exact fibre identity for a fixed deleted bin.  The auxiliary allocation
has `(q + 1)^d` possible values. -/
theorem sum_maxBinLoad_resampleDeletedBin (q d : ℕ) (j : Fin (q + 1)) :
    (∑ f : Fin d → Fin (q + 1), ∑ r : Fin d → Fin q,
        maxBinLoad (resampleDeletedBin j f r)) =
      (q + 1) ^ d * ∑ g : Fin d → Fin q, maxBinLoad g := by
  calc
    (∑ f : Fin d → Fin (q + 1), ∑ r : Fin d → Fin q,
        maxBinLoad (resampleDeletedBin j f r)) =
        ∑ fr : (Fin d → Fin (q + 1)) × (Fin d → Fin q),
          maxBinLoad (resampleDeletedBin j fr.1 fr.2) := by
      rw [Fintype.sum_prod_type]
    _ = ∑ ga : (Fin d → Fin q) × (Fin d → Fin (q + 1)),
          maxBinLoad ga.1 := by
      have h := Equiv.sum_comp (resampleDeletedBinEquiv q d j)
        (fun ga : (Fin d → Fin q) × (Fin d → Fin (q + 1)) ↦
          maxBinLoad ga.1)
      dsimp only [resampleDeletedBinEquiv] at h
      exact h
    _ = (q + 1) ^ d * ∑ g : Fin d → Fin q, maxBinLoad g := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, Nat.cast_id, nsmul_eq_mul]
      rw [Finset.mul_sum]

/-- The integer double-counting inequality before normalizing the two
uniform allocation spaces. -/
theorem mul_pow_mul_sum_maxBinLoad_succ_le {q d : ℕ} (hq : 0 < q) :
    q * q ^ d * (∑ f : Fin d → Fin (q + 1), maxBinLoad f) ≤
      (q + 1) ^ (d + 1) * (∑ g : Fin d → Fin q, maxBinLoad g) := by
  calc
    q * q ^ d * (∑ f : Fin d → Fin (q + 1), maxBinLoad f) =
        ∑ f : Fin d → Fin (q + 1), q * q ^ d * maxBinLoad f := by
      rw [Finset.mul_sum]
    _ = ∑ f : Fin d → Fin (q + 1), ∑ r : Fin d → Fin q,
          q * maxBinLoad f := by
      apply Finset.sum_congr rfl
      intro f _
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, Nat.cast_id, nsmul_eq_mul]
      ring
    _ ≤ ∑ f : Fin d → Fin (q + 1), ∑ r : Fin d → Fin q,
          ∑ j : Fin (q + 1), maxBinLoad (resampleDeletedBin j f r) := by
      apply Finset.sum_le_sum
      intro f _
      apply Finset.sum_le_sum
      intro r _
      exact mul_maxBinLoad_le_sum_resampleDeletedBin hq f r
    _ = ∑ f : Fin d → Fin (q + 1), ∑ j : Fin (q + 1),
          ∑ r : Fin d → Fin q, maxBinLoad (resampleDeletedBin j f r) := by
      apply Finset.sum_congr rfl
      intro f _
      rw [Finset.sum_comm]
    _ = ∑ j : Fin (q + 1), ∑ f : Fin d → Fin (q + 1),
          ∑ r : Fin d → Fin q, maxBinLoad (resampleDeletedBin j f r) := by
      rw [Finset.sum_comm]
    _ = ∑ _j : Fin (q + 1),
          (q + 1) ^ d * (∑ g : Fin d → Fin q, maxBinLoad g) := by
      apply Finset.sum_congr rfl
      intro j _
      exact sum_maxBinLoad_resampleDeletedBin q d j
    _ = (q + 1) ^ (d + 1) *
          (∑ g : Fin d → Fin q, maxBinLoad g) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        Nat.cast_id, nsmul_eq_mul, pow_succ]
      ring

/-- Appendix A.2 in cross-multiplied expectation form.  The assumption
`0 < q` is essential: the uniform allocation space with zero bins is empty
as soon as there is a ball. -/
theorem mul_expectedMaxBinLoad_succ_bins_le {q d : ℕ} (hq : 0 < q) :
    (q : ℝ) * expectedMaxBinLoad (q + 1) d ≤
      (q + 1 : ℕ) * expectedMaxBinLoad q d := by
  have hNat := mul_pow_mul_sum_maxBinLoad_succ_le (d := d) hq
  have hReal :
      (q : ℝ) * (q : ℝ) ^ d *
          (∑ f : Fin d → Fin (q + 1), (maxBinLoad f : ℝ)) ≤
        (((q + 1 : ℕ) : ℝ) ^ (d + 1)) *
          (∑ g : Fin d → Fin q, (maxBinLoad g : ℝ)) := by
    exact_mod_cast hNat
  have hqReal : (0 : ℝ) < q := by exact_mod_cast hq
  have hsuccReal : (0 : ℝ) < (q + 1 : ℕ) := by positivity
  rw [expectedMaxBinLoad, expectedMaxBinLoad]
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  calc
    (q : ℝ) *
        ((∑ f : Fin d → Fin (q + 1), (maxBinLoad f : ℝ)) /
          (((q + 1 : ℕ) : ℝ) ^ d)) =
        ((q : ℝ) *
          ∑ f : Fin d → Fin (q + 1), (maxBinLoad f : ℝ)) /
            (((q + 1 : ℕ) : ℝ) ^ d) := by ring
    _ ≤ (((q + 1 : ℕ) : ℝ) *
          ∑ g : Fin d → Fin q, (maxBinLoad g : ℝ)) /
            (q : ℝ) ^ d := by
      rw [div_le_div_iff₀ (pow_pos hsuccReal d) (pow_pos hqReal d)]
      calc
        ((q : ℝ) *
            ∑ f : Fin d → Fin (q + 1), (maxBinLoad f : ℝ)) *
              (q : ℝ) ^ d =
            (q : ℝ) * (q : ℝ) ^ d *
              ∑ f : Fin d → Fin (q + 1), (maxBinLoad f : ℝ) := by ring
        _ ≤ (((q + 1 : ℕ) : ℝ) ^ (d + 1)) *
              ∑ g : Fin d → Fin q, (maxBinLoad g : ℝ) := hReal
        _ = (((q + 1 : ℕ) : ℝ) *
              ∑ g : Fin d → Fin q, (maxBinLoad g : ℝ)) *
                (q : ℝ) ^ 0 * (((q + 1 : ℕ) : ℝ) ^ d) := by
          rw [pow_succ, pow_zero]
          ring
        _ = (((q + 1 : ℕ) : ℝ) *
              ∑ g : Fin d → Fin q, (maxBinLoad g : ℝ)) *
                (((q + 1 : ℕ) : ℝ) ^ d) := by ring
    _ = ((q + 1 : ℕ) : ℝ) *
        ((∑ g : Fin d → Fin q, (maxBinLoad g : ℝ)) /
          (q : ℝ) ^ d) := by ring

/-! ## The sharp monotonicity coupling -/

/-- The macro-bin of a micro-bin after the first `k` transfers. -/
private def stagedBin (q k : ℕ) (c : Fin (q + 1) × Fin q) : Fin (q + 1) :=
  if c.1 = Fin.last q ∧ c.2.val < k then Fin.last q else c.2.castSucc

/-- Swap the `k` already occupied receiver micro-bins with `k` donor
micro-bins. -/
private def stepSwapLabel {q : ℕ} (k : Fin q)
    (c : Fin (q + 1) × Fin q) : Fin (q + 1) × Fin q :=
  if hR : c.1 = Fin.last q ∧ c.2 < k then
    (c.2.castSucc, k)
  else if hA : c.2 = k ∧ c.1.val < k.val then
    (Fin.last q,
      ⟨c.1.val % q, Nat.mod_lt _ (Nat.zero_lt_of_lt k.isLt)⟩)
  else c

private theorem stepSwapLabel_of_receiver {q : ℕ} (k : Fin q)
    (c : Fin (q + 1) × Fin q) (h : c.1 = Fin.last q ∧ c.2 < k) :
    stepSwapLabel k c = (c.2.castSucc, k) := by
  simp [stepSwapLabel, h]

private theorem stepSwapLabel_of_donor {q : ℕ} (k : Fin q)
    (c : Fin (q + 1) × Fin q) (hR : ¬(c.1 = Fin.last q ∧ c.2 < k))
    (hA : c.2 = k ∧ c.1.val < k.val) :
    stepSwapLabel k c =
      (Fin.last q, ⟨c.1.val % q,
        Nat.mod_lt _ (Nat.zero_lt_of_lt k.isLt)⟩) := by
  simp [stepSwapLabel, hR, hA]

private theorem stepSwapLabel_of_other {q : ℕ} (k : Fin q)
    (c : Fin (q + 1) × Fin q) (hR : ¬(c.1 = Fin.last q ∧ c.2 < k))
    (hA : ¬(c.2 = k ∧ c.1.val < k.val)) :
    stepSwapLabel k c = c := by
  simp [stepSwapLabel, hR, hA]

private theorem stepSwapLabel_involutive {q : ℕ} (k : Fin q) :
    Function.Involutive (stepSwapLabel k) := by
  intro c
  by_cases hR : c.1 = Fin.last q ∧ c.2 < k
  · have hlast : c.2.castSucc ≠ Fin.last q := Fin.ne_last_of_lt c.2.castSucc_lt_last
    have hA' : (k = k) ∧ c.2.castSucc.val < k.val := ⟨rfl, hR.2⟩
    have hnotR' : ¬(c.2.castSucc = Fin.last q ∧ k < k) := fun h ↦ hlast h.1
    rw [stepSwapLabel_of_receiver k c hR,
      stepSwapLabel_of_donor k _ hnotR' hA']
    apply Prod.ext
    · exact hR.1.symm
    · apply Fin.ext
      simp [Nat.mod_eq_of_lt c.2.isLt]
  · by_cases hA : c.2 = k ∧ c.1.val < k.val
    · have hcq : c.1.val < q := lt_trans hA.2 k.isLt
      have hR' : (Fin.last q = Fin.last q) ∧
          (⟨c.1.val % q, Nat.mod_lt _ (Nat.zero_lt_of_lt k.isLt)⟩ : Fin q) < k := by
        constructor
        · rfl
        · show c.1.val % q < k.val
          rw [Nat.mod_eq_of_lt hcq]
          exact hA.2
      rw [stepSwapLabel_of_donor k c hR hA,
        stepSwapLabel_of_receiver k _ hR']
      apply Prod.ext
      · apply Fin.ext
        simp [Nat.mod_eq_of_lt hcq]
      · exact hA.1.symm
    · rw [stepSwapLabel_of_other k c hR hA,
        stepSwapLabel_of_other k c hR hA]

/-- The label swap as a permutation. -/
private def stepSwapEquiv {q : ℕ} (k : Fin q) :
    Equiv.Perm (Fin (q + 1) × Fin q) where
  toFun := stepSwapLabel k
  invFun := stepSwapLabel k
  left_inv := stepSwapLabel_involutive k
  right_inv := stepSwapLabel_involutive k

/-- Apply the label involution to every ball. -/
private def stepSwapAllocation {q d : ℕ} (k : Fin q)
    (h : Fin d → Fin (q + 1) × Fin q) :
    Fin d → Fin (q + 1) × Fin q :=
  fun x ↦ stepSwapLabel k (h x)

private def stagedAllocation {q d : ℕ} (k : ℕ)
    (h : Fin d → Fin (q + 1) × Fin q) : Fin d → Fin (q + 1) :=
  fun x ↦ stagedBin q k (h x)

private def microCount {q d : ℕ}
    (h : Fin d → Fin (q + 1) × Fin q)
    (P : (Fin (q + 1) × Fin q) → Prop) [DecidablePred P] : ℕ :=
  ((Finset.univ : Finset (Fin d)).filter (fun x ↦ P (h x))).card

private theorem microCount_or {q d : ℕ}
    (h : Fin d → Fin (q + 1) × Fin q)
    (P Q : (Fin (q + 1) × Fin q) → Prop)
    [DecidablePred P] [DecidablePred Q]
    (hdisj : ∀ c, P c → ¬ Q c) :
    microCount h (fun c ↦ P c ∨ Q c) =
      microCount h P + microCount h Q := by
  classical
  unfold microCount
  rw [Finset.filter_or, Finset.card_union_of_disjoint]
  exact Finset.disjoint_filter.mpr fun x _ hx ↦ hdisj (h x) hx

private theorem stagedBin_donor_iff {q : ℕ} (k : Fin q)
    (c : Fin (q + 1) × Fin q) :
    stagedBin q k.val c = k.castSucc ↔ c.2 = k := by
  unfold stagedBin
  split_ifs with h
  · constructor
    · intro heq
      exact (Fin.ne_last_of_lt k.castSucc_lt_last heq.symm).elim
    · intro hck
      omega
  · simpa using Fin.castSucc_inj

private theorem stagedBin_succ_donor_iff {q : ℕ} (k : Fin q)
    (c : Fin (q + 1) × Fin q) :
    stagedBin q (k.val + 1) c = k.castSucc ↔
      c.2 = k ∧ c.1 ≠ Fin.last q := by
  unfold stagedBin
  split_ifs with h
  · constructor
    · intro heq
      exact (Fin.ne_last_of_lt k.castSucc_lt_last heq.symm).elim
    · intro hc
      exact (hc.2 h.1).elim
  · constructor
    · intro heq
      have hc2 : c.2 = k := Fin.castSucc_injective q heq
      refine ⟨hc2, ?_⟩
      intro hc1
      apply h
      exact ⟨hc1, by simpa [hc2]⟩
    · intro hc
      exact congrArg Fin.castSucc hc.1

private theorem stagedBin_receiver_iff {q : ℕ} (k : Fin q)
    (c : Fin (q + 1) × Fin q) :
    stagedBin q k.val c = Fin.last q ↔
      c.1 = Fin.last q ∧ c.2 < k := by
  simp only [stagedBin]
  split_ifs with h
  · exact iff_of_true rfl h
  · exact iff_of_false (Fin.ne_last_of_lt c.2.castSucc_lt_last) h

private theorem stagedBin_succ_receiver_iff {q : ℕ} (k : Fin q)
    (c : Fin (q + 1) × Fin q) :
    stagedBin q (k.val + 1) c = Fin.last q ↔
      c.1 = Fin.last q ∧ c.2 ≤ k := by
  simp only [stagedBin]
  split_ifs with h
  · exact iff_of_true rfl ⟨h.1, by omega⟩
  · refine iff_of_false (Fin.ne_last_of_lt c.2.castSucc_lt_last) ?_
    intro hc
    apply h
    exact ⟨hc.1, by omega⟩

private def transferDonor {q : ℕ} (k : Fin q)
    (c : Fin (q + 1) × Fin q) : Prop :=
  c.2 = k ∧ c.1 ≠ Fin.last q

private def transferReceiver {q : ℕ} (k : Fin q)
    (c : Fin (q + 1) × Fin q) : Prop :=
  c.1 = Fin.last q ∧ c.2 < k

private instance instDecidablePredTransferDonor {q : ℕ} (k : Fin q) :
    DecidablePred (transferDonor k) := fun c ↦ by
  unfold transferDonor
  infer_instance

private instance instDecidablePredTransferReceiver {q : ℕ} (k : Fin q) :
    DecidablePred (transferReceiver k) := fun c ↦ by
  unfold transferReceiver
  infer_instance

private theorem transferReceiver_swap_imp_donor {q : ℕ} (k : Fin q)
    (c : Fin (q + 1) × Fin q)
    (hc : transferReceiver k (stepSwapLabel k c)) :
    transferDonor k c := by
  by_cases hR : c.1 = Fin.last q ∧ c.2 < k
  · rw [stepSwapLabel_of_receiver k c hR] at hc
    exact ((Fin.ne_last_of_lt c.2.castSucc_lt_last) hc.1).elim
  · by_cases hA : c.2 = k ∧ c.1.val < k.val
    · refine ⟨hA.1, ?_⟩
      intro heq
      have hk := k.isLt
      have ha := hA.2
      rw [heq] at ha
      simp only [Fin.val_last] at ha
      omega
    · rw [stepSwapLabel_of_other k c hR hA] at hc
      exact (hR hc).elim

private theorem transferReceiver_imp_swap_donor {q : ℕ} (k : Fin q)
    (c : Fin (q + 1) × Fin q) (hc : transferReceiver k c) :
    transferDonor k (stepSwapLabel k c) := by
  rw [stepSwapLabel_of_receiver k c hc]
  exact ⟨rfl, Fin.ne_last_of_lt c.2.castSucc_lt_last⟩

private theorem transfer_union_swap_iff {q : ℕ} (k : Fin q)
    (c : Fin (q + 1) × Fin q) :
    transferDonor k (stepSwapLabel k c) ∨
        transferReceiver k (stepSwapLabel k c) ↔
      transferDonor k c ∨ transferReceiver k c := by
  by_cases hR : c.1 = Fin.last q ∧ c.2 < k
  · rw [stepSwapLabel_of_receiver k c hR]
    simp [transferDonor, transferReceiver, hR,
      Fin.ne_last_of_lt c.2.castSucc_lt_last]
  · by_cases hA : c.2 = k ∧ c.1.val < k.val
    · have hcq : c.1.val < q := lt_trans hA.2 k.isLt
      have hcne : c.1 ≠ Fin.last q := by
        intro heq
        have hk := k.isLt
        have ha := hA.2
        rw [heq] at ha
        simp only [Fin.val_last] at ha
        omega
      rw [stepSwapLabel_of_donor k c hR hA]
      simp [transferDonor, transferReceiver, hA, hcne,
        Nat.mod_eq_of_lt hcq]
      exact hA.2
    · rw [stepSwapLabel_of_other k c hR hA]

private theorem microCount_congr {q d : ℕ}
    (h : Fin d → Fin (q + 1) × Fin q)
    (P Q : (Fin (q + 1) × Fin q) → Prop)
    [DecidablePred P] [DecidablePred Q] (hiff : ∀ c, P c ↔ Q c) :
    microCount h P = microCount h Q := by
  classical
  unfold microCount
  apply congrArg Finset.card
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact hiff (h x)

private theorem binLoad_staged_donor {q d : ℕ} (k : Fin q)
    (h : Fin d → Fin (q + 1) × Fin q) :
    binLoad (stagedAllocation k.val h) k.castSucc =
      microCount h (fun c ↦ c.2 = k) := by
  classical
  unfold binLoad stagedAllocation microCount
  apply congrArg Finset.card
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact stagedBin_donor_iff k (h x)

private theorem binLoad_staged_succ_donor {q d : ℕ} (k : Fin q)
    (h : Fin d → Fin (q + 1) × Fin q) :
    binLoad (stagedAllocation (k.val + 1) h) k.castSucc =
      microCount h (transferDonor k) := by
  classical
  unfold binLoad stagedAllocation microCount transferDonor
  apply congrArg Finset.card
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact stagedBin_succ_donor_iff k (h x)

private theorem binLoad_staged_receiver {q d : ℕ} (k : Fin q)
    (h : Fin d → Fin (q + 1) × Fin q) :
    binLoad (stagedAllocation k.val h) (Fin.last q) =
      microCount h (transferReceiver k) := by
  classical
  unfold binLoad stagedAllocation microCount transferReceiver
  apply congrArg Finset.card
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact stagedBin_receiver_iff k (h x)

private theorem binLoad_staged_succ_receiver {q d : ℕ} (k : Fin q)
    (h : Fin d → Fin (q + 1) × Fin q) :
    binLoad (stagedAllocation (k.val + 1) h) (Fin.last q) =
      microCount h (fun c ↦ c.1 = Fin.last q ∧ c.2 ≤ k) := by
  classical
  unfold binLoad stagedAllocation microCount
  apply congrArg Finset.card
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact stagedBin_succ_receiver_iff k (h x)

private theorem staged_donor_eq_succ_add_special {q d : ℕ} (k : Fin q)
    (h : Fin d → Fin (q + 1) × Fin q) :
    binLoad (stagedAllocation k.val h) k.castSucc =
      binLoad (stagedAllocation (k.val + 1) h) k.castSucc +
        microCount h (fun c ↦ c = (Fin.last q, k)) := by
  rw [binLoad_staged_donor, binLoad_staged_succ_donor]
  calc
    microCount h (fun c ↦ c.2 = k) =
        microCount h (fun c ↦ transferDonor k c ∨
          c = (Fin.last q, k)) := by
      apply microCount_congr
      intro c
      constructor
      · intro hc
        by_cases hlast : c.1 = Fin.last q
        · right
          apply Prod.ext
          · exact hlast
          · exact hc
        · exact Or.inl ⟨hc, hlast⟩
      · rintro (hc | rfl)
        · exact hc.1
        · rfl
    _ = microCount h (transferDonor k) +
          microCount h (fun c ↦ c = (Fin.last q, k)) := by
      apply microCount_or
      intro c hcD hcS
      exact hcD.2 (congrArg Prod.fst hcS)

private theorem staged_succ_receiver_eq_add_special {q d : ℕ} (k : Fin q)
    (h : Fin d → Fin (q + 1) × Fin q) :
    binLoad (stagedAllocation (k.val + 1) h) (Fin.last q) =
      binLoad (stagedAllocation k.val h) (Fin.last q) +
        microCount h (fun c ↦ c = (Fin.last q, k)) := by
  rw [binLoad_staged_succ_receiver, binLoad_staged_receiver]
  calc
    microCount h (fun c ↦ c.1 = Fin.last q ∧ c.2 ≤ k) =
        microCount h (fun c ↦ transferReceiver k c ∨
          c = (Fin.last q, k)) := by
      apply microCount_congr
      intro c
      constructor
      · intro hc
        rcases lt_or_eq_of_le hc.2 with hlt | heq
        · exact Or.inl ⟨hc.1, hlt⟩
        · right
          apply Prod.ext
          · exact hc.1
          · exact heq
      · rintro (hc | rfl)
        · exact ⟨hc.1, hc.2.le⟩
        · exact ⟨rfl, le_rfl⟩
    _ = microCount h (transferReceiver k) +
          microCount h (fun c ↦ c = (Fin.last q, k)) := by
      apply microCount_or
      intro c hcR hcS
      subst c
      exact (lt_irrefl k hcR.2).elim

private theorem stepSwapLabel_special {q : ℕ} (k : Fin q) :
    stepSwapLabel k (Fin.last q, k) = (Fin.last q, k) := by
  apply stepSwapLabel_of_other
  · simp
  · simp

private theorem microCount_special_swap {q d : ℕ} (k : Fin q)
    (h : Fin d → Fin (q + 1) × Fin q) :
    microCount (stepSwapAllocation k h)
        (fun c ↦ c = (Fin.last q, k)) =
      microCount h (fun c ↦ c = (Fin.last q, k)) := by
  unfold microCount stepSwapAllocation
  apply congrArg Finset.card
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  let c := h x
  change stepSwapLabel k c = (Fin.last q, k) ↔ c = (Fin.last q, k)
  constructor
  · intro hc
    calc
      c = stepSwapLabel k (stepSwapLabel k c) :=
        (stepSwapLabel_involutive k c).symm
      _ = stepSwapLabel k (Fin.last q, k) := congrArg (stepSwapLabel k) hc
      _ = (Fin.last q, k) := stepSwapLabel_special k
  · intro hc
    rw [hc]
    exact stepSwapLabel_special k

private theorem transfer_load_sum_swap {q d : ℕ} (k : Fin q)
    (h : Fin d → Fin (q + 1) × Fin q) :
    binLoad (stagedAllocation (k.val + 1) h) k.castSucc +
        binLoad (stagedAllocation k.val h) (Fin.last q) =
      binLoad (stagedAllocation (k.val + 1) (stepSwapAllocation k h))
          k.castSucc +
        binLoad (stagedAllocation k.val (stepSwapAllocation k h))
          (Fin.last q) := by
  rw [binLoad_staged_succ_donor, binLoad_staged_receiver,
    binLoad_staged_succ_donor, binLoad_staged_receiver]
  calc
    microCount h (transferDonor k) + microCount h (transferReceiver k) =
        microCount h (fun c ↦
          transferDonor k c ∨ transferReceiver k c) := by
      symm
      apply microCount_or
      intro c hcD hcR
      exact hcD.2 hcR.1
    _ = microCount h (fun c ↦
          transferDonor k (stepSwapLabel k c) ∨
            transferReceiver k (stepSwapLabel k c)) := by
      apply microCount_congr
      intro c
      exact (transfer_union_swap_iff k c).symm
    _ = microCount (stepSwapAllocation k h) (fun c ↦
          transferDonor k c ∨ transferReceiver k c) := rfl
    _ = microCount (stepSwapAllocation k h) (transferDonor k) +
          microCount (stepSwapAllocation k h) (transferReceiver k) := by
      apply microCount_or
      intro c hcD hcR
      exact hcD.2 hcR.1

private theorem receiver_swap_le_succ_donor {q d : ℕ} (k : Fin q)
    (h : Fin d → Fin (q + 1) × Fin q) :
    binLoad (stagedAllocation k.val (stepSwapAllocation k h)) (Fin.last q) ≤
      binLoad (stagedAllocation (k.val + 1) h) k.castSucc := by
  rw [binLoad_staged_receiver, binLoad_staged_succ_donor]
  unfold microCount stepSwapAllocation
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact transferReceiver_swap_imp_donor k (h x) hx

private theorem receiver_le_succ_donor_swap {q d : ℕ} (k : Fin q)
    (h : Fin d → Fin (q + 1) × Fin q) :
    binLoad (stagedAllocation k.val h) (Fin.last q) ≤
      binLoad (stagedAllocation (k.val + 1) (stepSwapAllocation k h))
        k.castSucc := by
  rw [binLoad_staged_receiver, binLoad_staged_succ_donor]
  unfold microCount stepSwapAllocation
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact transferReceiver_imp_swap_donor k (h x) hx

private theorem stagedBin_succ_other_iff {q : ℕ} (k : Fin q)
    (i : Fin (q + 1)) (hiD : i ≠ k.castSucc) (hiR : i ≠ Fin.last q)
    (c : Fin (q + 1) × Fin q) :
    stagedBin q (k.val + 1) c = i ↔ stagedBin q k.val c = i := by
  by_cases hold : c.1 = Fin.last q ∧ c.2.val < k.val
  · have hnew : c.1 = Fin.last q ∧ c.2.val < k.val + 1 :=
      ⟨hold.1, by omega⟩
    have hsnew : stagedBin q (k.val + 1) c = Fin.last q := by
      unfold stagedBin
      rw [if_pos hnew]
    have hsold : stagedBin q k.val c = Fin.last q := by
      unfold stagedBin
      rw [if_pos hold]
    rw [hsnew, hsold]
  · by_cases hnew : c.1 = Fin.last q ∧ c.2.val < k.val + 1
    · have hc2 : c.2 = k := by
        apply Fin.ext
        omega
      have hsnew : stagedBin q (k.val + 1) c = Fin.last q := by
        unfold stagedBin
        rw [if_pos hnew]
      have hsold : stagedBin q k.val c = k.castSucc := by
        unfold stagedBin
        rw [if_neg hold, hc2]
      rw [hsnew, hsold]
      constructor
      · intro heq
        exact (hiR heq.symm).elim
      · intro heq
        exact (hiD heq.symm).elim
    · have hsnew : stagedBin q (k.val + 1) c = c.2.castSucc := by
        unfold stagedBin
        rw [if_neg hnew]
      have hsold : stagedBin q k.val c = c.2.castSucc := by
        unfold stagedBin
        rw [if_neg hold]
      rw [hsnew, hsold]

private theorem stagedBin_swap_other_iff {q : ℕ} (k : Fin q)
    (i : Fin (q + 1)) (hiD : i ≠ k.castSucc) (hiR : i ≠ Fin.last q)
    (c : Fin (q + 1) × Fin q) :
    stagedBin q k.val (stepSwapLabel k c) = i ↔
      stagedBin q k.val c = i := by
  by_cases hR : c.1 = Fin.last q ∧ c.2 < k
  · rw [stepSwapLabel_of_receiver k c hR]
    rw [(stagedBin_donor_iff k _).2 rfl,
      (stagedBin_receiver_iff k c).2 hR]
    constructor
    · intro heq
      exact (hiD heq.symm).elim
    · intro heq
      exact (hiR heq.symm).elim
  · by_cases hA : c.2 = k ∧ c.1.val < k.val
    · have hcq : c.1.val < q := lt_trans hA.2 k.isLt
      have hcne : c.1 ≠ Fin.last q := by
        intro heq
        have hk := k.isLt
        have ha := hA.2
        rw [heq] at ha
        simp only [Fin.val_last] at ha
        omega
      have hrecv : transferReceiver k
          (Fin.last q, ⟨c.1.val % q,
            Nat.mod_lt _ (Nat.zero_lt_of_lt k.isLt)⟩) := by
        refine ⟨rfl, ?_⟩
        show c.1.val % q < k.val
        rw [Nat.mod_eq_of_lt hcq]
        exact hA.2
      rw [stepSwapLabel_of_donor k c hR hA]
      rw [(stagedBin_receiver_iff k _).2 hrecv,
        (stagedBin_donor_iff k c).2 hA.1]
      constructor
      · intro heq
        exact (hiR heq.symm).elim
      · intro heq
        exact (hiD heq.symm).elim
    · rw [stepSwapLabel_of_other k c hR hA]

private theorem stagedBin_succ_swap_other_iff {q : ℕ} (k : Fin q)
    (i : Fin (q + 1)) (hiD : i ≠ k.castSucc) (hiR : i ≠ Fin.last q)
    (c : Fin (q + 1) × Fin q) :
    stagedBin q (k.val + 1) (stepSwapLabel k c) = i ↔
      stagedBin q (k.val + 1) c = i := by
  rw [stagedBin_succ_other_iff k i hiD hiR,
    stagedBin_swap_other_iff k i hiD hiR,
    stagedBin_succ_other_iff k i hiD hiR]

private theorem binLoad_staged_succ_other {q d : ℕ} (k : Fin q)
    (h : Fin d → Fin (q + 1) × Fin q) (i : Fin (q + 1))
    (hiD : i ≠ k.castSucc) (hiR : i ≠ Fin.last q) :
    binLoad (stagedAllocation (k.val + 1) h) i =
      binLoad (stagedAllocation k.val h) i := by
  unfold binLoad stagedAllocation
  apply congrArg Finset.card
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact stagedBin_succ_other_iff k i hiD hiR (h x)

private theorem binLoad_staged_swap_other {q d : ℕ} (k : Fin q)
    (h : Fin d → Fin (q + 1) × Fin q) (i : Fin (q + 1))
    (hiD : i ≠ k.castSucc) (hiR : i ≠ Fin.last q) :
    binLoad (stagedAllocation k.val (stepSwapAllocation k h)) i =
      binLoad (stagedAllocation k.val h) i := by
  unfold binLoad stagedAllocation stepSwapAllocation
  apply congrArg Finset.card
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact stagedBin_swap_other_iff k i hiD hiR (h x)

private theorem binLoad_staged_succ_swap_other {q d : ℕ} (k : Fin q)
    (h : Fin d → Fin (q + 1) × Fin q) (i : Fin (q + 1))
    (hiD : i ≠ k.castSucc) (hiR : i ≠ Fin.last q) :
    binLoad (stagedAllocation (k.val + 1) (stepSwapAllocation k h)) i =
      binLoad (stagedAllocation (k.val + 1) h) i := by
  unfold binLoad stagedAllocation stepSwapAllocation
  apply congrArg Finset.card
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact stagedBin_succ_swap_other_iff k i hiD hiR (h x)

/-- Maximum load outside two distinguished bins. -/
private def otherMaxBinLoad {q d : ℕ} (f : Fin d → Fin q)
    (i j : Fin q) : ℕ :=
  (((Finset.univ : Finset (Fin q)).erase i).erase j).sup (binLoad f)

private theorem otherMax_staged_succ {q d : ℕ} (k : Fin q)
    (h : Fin d → Fin (q + 1) × Fin q) :
    otherMaxBinLoad (stagedAllocation (k.val + 1) h)
        k.castSucc (Fin.last q) =
      otherMaxBinLoad (stagedAllocation k.val h)
        k.castSucc (Fin.last q) := by
  unfold otherMaxBinLoad
  apply Finset.sup_congr rfl
  intro i hi
  simp only [Finset.mem_erase] at hi
  exact binLoad_staged_succ_other k h i hi.2.1 hi.1

private theorem otherMax_staged_swap {q d : ℕ} (k : Fin q)
    (h : Fin d → Fin (q + 1) × Fin q) :
    otherMaxBinLoad (stagedAllocation k.val (stepSwapAllocation k h))
        k.castSucc (Fin.last q) =
      otherMaxBinLoad (stagedAllocation k.val h)
        k.castSucc (Fin.last q) := by
  unfold otherMaxBinLoad
  apply Finset.sup_congr rfl
  intro i hi
  simp only [Finset.mem_erase] at hi
  exact binLoad_staged_swap_other k h i hi.2.1 hi.1

private theorem otherMax_staged_succ_swap {q d : ℕ} (k : Fin q)
    (h : Fin d → Fin (q + 1) × Fin q) :
    otherMaxBinLoad
        (stagedAllocation (k.val + 1) (stepSwapAllocation k h))
        k.castSucc (Fin.last q) =
      otherMaxBinLoad (stagedAllocation (k.val + 1) h)
        k.castSucc (Fin.last q) := by
  unfold otherMaxBinLoad
  apply Finset.sup_congr rfl
  intro i hi
  simp only [Finset.mem_erase] at hi
  exact binLoad_staged_succ_swap_other k h i hi.2.1 hi.1

private theorem maxBinLoad_eq_max_other {q d : ℕ} (f : Fin d → Fin q)
    (i j : Fin q) (hij : i ≠ j) :
    maxBinLoad f =
      max (otherMaxBinLoad f i j) (max (binLoad f i) (binLoad f j)) := by
  apply le_antisymm
  · unfold maxBinLoad
    apply Finset.sup_le
    intro x _
    by_cases hxi : x = i
    · subst hxi
      exact le_max_of_le_right (le_max_left _ _)
    · by_cases hxj : x = j
      · subst hxj
        exact le_max_of_le_right (le_max_right _ _)
      · apply le_max_of_le_left
        apply Finset.le_sup (f := binLoad f)
        simp [hxi, hxj]
  · apply max_le
    · unfold otherMaxBinLoad maxBinLoad
      apply Finset.sup_le
      intro x _
      exact Finset.le_sup (f := binLoad f) (Finset.mem_univ x)
    · apply max_le <;> exact binLoad_le_maxBinLoad f _

/-- The numerical four-term inequality behind one micro-bin transfer. -/
private theorem max_transfer_pair_le
    {u v u' v' x z : ℕ} (hsum : u + v = u' + v')
    (hu : v' ≤ u) (hu' : v ≤ u') :
    max z (max u (v + x)) + max z (max u' (v' + x)) ≤
      max z (max (u + x) v) + max z (max (u' + x) v') := by
  omega

/-- Pairwise inequality for an allocation and its label-swapped mate. -/
private theorem maxBinLoad_transfer_pair_le {q d : ℕ} (k : Fin q)
    (h : Fin d → Fin (q + 1) × Fin q) :
    maxBinLoad (stagedAllocation (k.val + 1) h) +
        maxBinLoad
          (stagedAllocation (k.val + 1) (stepSwapAllocation k h)) ≤
      maxBinLoad (stagedAllocation k.val h) +
        maxBinLoad (stagedAllocation k.val (stepSwapAllocation k h)) := by
  have hij : k.castSucc ≠ Fin.last q :=
    Fin.ne_last_of_lt k.castSucc_lt_last
  rw [maxBinLoad_eq_max_other
      (stagedAllocation (k.val + 1) h) k.castSucc (Fin.last q) hij,
    maxBinLoad_eq_max_other
      (stagedAllocation (k.val + 1) (stepSwapAllocation k h))
        k.castSucc (Fin.last q) hij,
    maxBinLoad_eq_max_other
      (stagedAllocation k.val h) k.castSucc (Fin.last q) hij,
    maxBinLoad_eq_max_other
      (stagedAllocation k.val (stepSwapAllocation k h))
        k.castSucc (Fin.last q) hij]
  rw [otherMax_staged_succ k h,
    otherMax_staged_succ_swap k h,
    otherMax_staged_succ k h,
    otherMax_staged_swap k h]
  rw [staged_succ_receiver_eq_add_special k h,
    staged_succ_receiver_eq_add_special k (stepSwapAllocation k h),
    microCount_special_swap k h,
    staged_donor_eq_succ_add_special k h,
    staged_donor_eq_succ_add_special k (stepSwapAllocation k h),
    microCount_special_swap k h]
  apply max_transfer_pair_le
  · exact transfer_load_sum_swap k h
  · exact receiver_swap_le_succ_donor k h
  · exact receiver_le_succ_donor_swap k h

private def stepSwapAllocationEquiv {q d : ℕ} (k : Fin q) :
    Equiv.Perm (Fin d → Fin (q + 1) × Fin q) where
  toFun := stepSwapAllocation k
  invFun := stepSwapAllocation k
  left_inv h := by
    funext x
    exact stepSwapLabel_involutive k (h x)
  right_inv h := by
    funext x
    exact stepSwapLabel_involutive k (h x)

private def stagedMaxSum (q d k : ℕ) : ℕ :=
  ∑ h : Fin d → Fin (q + 1) × Fin q,
    maxBinLoad (stagedAllocation k h)

/-- One transfer weakly decreases the total maximum load. -/
private theorem stagedMaxSum_succ_le {q d : ℕ} (k : Fin q) :
    stagedMaxSum q d (k.val + 1) ≤ stagedMaxSum q d k.val := by
  have hpair :
      (∑ h : Fin d → Fin (q + 1) × Fin q,
          (maxBinLoad (stagedAllocation (k.val + 1) h) +
            maxBinLoad (stagedAllocation (k.val + 1)
              (stepSwapAllocation k h)))) ≤
        ∑ h : Fin d → Fin (q + 1) × Fin q,
          (maxBinLoad (stagedAllocation k.val h) +
            maxBinLoad (stagedAllocation k.val
              (stepSwapAllocation k h))) := by
    apply Finset.sum_le_sum
    intro h _
    exact maxBinLoad_transfer_pair_le k h
  have hnew := Equiv.sum_comp (stepSwapAllocationEquiv (d := d) k)
    (fun h : Fin d → Fin (q + 1) × Fin q ↦
      maxBinLoad (stagedAllocation (k.val + 1) h))
  have hold := Equiv.sum_comp (stepSwapAllocationEquiv (d := d) k)
    (fun h : Fin d → Fin (q + 1) × Fin q ↦
      maxBinLoad (stagedAllocation k.val h))
  change (∑ h : Fin d → Fin (q + 1) × Fin q,
      maxBinLoad (stagedAllocation (k.val + 1) (stepSwapAllocation k h))) =
        ∑ h : Fin d → Fin (q + 1) × Fin q,
          maxBinLoad (stagedAllocation (k.val + 1) h) at hnew
  change (∑ h : Fin d → Fin (q + 1) × Fin q,
      maxBinLoad (stagedAllocation k.val (stepSwapAllocation k h))) =
        ∑ h : Fin d → Fin (q + 1) × Fin q,
          maxBinLoad (stagedAllocation k.val h) at hold
  unfold stagedMaxSum
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hnew, hold] at hpair
  omega

private theorem stagedMaxSum_last_le_zero {q d : ℕ} :
    stagedMaxSum q d q ≤ stagedMaxSum q d 0 := by
  have hprefix : ∀ k, k ≤ q → stagedMaxSum q d k ≤ stagedMaxSum q d 0 := by
    intro k hk
    induction k with
    | zero => exact le_rfl
    | succ k ih =>
        have hklt : k < q := Nat.lt_of_succ_le hk
        exact (stagedMaxSum_succ_le (⟨k, hklt⟩ : Fin q)).trans
          (ih (Nat.le_of_succ_le hk))
  exact hprefix q le_rfl

private def castSuccAllocation {q d : ℕ} (g : Fin d → Fin q) :
    Fin d → Fin (q + 1) := fun x ↦ (g x).castSucc

private theorem binLoad_castSuccAllocation {q d : ℕ} (g : Fin d → Fin q)
    (i : Fin q) :
    binLoad (castSuccAllocation g) i.castSucc = binLoad g i := by
  classical
  unfold binLoad castSuccAllocation
  apply congrArg Finset.card
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.castSucc_inj]

private theorem binLoad_castSuccAllocation_last {q d : ℕ}
    (g : Fin d → Fin q) :
    binLoad (castSuccAllocation g) (Fin.last q) = 0 := by
  classical
  simp [binLoad, castSuccAllocation, Fin.ne_last_of_lt]

private theorem maxBinLoad_castSuccAllocation {q d : ℕ}
    (g : Fin d → Fin q) :
    maxBinLoad (castSuccAllocation g) = maxBinLoad g := by
  apply le_antisymm
  · unfold maxBinLoad
    apply Finset.sup_le
    intro i _
    induction i using Fin.lastCases with
    | last =>
        rw [binLoad_castSuccAllocation_last]
        exact Nat.zero_le _
    | cast i =>
        rw [binLoad_castSuccAllocation]
        exact Finset.le_sup (f := binLoad g) (Finset.mem_univ i)
  · unfold maxBinLoad
    apply Finset.sup_le
    intro i _
    rw [← binLoad_castSuccAllocation]
    exact Finset.le_sup (f := binLoad (castSuccAllocation g))
      (Finset.mem_univ i.castSucc)

private def initialMicroAllocationEquiv (q d : ℕ) :
    (Fin d → Fin (q + 1) × Fin q) ≃
      (Fin d → Fin q) × (Fin d → Fin (q + 1)) where
  toFun h := (fun x ↦ (h x).2, fun x ↦ (h x).1)
  invFun ga := fun x ↦ (ga.2 x, ga.1 x)
  left_inv h := by
    funext x
    exact Prod.eta (h x)
  right_inv ga := by
    apply Prod.ext <;> rfl

private theorem stagedAllocation_zero (q d : ℕ)
    (h : Fin d → Fin (q + 1) × Fin q) :
    stagedAllocation 0 h =
      castSuccAllocation (initialMicroAllocationEquiv q d h).1 := by
  funext x
  simp [stagedAllocation, stagedBin, castSuccAllocation,
    initialMicroAllocationEquiv]

private theorem stagedMaxSum_zero (q d : ℕ) :
    stagedMaxSum q d 0 =
      (q + 1) ^ d * ∑ g : Fin d → Fin q, maxBinLoad g := by
  unfold stagedMaxSum
  rw [← Equiv.sum_comp (initialMicroAllocationEquiv q d).symm
    (fun h : Fin d → Fin (q + 1) × Fin q ↦
      maxBinLoad (stagedAllocation 0 h))]
  rw [Fintype.sum_prod_type]
  calc
    (∑ g : Fin d → Fin q, ∑ a : Fin d → Fin (q + 1),
        maxBinLoad (stagedAllocation 0
          ((initialMicroAllocationEquiv q d).symm (g, a)))) =
        ∑ g : Fin d → Fin q, ∑ _a : Fin d → Fin (q + 1),
          maxBinLoad g := by
      apply Finset.sum_congr rfl
      intro g _
      apply Finset.sum_congr rfl
      intro a _
      rw [stagedAllocation_zero, maxBinLoad_castSuccAllocation]
      rfl
    _ = (q + 1) ^ d * ∑ g : Fin d → Fin q, maxBinLoad g := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, Nat.cast_id, nsmul_eq_mul]
      rw [Finset.mul_sum]

/-- At the final stage, use the first coordinate unless it is the last
micro-label; this gives `q` micro-labels over every macro-bin. -/
private def finalMicroLabelEquiv (q : ℕ) :
    (Fin (q + 1) × Fin q) ≃ (Fin (q + 1) × Fin q) where
  toFun c := Fin.lastCases (Fin.last q, c.2)
    (fun a ↦ (c.2.castSucc, a)) c.1
  invFun cr := Fin.lastCases (Fin.last q, cr.2)
    (fun b ↦ (cr.2.castSucc, b)) cr.1
  left_inv c := by
    rcases c with ⟨a, b⟩
    induction a using Fin.lastCases with
    | last => simp
    | cast a => simp
  right_inv cr := by
    rcases cr with ⟨c, r⟩
    induction c using Fin.lastCases with
    | last => simp
    | cast c => simp

private theorem stagedBin_last_eq_final_fst (q : ℕ)
    (c : Fin (q + 1) × Fin q) :
    stagedBin q q c = (finalMicroLabelEquiv q c).1 := by
  rcases c with ⟨a, b⟩
  induction a using Fin.lastCases with
  | last => simp [stagedBin, finalMicroLabelEquiv, b.isLt]
  | cast a => simp [stagedBin, finalMicroLabelEquiv,
      Fin.ne_last_of_lt a.castSucc_lt_last]

private def finalMicroAllocationEquiv (q d : ℕ) :
    (Fin d → Fin (q + 1) × Fin q) ≃
      (Fin d → Fin (q + 1)) × (Fin d → Fin q) where
  toFun h :=
    (fun x ↦ (finalMicroLabelEquiv q (h x)).1,
      fun x ↦ (finalMicroLabelEquiv q (h x)).2)
  invFun gr := fun x ↦
    (finalMicroLabelEquiv q).symm (gr.1 x, gr.2 x)
  left_inv h := by
    funext x
    exact (finalMicroLabelEquiv q).symm_apply_apply (h x)
  right_inv gr := by
    apply Prod.ext <;> funext x
    · exact congrArg Prod.fst
        ((finalMicroLabelEquiv q).apply_symm_apply (gr.1 x, gr.2 x))
    · exact congrArg Prod.snd
        ((finalMicroLabelEquiv q).apply_symm_apply (gr.1 x, gr.2 x))

private theorem stagedAllocation_last_of_final_symm (q d : ℕ)
    (g : Fin d → Fin (q + 1)) (r : Fin d → Fin q) :
    stagedAllocation q ((finalMicroAllocationEquiv q d).symm (g, r)) = g := by
  funext x
  rw [stagedAllocation, stagedBin_last_eq_final_fst]
  exact congrArg Prod.fst
    ((finalMicroLabelEquiv q).apply_symm_apply (g x, r x))

private theorem stagedMaxSum_last (q d : ℕ) :
    stagedMaxSum q d q =
      q ^ d * ∑ g : Fin d → Fin (q + 1), maxBinLoad g := by
  unfold stagedMaxSum
  rw [← Equiv.sum_comp (finalMicroAllocationEquiv q d).symm
    (fun h : Fin d → Fin (q + 1) × Fin q ↦
      maxBinLoad (stagedAllocation q h))]
  rw [Fintype.sum_prod_type]
  calc
    (∑ g : Fin d → Fin (q + 1), ∑ r : Fin d → Fin q,
        maxBinLoad (stagedAllocation q
          ((finalMicroAllocationEquiv q d).symm (g, r)))) =
        ∑ g : Fin d → Fin (q + 1), ∑ _r : Fin d → Fin q,
          maxBinLoad g := by
      apply Finset.sum_congr rfl
      intro g _
      apply Finset.sum_congr rfl
      intro r _
      rw [stagedAllocation_last_of_final_symm]
    _ = q ^ d * ∑ g : Fin d → Fin (q + 1), maxBinLoad g := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, Nat.cast_id, nsmul_eq_mul]
      rw [Finset.mul_sum]

/-- Sharp integer form of monotonicity in the number of bins. -/
theorem pow_mul_sum_maxBinLoad_succ_bins_le {q d : ℕ} :
    q ^ d * (∑ f : Fin d → Fin (q + 1), maxBinLoad f) ≤
      (q + 1) ^ d * (∑ g : Fin d → Fin q, maxBinLoad g) := by
  have h := stagedMaxSum_last_le_zero (q := q) (d := d)
  rw [stagedMaxSum_last, stagedMaxSum_zero] at h
  exact h

/-- The expected maximum load is antitone in the positive bin count. -/
theorem expectedMaxBinLoad_succ_bins_le {q d : ℕ} (hq : 0 < q) :
    expectedMaxBinLoad (q + 1) d ≤ expectedMaxBinLoad q d := by
  have hNat := pow_mul_sum_maxBinLoad_succ_bins_le (q := q) (d := d)
  have hReal :
      (q : ℝ) ^ d *
          (∑ f : Fin d → Fin (q + 1), (maxBinLoad f : ℝ)) ≤
        (((q + 1 : ℕ) : ℝ) ^ d) *
          (∑ g : Fin d → Fin q, (maxBinLoad g : ℝ)) := by
    exact_mod_cast hNat
  have hqReal : (0 : ℝ) < q := by exact_mod_cast hq
  have hsuccReal : (0 : ℝ) < (q + 1 : ℕ) := by positivity
  rw [expectedMaxBinLoad, expectedMaxBinLoad]
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  rw [div_le_div_iff₀ (pow_pos hsuccReal d) (pow_pos hqReal d)]
  calc
    (∑ f : Fin d → Fin (q + 1), (maxBinLoad f : ℝ)) *
        (q : ℝ) ^ d =
      (q : ℝ) ^ d *
        ∑ f : Fin d → Fin (q + 1), (maxBinLoad f : ℝ) := by ring
    _ ≤ (((q + 1 : ℕ) : ℝ) ^ d) *
        ∑ g : Fin d → Fin q, (maxBinLoad g : ℝ) := hReal
    _ = (∑ g : Fin d → Fin q, (maxBinLoad g : ℝ)) *
        (((q + 1 : ℕ) : ℝ) ^ d) := by ring

/-- Appendix A.1/A.2, bin-coordinate successor step.  The explicit
positivity assumption excludes the degenerate zero-bin sample space. -/
theorem ballsBinsWeight_antitone_bins {q d : ℕ} (hq : 0 < q) :
    ballsBinsWeight (q + 1) d ≤ ballsBinsWeight q d := by
  unfold ballsBinsWeight
  exact div_le_div_of_nonneg_right
    (expectedMaxBinLoad_succ_bins_le (d := d) hq) (by positivity)

end

end LeanCo.SizeRamsey
