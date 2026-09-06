import Mathlib

/-!
# Real roots of the Eulerian polynomials

The polynomials here use the indexing of arXiv:2608.29224: `eulerianPoly 0 = 1`
and the coefficients of `eulerianPoly n` are the Eulerian numbers in row `n`.
-/

namespace LeanCo.EulerianTP3

open scoped Polynomial
open Polynomial

/-- The ordinary Eulerian polynomial, with `eulerianPoly 0 = 1`. -/
noncomputable def eulerianPoly : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      (1 + C (n + 1 : ℝ) * X) * eulerianPoly n
        + X * (1 - X) * (eulerianPoly n).derivative

@[simp] lemma eulerianPoly_zero : eulerianPoly 0 = 1 := rfl

lemma eulerianPoly_succ (n : ℕ) :
    eulerianPoly (n + 1) =
      (1 + C (n + 1 : ℝ) * X) * eulerianPoly n
        + X * (1 - X) * (eulerianPoly n).derivative := rfl

lemma eulerianPoly_succ_coeff_top (n : ℕ)
    (h : IsMonicOfDegree (eulerianPoly n) n) :
    (eulerianPoly (n + 1)).coeff (n + 1) = 1 := by
  have hp : (eulerianPoly n).coeff n = 1 := by
    simpa [h.natDegree_eq] using h.monic.coeff_natDegree
  have hp_hi : (eulerianPoly n).coeff (n + 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by rw [h.natDegree_eq]; omega)
  rw [eulerianPoly_succ]
  rw [show
      (1 + C (n + 1 : ℝ) * X) * eulerianPoly n
          + X * (1 - X) * (eulerianPoly n).derivative =
        eulerianPoly n + C (n + 1 : ℝ) * (X * eulerianPoly n)
          + X * (eulerianPoly n).derivative
          - X * (X * (eulerianPoly n).derivative) by ring]
  cases n with
  | zero => norm_num [coeff_one]
  | succ m =>
      simp only [Nat.add_assoc, coeff_sub, coeff_add,
        coeff_C_mul, coeff_X_mul, coeff_derivative]
      rw [hp, hp_hi]
      norm_num

lemma eulerianPoly_succ_natDegree_le (n : ℕ)
    (h : IsMonicOfDegree (eulerianPoly n) n) :
    (eulerianPoly (n + 1)).natDegree ≤ n + 1 := by
  by_cases hn : n = 0
  · subst n
    simpa [eulerianPoly_succ, add_comm] using (natDegree_X_add_C (1 : ℝ)).le
  rw [eulerianPoly_succ]
  apply natDegree_add_le_of_degree_le
  · calc
      ((1 + C (n + 1 : ℝ) * X) * eulerianPoly n).natDegree
          ≤ (1 + C (n + 1 : ℝ) * X).natDegree + (eulerianPoly n).natDegree :=
            natDegree_mul_le
      _ ≤ 1 + n := by
        gcongr
        · calc
            (1 + C (n + 1 : ℝ) * X).natDegree
                ≤ max (1 : ℝ[X]).natDegree (C (n + 1 : ℝ) * X).natDegree :=
                  natDegree_add_le _ _
            _ ≤ 1 := by
              apply max_le
              · simp
              · calc
                  (C (n + 1 : ℝ) * X).natDegree
                      ≤ (X : ℝ[X]).natDegree := natDegree_C_mul_le ..
                  _ ≤ 1 := by simp
        · exact h.natDegree_eq.le
      _ = n + 1 := by omega
  · calc
      (X * (1 - X : ℝ[X]) * (eulerianPoly n).derivative).natDegree
          ≤ (X * (1 - X : ℝ[X])).natDegree
              + (eulerianPoly n).derivative.natDegree :=
            natDegree_mul_le
      _ ≤ 2 + (n - 1) := by
        gcongr
        · calc
            (X * (1 - X : ℝ[X])).natDegree
                ≤ X.natDegree + (1 - X : ℝ[X]).natDegree :=
              natDegree_mul_le
            _ ≤ 2 := by
              calc
                X.natDegree + (1 - X : ℝ[X]).natDegree ≤ 1 + 1 :=
                  Nat.add_le_add (by simp) (by simpa using natDegree_sub_le (1 : ℝ[X]) X)
                _ = 2 := rfl
        · simpa [h.natDegree_eq] using (eulerianPoly n).natDegree_derivative_le
      _ ≤ n + 1 := by omega

/-- `eulerianPoly n` is monic and has degree exactly `n`. -/
theorem eulerianPoly_isMonicOfDegree (n : ℕ) :
    IsMonicOfDegree (eulerianPoly n) n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [isMonicOfDegree_iff]
      exact ⟨eulerianPoly_succ_natDegree_le n ih, eulerianPoly_succ_coeff_top n ih⟩

@[simp] theorem eulerianPoly_natDegree (n : ℕ) : (eulerianPoly n).natDegree = n :=
  (eulerianPoly_isMonicOfDegree n).natDegree_eq

theorem eulerianPoly_monic (n : ℕ) : (eulerianPoly n).Monic :=
  (eulerianPoly_isMonicOfDegree n).monic

@[simp] theorem eulerianPoly_eval_zero (n : ℕ) : (eulerianPoly n).eval 0 = 1 := by
  induction n with
  | zero => simp
  | succ n ih => simp [eulerianPoly_succ, ih]

lemma eulerianPoly_eval_succ (n : ℕ) (x : ℝ) :
    (eulerianPoly (n + 1)).eval x =
      (1 + (n + 1 : ℝ) * x) * (eulerianPoly n).eval x
        + x * (1 - x) * (eulerianPoly n).derivative.eval x := by
  simp [eulerianPoly_succ]

/-- A concrete certificate that a polynomial has exactly `n` distinct, strictly negative roots.
The roots are listed from left to right. -/
def HasOrderedNegativeRoots (p : ℝ[X]) (n : ℕ) : Prop :=
  ∃ z : Fin n → ℝ,
    StrictMono z ∧ (∀ i, z i < 0) ∧ p = ∏ i, (X - C (z i))

lemma HasOrderedNegativeRoots.monic {p : ℝ[X]} {n : ℕ}
    (h : HasOrderedNegativeRoots p n) : p.Monic := by
  obtain ⟨z, _, _, rfl⟩ := h
  exact monic_prod_of_monic Finset.univ (fun i ↦ X - C (z i))
    fun _ _ ↦ monic_X_sub_C _

lemma HasOrderedNegativeRoots.isMonicOfDegree {p : ℝ[X]} {n : ℕ}
    (h : HasOrderedNegativeRoots p n) : IsMonicOfDegree p n := by
  obtain ⟨z, _, _, rfl⟩ := h
  let hmon : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      (X - C (z i) : ℝ[X]).Monic := fun i _ ↦ monic_X_sub_C _
  refine ⟨?_, monic_prod_of_monic Finset.univ (fun i ↦ X - C (z i)) hmon⟩
  rw [natDegree_prod_of_monic (s := Finset.univ) (f := fun i ↦ X - C (z i)) hmon]
  simp

lemma HasOrderedNegativeRoots.roots_eq {p : ℝ[X]} {n : ℕ}
    (h : HasOrderedNegativeRoots p n) :
    ∃ z : Fin n → ℝ,
      StrictMono z ∧ (∀ i, z i < 0) ∧
        p.roots = (Finset.univ : Finset (Fin n)).val.map z := by
  obtain ⟨z, hz, hzneg, hp⟩ := h
  refine ⟨z, hz, hzneg, ?_⟩
  rw [hp]
  simpa using roots_prod (fun i : Fin n ↦ (X - C (z i) : ℝ[X])) Finset.univ
    (monic_prod_X_sub_C z Finset.univ |>.ne_zero)

/-- In particular, the root multiset has no repetitions: every root is simple. -/
lemma HasOrderedNegativeRoots.roots_nodup {p : ℝ[X]} {n : ℕ}
    (h : HasOrderedNegativeRoots p n) : p.roots.Nodup := by
  obtain ⟨z, hz, _, hroots⟩ := h.roots_eq
  rw [hroots]
  exact (Finset.univ : Finset (Fin n)).nodup.map hz.injective

lemma HasOrderedNegativeRoots.root_lt_zero {p : ℝ[X]} {n : ℕ}
    (h : HasOrderedNegativeRoots p n) {x : ℝ} (hx : x ∈ p.roots) : x < 0 := by
  obtain ⟨z, _, hzneg, hroots⟩ := h.roots_eq
  rw [hroots] at hx
  obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hx
  exact hzneg i

lemma HasOrderedNegativeRoots.splits {p : ℝ[X]} {n : ℕ}
    (h : HasOrderedNegativeRoots p n) : p.Splits := by
  have hdegree := h.isMonicOfDegree.natDegree_eq
  obtain ⟨z, _, _, hroots⟩ := h.roots_eq
  rw [splits_iff_card_roots, hroots, Multiset.card_map]
  simpa [hdegree]

/-- Convert a monic factorization by negative roots and constant term one into the normalized
positive linear-factor form used in the total-positivity argument. -/
lemma HasOrderedNegativeRoots.exists_positive_linearFactors {p : ℝ[X]} {n : ℕ}
    (h : HasOrderedNegativeRoots p n) (hp0 : p.eval 0 = 1) :
    ∃ r : Fin n → ℝ, (∀ i, 0 < r i) ∧
      p = ∏ i, (1 + C (r i) * X) := by
  obtain ⟨z, hzmono, hzneg, hp⟩ := h
  let r : Fin n → ℝ := fun i ↦ (-z i)⁻¹
  have hzpos (i : Fin n) : 0 < -z i := neg_pos.mpr (hzneg i)
  have hz0 (i : Fin n) : -z i ≠ 0 := (hzpos i).ne'
  have hfactor (i : Fin n) :
      (X - C (z i) : ℝ[X]) = C (-z i) * (1 + C (r i) * X) := by
    dsimp [r]
    rw [mul_add, mul_one, ← mul_assoc, ← C_mul]
    rw [mul_inv_cancel₀ (hz0 i)]
    simp
    ring
  have hscale : ∏ i, (-z i) = 1 := by
    calc
      ∏ i, (-z i) = (∏ i, (X - C (z i) : ℝ[X])).eval 0 := by
        rw [eval_prod]
        simp
      _ = p.eval 0 := by rw [← hp]
      _ = 1 := hp0
  refine ⟨r, fun i ↦ inv_pos.mpr (hzpos i), ?_⟩
  calc
    p = ∏ i, (X - C (z i)) := hp
    _ = ∏ i, (C (-z i) * (1 + C (r i) * X)) := by
      exact Finset.prod_congr rfl fun i _ ↦ hfactor i
    _ = (∏ i, C (-z i)) * ∏ i, (1 + C (r i) * X) :=
      Finset.prod_mul_distrib
    _ = C (∏ i, (-z i)) * ∏ i, (1 + C (r i) * X) := by rw [map_prod]
    _ = ∏ i, (1 + C (r i) * X) := by rw [hscale]; simp

lemma eval_derivative_prod_X_sub_C {n : ℕ} (z : Fin n → ℝ)
    (hz : Function.Injective z) (i : Fin n) :
    (derivative ((Finset.univ : Finset (Fin n)).prod
      (fun j ↦ (X - C (z j) : ℝ[X])))).eval (z i) =
      ((Finset.univ : Finset (Fin n)).erase i).prod (fun j ↦ z i - z j) := by
  classical
  let s : Multiset (Fin n) := (Finset.univ : Finset (Fin n)).val
  have hi : z i ∈ s.map z := Multiset.mem_map.mpr ⟨i, by simp [s], rfl⟩
  have heval := eval_multiset_prod_X_sub_C_derivative hi
  rw [← Multiset.map_erase z hz i s] at heval
  change (derivative (Multiset.map (fun j ↦ (X - C (z j) : ℝ[X]))
      (Finset.univ : Finset (Fin n)).val).prod).eval (z i) =
    (Multiset.map (fun j ↦ z i - z j)
      ((Finset.univ : Finset (Fin n)).erase i).val).prod
  rw [Finset.erase_val]
  change (derivative (Multiset.map (fun j ↦ (X - C (z j) : ℝ[X])) s).prod).eval (z i) =
    (Multiset.map (fun j ↦ z i - z j) (s.erase i)).prod
  simpa only [Multiset.map_map, Function.comp_apply] using heval

/-- The sign of the derivative at the `i`-th root of a monic product alternates with the
number of roots to its right. -/
lemma negOnePow_mul_eval_derivative_prod_pos {n : ℕ} (z : Fin n → ℝ)
    (hz : StrictMono z) (i : Fin n) :
    0 < (-1 : ℝ) ^ (n - 1 - i.1) *
      (derivative ((Finset.univ : Finset (Fin n)).prod
        (fun j ↦ (X - C (z j) : ℝ[X])))).eval (z i) := by
  classical
  rw [eval_derivative_prod_X_sub_C z hz.injective]
  have herase : (Finset.univ : Finset (Fin n)).erase i =
      Finset.Iio i ∪ Finset.Ioi i := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union,
      Finset.mem_Iio, Finset.mem_Ioi]
    exact ne_iff_lt_or_gt
  rw [herase, Finset.prod_union (Finset.disjoint_Ioi_Iio i).symm]
  have hlo : 0 < ∏ j ∈ Finset.Iio i, (z i - z j) := by
    exact Finset.prod_pos fun j hj ↦ sub_pos.mpr (hz (Finset.mem_Iio.mp hj))
  have hhi : 0 < ∏ j ∈ Finset.Ioi i, (z j - z i) := by
    exact Finset.prod_pos fun j hj ↦ sub_pos.mpr (hz (Finset.mem_Ioi.mp hj))
  have hrewrite :
      (∏ j ∈ Finset.Ioi i, (z i - z j)) =
        (-1 : ℝ) ^ (Finset.Ioi i).card * ∏ j ∈ Finset.Ioi i, (z j - z i) := by
    calc
      (∏ j ∈ Finset.Ioi i, (z i - z j)) =
          ∏ j ∈ Finset.Ioi i, -(z j - z i) := by
            apply Finset.prod_congr rfl
            intro j _
            ring
      _ = (-1 : ℝ) ^ (Finset.Ioi i).card * ∏ j ∈ Finset.Ioi i, (z j - z i) :=
        Finset.prod_neg _
  rw [hrewrite, Fin.card_Ioi]
  have hs : 0 < (-1 : ℝ) ^ (n - 1 - i.1) * (-1 : ℝ) ^ (n - 1 - i.1) :=
    mul_self_pos.mpr (pow_ne_zero _ (by norm_num))
  calc
    0 < ((-1 : ℝ) ^ (n - 1 - i.1) * (-1 : ℝ) ^ (n - 1 - i.1)) *
        ((∏ j ∈ Finset.Iio i, (z i - z j)) * ∏ j ∈ Finset.Ioi i, (z j - z i)) :=
      mul_pos hs (mul_pos hlo hhi)
    _ = (-1 : ℝ) ^ (n - 1 - i.1) *
        ((∏ j ∈ Finset.Iio i, (z i - z j)) *
          ((-1 : ℝ) ^ (n - 1 - i.1) * ∏ j ∈ Finset.Ioi i, (z j - z i))) := by
      ring

lemma exists_eval_eq_zero_between (p : ℝ[X]) {a b : ℝ} (hab : a < b)
    (hsign : p.eval a * p.eval b < 0) :
    ∃ x : ℝ, a < x ∧ x < b ∧ p.eval x = 0 := by
  rcases mul_neg_iff.mp hsign with h | h
  · obtain ⟨x, hx, hzero⟩ :=
      intermediate_value_Ioo' hab.le p.continuous.continuousOn ⟨h.2, h.1⟩
    exact ⟨x, hx.1, hx.2, hzero⟩
  · obtain ⟨x, hx, hzero⟩ :=
      intermediate_value_Ioo hab.le p.continuous.continuousOn ⟨h.1, h.2⟩
    exact ⟨x, hx.1, hx.2, hzero⟩

lemma mul_neg_of_alternating_sign {k : ℕ} {a b : ℝ}
    (ha : 0 < (-1 : ℝ) ^ (k + 1) * a)
    (hb : 0 < (-1 : ℝ) ^ k * b) : a * b < 0 := by
  rcases k.even_or_odd with hk | hk
  · rw [pow_succ, hk.neg_one_pow] at ha
    rw [hk.neg_one_pow] at hb
    norm_num at ha hb
    exact mul_neg_of_neg_of_pos ha hb
  · rw [pow_succ, hk.neg_one_pow] at ha
    rw [hk.neg_one_pow] at hb
    norm_num at ha hb
    exact mul_neg_of_pos_of_neg ha hb

/-- A monic polynomial of positive degree has the expected strict sign sufficiently far to
the left.  This packages the only unbounded-endpoint argument needed for interlacing. -/
lemma exists_lt_eval_with_leading_sign {p : ℝ[X]} {n : ℕ}
    (hp : IsMonicOfDegree p n) (hn : 0 < n) (a : ℝ) :
    ∃ x < a, 0 < (-1 : ℝ) ^ n * p.eval x := by
  let g : ℝ[X] := C ((-1 : ℝ) ^ p.natDegree) * p.comp (-X)
  have hgmonic : g.Monic := by
    simpa [g] using hp.monic.neg_one_pow_natDegree_mul_comp_neg_X
  have hgdeg : 0 < g.degree := by
    dsimp [g]
    rw [degree_C_mul (pow_ne_zero _ (by norm_num)), degree_comp_neg_X,
      degree_eq_natDegree hp.monic.ne_zero, hp.natDegree_eq]
    exact_mod_cast hn
  have ht : Filter.Tendsto (fun x : ℝ ↦ g.eval x) Filter.atTop Filter.atTop :=
    g.tendsto_atTop_of_leadingCoeff_nonneg hgdeg (by rw [hgmonic.leadingCoeff]; norm_num)
  have heval : ∀ᶠ x in Filter.atTop, 0 < g.eval x := ht.eventually_gt_atTop 0
  have hbound : ∀ᶠ x : ℝ in Filter.atTop, -a < x := Filter.eventually_gt_atTop (-a)
  obtain ⟨y, hy, hya⟩ := (heval.and hbound).exists
  refine ⟨-y, by linarith, ?_⟩
  simpa [g, hp.natDegree_eq] using hy

/-- The ordinary Eulerian polynomials have a strictly increasing list of distinct negative
roots.  The proof is the classical strict-interlacing induction, including the root to the
left of all old roots. -/
theorem eulerianPoly_hasOrderedNegativeRoots (n : ℕ) :
    HasOrderedNegativeRoots (eulerianPoly n) n := by
  induction n with
  | zero =>
      refine ⟨Fin.elim0, Subsingleton.strictMono _, ?_, ?_⟩
      · exact fun i ↦ Fin.elim0 i
      · simp
  | succ n ih =>
      cases n with
      | zero =>
          let z : Fin 1 → ℝ := fun _ ↦ -1
          refine ⟨z, Subsingleton.strictMono z, ?_, ?_⟩
          · intro i
            simp [z]
          · simp [z, eulerianPoly_succ]
            ring
      | succ m =>
          classical
          obtain ⟨z, hzmono, hzneg, hp⟩ := ih
          have hprod :
              (Finset.univ : Finset (Fin (m + 1))).prod
                  (fun j ↦ (X - C (z j) : ℝ[X])) = eulerianPoly (m + 1) := by
            simpa using hp.symm
          have hpzero (i : Fin (m + 1)) : (eulerianPoly (m + 1)).eval (z i) = 0 := by
            rw [← hprod, eval_prod]
            exact Finset.prod_eq_zero
              (f := fun j ↦ (X - C (z j) : ℝ[X]).eval (z i))
              (s := Finset.univ) (i := i) (by simp) (by simp)
          have hder (i : Fin (m + 1)) :
              0 < (-1 : ℝ) ^ (m + 1 - 1 - i.1) *
                (eulerianPoly (m + 1)).derivative.eval (z i) := by
            have h := negOnePow_mul_eval_derivative_prod_pos z hzmono i
            rw [hprod] at h
            exact h
          have hsign (i : Fin (m + 1)) :
              0 < (-1 : ℝ) ^ (m + 1 - i.1) *
                (eulerianPoly (m + 2)).eval (z i) := by
            have heval := eulerianPoly_eval_succ (m + 1) (z i)
            rw [hpzero i] at heval
            simp only [mul_zero, zero_add] at heval
            have hc : z i * (1 - z i) < 0 :=
              mul_neg_of_neg_of_pos (hzneg i) (by linarith [hzneg i])
            have hk : m + 1 - i.1 = (m + 1 - 1 - i.1) + 1 := by omega
            rw [hk, pow_succ, heval]
            calc
              0 < -(z i * (1 - z i)) *
                  ((-1 : ℝ) ^ (m + 1 - 1 - i.1) *
                    (eulerianPoly (m + 1)).derivative.eval (z i)) :=
                mul_pos (neg_pos.mpr hc) (hder i)
              _ = (-1 : ℝ) ^ (m + 1 - 1 - i.1) * -1 *
                  (z i * (1 - z i) *
                    (eulerianPoly (m + 1)).derivative.eval (z i)) := by ring
          have hmiddle_exists (j : Fin m) :
              ∃ x : ℝ, z j.castSucc < x ∧ x < z j.succ ∧
                (eulerianPoly (m + 2)).eval x = 0 := by
            have h₁ := hsign j.castSucc
            have h₂ := hsign j.succ
            have hk₁ : m + 1 - j.castSucc.1 = (m - j.1) + 1 := by
              simp only [Fin.val_castSucc]
              omega
            have hk₂ : m + 1 - j.succ.1 = m - j.1 := by
              simp only [Fin.val_succ]
              omega
            rw [hk₁] at h₁
            rw [hk₂] at h₂
            exact exists_eval_eq_zero_between _ (hzmono j.castSucc_lt_succ)
              (mul_neg_of_alternating_sign h₁ h₂)
          choose middle hmiddle_lower hmiddle_upper hmiddle_zero using hmiddle_exists
          have hlast_sign :
              (eulerianPoly (m + 2)).eval (z (Fin.last m)) < 0 := by
            have h := hsign (Fin.last m)
            simpa using h
          obtain ⟨lastRoot, hlast_lower, hlast_upper, hlast_zero⟩ :=
            exists_eval_eq_zero_between (eulerianPoly (m + 2))
              (hzneg (Fin.last m)) (by simpa using hlast_sign)
          obtain ⟨L, hL, hLsign⟩ :=
            exists_lt_eval_with_leading_sign (eulerianPoly_isMonicOfDegree (m + 2))
              (by omega) (z 0)
          have hLsign' :
              0 < (-1 : ℝ) ^ ((m + 1) + 1) * (eulerianPoly (m + 2)).eval L := by
            simpa only [Nat.add_assoc] using hLsign
          have hzzero_sign :
              0 < (-1 : ℝ) ^ (m + 1) * (eulerianPoly (m + 2)).eval (z 0) := by
            simpa using hsign (0 : Fin (m + 1))
          obtain ⟨leftRoot, hleft_lower, hleft_upper, hleft_zero⟩ :=
            exists_eval_eq_zero_between (eulerianPoly (m + 2)) hL
              (mul_neg_of_alternating_sign hLsign' hzzero_sign)
          let right : Fin (m + 1) → ℝ := Fin.lastCases lastRoot middle
          have hright_lower (i : Fin (m + 1)) : z i < right i := by
            refine Fin.lastCases ?_ (fun j ↦ ?_) i
            · simpa [right] using hlast_lower
            · simpa [right] using hmiddle_lower j
          have hright_neg (i : Fin (m + 1)) : right i < 0 := by
            refine Fin.lastCases ?_ (fun j ↦ ?_) i
            · simpa [right] using hlast_upper
            · exact (by simpa [right] using (hmiddle_upper j).trans (hzneg j.succ))
          have hright_zero (i : Fin (m + 1)) :
              (eulerianPoly (m + 2)).eval (right i) = 0 := by
            refine Fin.lastCases ?_ (fun j ↦ ?_) i
            · simpa [right] using hlast_zero
            · simpa [right] using hmiddle_zero j
          let w : Fin (m + 2) → ℝ := Fin.cons leftRoot right
          have hwmono : StrictMono w := by
            rw [Fin.strictMono_iff_lt_succ]
            intro i
            refine Fin.cases ?_ (fun j ↦ ?_) i
            · simpa [w] using hleft_upper.trans (hright_lower 0)
            · have hchain : right j.castSucc < right j.succ := by
                calc
                  right j.castSucc = middle j := by simp [right]
                  _ < z j.succ := hmiddle_upper j
                  _ < right j.succ := hright_lower j.succ
              simpa [w] using hchain
          have hwneg (i : Fin (m + 2)) : w i < 0 := by
            refine Fin.cases ?_ (fun j ↦ ?_) i
            · exact (by simpa [w] using hleft_upper.trans (hzneg 0))
            · simpa [w] using hright_neg j
          have hwzero (i : Fin (m + 2)) :
              (eulerianPoly (m + 2)).eval (w i) = 0 := by
            refine Fin.cases ?_ (fun j ↦ ?_) i
            · simpa [w] using hleft_zero
            · simpa [w] using hright_zero j
          let rootProduct : ℝ[X] := ∏ i, (X - C (w i))
          have hrootProduct : HasOrderedNegativeRoots rootProduct (m + 2) := by
            exact ⟨w, hwmono, hwneg, rfl⟩
          have hsubdeg :
              (eulerianPoly (m + 2) - rootProduct).natDegree < m + 2 :=
            (eulerianPoly_isMonicOfDegree (m + 2)).natDegree_sub_lt (by omega)
              hrootProduct.isMonicOfDegree
          have hsubzero : eulerianPoly (m + 2) - rootProduct = 0 := by
            have hrootExplicit :
                (Finset.univ : Finset (Fin (m + 2))).prod
                    (fun j ↦ (X - C (w j) : ℝ[X])) = rootProduct := by
              simpa [rootProduct]
            apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hwmono.injective
            · intro i
              simp only [eval_sub, hwzero i, zero_sub, neg_eq_zero]
              rw [← hrootExplicit, eval_prod]
              exact Finset.prod_eq_zero
                (f := fun j ↦ (X - C (w j) : ℝ[X]).eval (w i))
                (s := Finset.univ) (i := i) (by simp) (by simp)
            · simpa using hsubdeg
          refine ⟨w, hwmono, hwneg, ?_⟩
          exact sub_eq_zero.mp hsubzero

theorem eulerianPoly_roots_nodup (n : ℕ) : (eulerianPoly n).roots.Nodup :=
  (eulerianPoly_hasOrderedNegativeRoots n).roots_nodup

theorem eulerianPoly_splits (n : ℕ) : (eulerianPoly n).Splits :=
  (eulerianPoly_hasOrderedNegativeRoots n).splits

theorem eulerianPoly_root_lt_zero (n : ℕ) {x : ℝ}
    (hx : x ∈ (eulerianPoly n).roots) : x < 0 :=
  (eulerianPoly_hasOrderedNegativeRoots n).root_lt_zero hx

theorem eulerianPoly_isRoot_lt_zero (n : ℕ) {x : ℝ}
    (hx : (eulerianPoly n).IsRoot x) : x < 0 :=
  eulerianPoly_root_lt_zero n ((mem_roots (eulerianPoly_monic n).ne_zero).2 hx)

theorem eulerianPoly_rootMultiplicity_eq_one (n : ℕ) {x : ℝ}
    (hx : (eulerianPoly n).IsRoot x) :
    rootMultiplicity x (eulerianPoly n) = 1 := by
  rw [← count_roots]
  exact Multiset.count_eq_one_of_mem (eulerianPoly_roots_nodup n)
    ((mem_roots (eulerianPoly_monic n).ne_zero).2 hx)

/-- End-to-end normalized factorization into positive linear factors. -/
theorem eulerianPoly_exists_positive_linearFactors (n : ℕ) :
    ∃ r : Fin n → ℝ, (∀ i, 0 < r i) ∧
      eulerianPoly n = ∏ i, (1 + C (r i) * X) :=
  (eulerianPoly_hasOrderedNegativeRoots n).exists_positive_linearFactors
    (eulerianPoly_eval_zero n)

end LeanCo.EulerianTP3
