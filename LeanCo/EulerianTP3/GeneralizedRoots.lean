import LeanCo.EulerianTP3.RealRoots

/-!
# Real roots of generalized Eulerian-type polynomials

This file treats the recurrence used in Theorem 4.1.  Positivity of `β` and of every
`alpha n` is sufficient; no real-rootedness hypothesis is assumed.
-/

namespace LeanCo.EulerianTP3

open scoped Polynomial
open Polynomial

/-- The generalized Eulerian-type polynomial with parameters `β` and `alpha`. -/
noncomputable def eulerianTypePoly (β : ℝ) (alpha : ℕ → ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      (1 + C ((n : ℝ) * β + alpha n) * X) * eulerianTypePoly β alpha n
        + C β * X * (1 - X) * (eulerianTypePoly β alpha n).derivative

@[simp] lemma eulerianTypePoly_zero (β : ℝ) (alpha : ℕ → ℝ) :
    eulerianTypePoly β alpha 0 = 1 := rfl

lemma eulerianTypePoly_succ (β : ℝ) (alpha : ℕ → ℝ) (n : ℕ) :
    eulerianTypePoly β alpha (n + 1) =
      (1 + C ((n : ℝ) * β + alpha n) * X) * eulerianTypePoly β alpha n
        + C β * X * (1 - X) * (eulerianTypePoly β alpha n).derivative := rfl

@[simp] theorem eulerianTypePoly_eval_zero (β : ℝ) (alpha : ℕ → ℝ) (n : ℕ) :
    (eulerianTypePoly β alpha n).eval 0 = 1 := by
  induction n with
  | zero => simp
  | succ n ih => simp [eulerianTypePoly_succ, ih]

lemma eulerianTypePoly_eval_succ (β : ℝ) (alpha : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    (eulerianTypePoly β alpha (n + 1)).eval x =
      (1 + ((n : ℝ) * β + alpha n) * x) * (eulerianTypePoly β alpha n).eval x
        + β * x * (1 - x) * (eulerianTypePoly β alpha n).derivative.eval x := by
  simp [eulerianTypePoly_succ]

lemma eulerianTypePoly_succ_natDegree_le (β : ℝ) (alpha : ℕ → ℝ) (n : ℕ)
    (hdegree : (eulerianTypePoly β alpha n).natDegree = n) :
    (eulerianTypePoly β alpha (n + 1)).natDegree ≤ n + 1 := by
  by_cases hn : n = 0
  · subst n
    rw [eulerianTypePoly_succ]
    simp only [Nat.cast_zero, zero_mul, zero_add, eulerianTypePoly_zero, mul_one,
      derivative_one, mul_zero, add_zero]
    calc
      (1 + C (alpha 0) * X).natDegree ≤
          max (1 : ℝ[X]).natDegree (C (alpha 0) * X).natDegree := natDegree_add_le _ _
      _ ≤ 1 := by
        apply max_le
        · simp
        · exact (natDegree_C_mul_le _ X).trans (by simp)
  rw [eulerianTypePoly_succ]
  apply natDegree_add_le_of_degree_le
  · calc
      ((1 + C ((n : ℝ) * β + alpha n) * X) * eulerianTypePoly β alpha n).natDegree
          ≤ (1 + C ((n : ℝ) * β + alpha n) * X).natDegree
              + (eulerianTypePoly β alpha n).natDegree := natDegree_mul_le
      _ ≤ 1 + n := by
        gcongr
        · calc
            (1 + C ((n : ℝ) * β + alpha n) * X).natDegree ≤
                max (1 : ℝ[X]).natDegree
                  (C ((n : ℝ) * β + alpha n) * X).natDegree := natDegree_add_le _ _
            _ ≤ 1 := by
              apply max_le
              · simp
              · exact (natDegree_C_mul_le _ X).trans (by simp)
        · exact hdegree.le
      _ = n + 1 := by omega
  · calc
      (C β * X * (1 - X) * (eulerianTypePoly β alpha n).derivative).natDegree ≤
          (C β * X * (1 - X : ℝ[X])).natDegree
            + (eulerianTypePoly β alpha n).derivative.natDegree := natDegree_mul_le
      _ ≤ 2 + (n - 1) := by
        gcongr
        · calc
            (C β * X * (1 - X : ℝ[X])).natDegree ≤
                (C β * X).natDegree + (1 - X : ℝ[X]).natDegree := natDegree_mul_le
            _ ≤ 2 := by
              calc
                (C β * X).natDegree + (1 - X : ℝ[X]).natDegree ≤ 1 + 1 :=
                  Nat.add_le_add ((natDegree_C_mul_le _ X).trans (by simp))
                    (by simpa using natDegree_sub_le (1 : ℝ[X]) X)
                _ = 2 := rfl
        · simpa [hdegree] using (eulerianTypePoly β alpha n).natDegree_derivative_le
      _ ≤ n + 1 := by omega

/-- Coefficient recurrence away from the constant term. -/
lemma eulerianTypePoly_succ_coeff_succ (β : ℝ) (alpha : ℕ → ℝ) (n k : ℕ) :
    (eulerianTypePoly β alpha (n + 1)).coeff (k + 1) =
      (1 + β * (k + 1 : ℝ)) * (eulerianTypePoly β alpha n).coeff (k + 1)
        + (alpha n + β * (n - k : ℝ)) * (eulerianTypePoly β alpha n).coeff k := by
  rw [eulerianTypePoly_succ]
  rw [show
      (1 + C ((n : ℝ) * β + alpha n) * X) * eulerianTypePoly β alpha n
          + C β * X * (1 - X) * (eulerianTypePoly β alpha n).derivative =
        eulerianTypePoly β alpha n
          + C ((n : ℝ) * β + alpha n) * (X * eulerianTypePoly β alpha n)
          + C β * (X * (eulerianTypePoly β alpha n).derivative)
          - C β * (X * (X * (eulerianTypePoly β alpha n).derivative)) by ring]
  cases k with
  | zero =>
      simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_mul, coeff_derivative]
      norm_num
      ring
  | succ j =>
      simp only [Nat.succ_eq_add_one, Nat.add_assoc, coeff_sub, coeff_add, coeff_C_mul,
        coeff_X_mul, coeff_derivative]
      push_cast
      ring_nf

/-- Degree and strict positivity of every coefficient in the support. -/
theorem eulerianTypePoly_degree_and_coeff_pos {β : ℝ} {alpha : ℕ → ℝ}
    (hβ : 0 < β) (halpha : ∀ n, 0 < alpha n) :
    ∀ n, (eulerianTypePoly β alpha n).natDegree = n ∧
      ∀ k ≤ n, 0 < (eulerianTypePoly β alpha n).coeff k := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hle := eulerianTypePoly_succ_natDegree_le β alpha n ih.1
      have hcoeff : ∀ k ≤ n + 1, 0 < (eulerianTypePoly β alpha (n + 1)).coeff k := by
        intro k hk
        cases k with
        | zero => simpa [coeff_zero_eq_eval_zero] using eulerianTypePoly_eval_zero β alpha (n + 1)
        | succ k =>
            rw [eulerianTypePoly_succ_coeff_succ]
            have hk' : k ≤ n := by omega
            have hpk : 0 < (eulerianTypePoly β alpha n).coeff k := ih.2 k hk'
            have hsecond : 0 <
                (alpha n + β * (n - k : ℝ)) * (eulerianTypePoly β alpha n).coeff k := by
              apply mul_pos
              · exact add_pos_of_pos_of_nonneg (halpha n)
                  (mul_nonneg hβ.le (sub_nonneg.mpr (by exact_mod_cast hk')))
              · exact hpk
            have hfirst : 0 ≤
                (1 + β * (k + 1 : ℝ)) * (eulerianTypePoly β alpha n).coeff (k + 1) := by
              apply mul_nonneg
              · positivity
              · by_cases hkn : k < n
                · exact (ih.2 (k + 1) (by omega)).le
                · have hEq : k = n := by omega
                  rw [hEq, coeff_eq_zero_of_natDegree_lt (by rw [ih.1]; omega)]
            exact add_pos_of_nonneg_of_pos hfirst hsecond
      refine ⟨?_, hcoeff⟩
      exact natDegree_eq_of_le_of_coeff_ne_zero hle (hcoeff (n + 1) (by omega)).ne'

@[simp] theorem eulerianTypePoly_natDegree {β : ℝ} {alpha : ℕ → ℝ}
    (hβ : 0 < β) (halpha : ∀ n, 0 < alpha n) (n : ℕ) :
    (eulerianTypePoly β alpha n).natDegree = n :=
  (eulerianTypePoly_degree_and_coeff_pos hβ halpha n).1

theorem eulerianTypePoly_coeff_pos {β : ℝ} {alpha : ℕ → ℝ}
    (hβ : 0 < β) (halpha : ∀ n, 0 < alpha n) {n k : ℕ} (hk : k ≤ n) :
    0 < (eulerianTypePoly β alpha n).coeff k :=
  (eulerianTypePoly_degree_and_coeff_pos hβ halpha n).2 k hk

theorem eulerianTypePoly_support {β : ℝ} {alpha : ℕ → ℝ}
    (hβ : 0 < β) (halpha : ∀ n, 0 < alpha n) (n : ℕ) :
    (eulerianTypePoly β alpha n).support = Finset.range (n + 1) := by
  ext k
  simp only [mem_support_iff, Finset.mem_range]
  constructor
  · intro hk
    by_contra hkn
    apply hk
    exact coeff_eq_zero_of_natDegree_lt (by rw [eulerianTypePoly_natDegree hβ halpha]; omega)
  · intro hk
    exact (eulerianTypePoly_coeff_pos hβ halpha (by omega)).ne'

/-- A certificate for distinct negative roots when the leading coefficient is merely positive,
rather than one. -/
def HasOrderedNegativeRootsUpToPositiveScale (p : ℝ[X]) (n : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ z : Fin n → ℝ,
    StrictMono z ∧ (∀ i, z i < 0) ∧ p = C c * ∏ i, (X - C (z i))

lemma HasOrderedNegativeRootsUpToPositiveScale.roots_nodup {p : ℝ[X]} {n : ℕ}
    (h : HasOrderedNegativeRootsUpToPositiveScale p n) : p.roots.Nodup := by
  obtain ⟨c, hc, z, hz, hzneg, hp⟩ := h
  let q : ℝ[X] := ∏ i, (X - C (z i))
  have hq : HasOrderedNegativeRoots q n := ⟨z, hz, hzneg, rfl⟩
  rw [hp, roots_C_mul q hc.ne']
  exact hq.roots_nodup

lemma HasOrderedNegativeRootsUpToPositiveScale.root_lt_zero {p : ℝ[X]} {n : ℕ}
    (h : HasOrderedNegativeRootsUpToPositiveScale p n) {x : ℝ} (hx : x ∈ p.roots) :
    x < 0 := by
  obtain ⟨c, hc, z, hz, hzneg, hp⟩ := h
  let q : ℝ[X] := ∏ i, (X - C (z i))
  have hq : HasOrderedNegativeRoots q n := ⟨z, hz, hzneg, rfl⟩
  rw [hp, roots_C_mul q hc.ne'] at hx
  exact hq.root_lt_zero hx

lemma HasOrderedNegativeRootsUpToPositiveScale.splits {p : ℝ[X]} {n : ℕ}
    (h : HasOrderedNegativeRootsUpToPositiveScale p n) : p.Splits := by
  obtain ⟨c, hc, z, hz, hzneg, rfl⟩ := h
  let q : ℝ[X] := ∏ i, (X - C (z i))
  have hq : HasOrderedNegativeRoots q n := ⟨z, hz, hzneg, rfl⟩
  exact hq.splits.C_mul c

lemma HasOrderedNegativeRootsUpToPositiveScale.exists_positive_linearFactors
    {p : ℝ[X]} {n : ℕ} (h : HasOrderedNegativeRootsUpToPositiveScale p n)
    (hp0 : p.eval 0 = 1) :
    ∃ r : Fin n → ℝ, (∀ i, 0 < r i) ∧ p = ∏ i, (1 + C (r i) * X) := by
  obtain ⟨c, hc, z, hzmono, hzneg, hp⟩ := h
  let r : Fin n → ℝ := fun i ↦ (-z i)⁻¹
  have hzpos (i : Fin n) : 0 < -z i := neg_pos.mpr (hzneg i)
  have hz0 (i : Fin n) : -z i ≠ 0 := (hzpos i).ne'
  have hfactor (i : Fin n) :
      (X - C (z i) : ℝ[X]) = C (-z i) * (1 + C (r i) * X) := by
    dsimp [r]
    rw [mul_add, mul_one, ← mul_assoc, ← C_mul, mul_inv_cancel₀ (hz0 i)]
    simp
    ring
  have hscale : c * ∏ i, (-z i) = 1 := by
    calc
      c * ∏ i, (-z i) = (C c * ∏ i, (X - C (z i) : ℝ[X])).eval 0 := by
        rw [eval_mul, eval_C, eval_prod]
        simp
      _ = p.eval 0 := by rw [← hp]
      _ = 1 := hp0
  refine ⟨r, fun i ↦ inv_pos.mpr (hzpos i), ?_⟩
  calc
    p = C c * ∏ i, (X - C (z i)) := hp
    _ = C c * ∏ i, (C (-z i) * (1 + C (r i) * X)) := by
      congr 1
      exact Finset.prod_congr rfl fun i _ ↦ hfactor i
    _ = C c * ((∏ i, C (-z i)) * ∏ i, (1 + C (r i) * X)) := by
      rw [Finset.prod_mul_distrib]
    _ = C (c * ∏ i, (-z i)) * ∏ i, (1 + C (r i) * X) := by
      rw [← mul_assoc]
      have hmap : (∏ i, C (-z i)) = C (∏ i, -z i) := by
        simpa using map_prod C (fun i : Fin n ↦ -z i) Finset.univ
      rw [hmap, ← C_mul]
    _ = ∏ i, (1 + C (r i) * X) := by rw [hscale]; simp

/-- Strict sign sufficiently far left for a polynomial with positive leading coefficient. -/
lemma exists_lt_eval_with_positive_leading_sign {p : ℝ[X]} {n : ℕ}
    (hdegree : p.natDegree = n) (hlead : 0 < p.leadingCoeff) (hn : 0 < n) (a : ℝ) :
    ∃ x < a, 0 < (-1 : ℝ) ^ n * p.eval x := by
  let g : ℝ[X] := C ((-1 : ℝ) ^ n) * p.comp (-X)
  have hp0 : p ≠ 0 := fun hp ↦ by simpa [hp] using hlead.ne'
  have hgdeg : 0 < g.degree := by
    dsimp [g]
    rw [degree_C_mul (pow_ne_zero _ (by norm_num)), degree_comp_neg_X,
      degree_eq_natDegree hp0, hdegree]
    exact_mod_cast hn
  have hglead : 0 ≤ g.leadingCoeff := by
    dsimp [g]
    rw [leadingCoeff_mul, leadingCoeff_C, comp_neg_X_leadingCoeff_eq, hdegree]
    have hs : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      norm_num
    rw [← mul_assoc, hs, one_mul]
    exact hlead.le
  have ht : Filter.Tendsto (fun x : ℝ ↦ g.eval x) Filter.atTop Filter.atTop :=
    g.tendsto_atTop_of_leadingCoeff_nonneg hgdeg hglead
  have heval : ∀ᶠ x in Filter.atTop, 0 < g.eval x := ht.eventually_gt_atTop 0
  have hbound : ∀ᶠ x : ℝ in Filter.atTop, -a < x := Filter.eventually_gt_atTop (-a)
  obtain ⟨y, hy, hya⟩ := (heval.and hbound).exists
  refine ⟨-y, by linarith, ?_⟩
  simpa [g] using hy

lemma eq_C_leadingCoeff_mul_prod_of_distinct_roots {q : ℝ[X]} {n : ℕ}
    (hdegree : q.natDegree = n) (hlead : 0 < q.leadingCoeff) (hn : 0 < n)
    (w : Fin n → ℝ) (hw : Function.Injective w)
    (hzero : ∀ i, q.eval (w i) = 0) :
    q = C q.leadingCoeff * ∏ i, (X - C (w i)) := by
  classical
  let rootProduct : ℝ[X] := ∏ i, (X - C (w i))
  have hrootExplicit :
      (Finset.univ : Finset (Fin n)).prod (fun j ↦ (X - C (w j) : ℝ[X])) =
        rootProduct := by
    simpa [rootProduct]
  have hrootMonic : IsMonicOfDegree rootProduct n := by
    let hmon : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        (X - C (w i) : ℝ[X]).Monic := fun i _ ↦ monic_X_sub_C _
    rw [← hrootExplicit]
    refine ⟨?_, monic_prod_of_monic Finset.univ (fun i ↦ X - C (w i)) hmon⟩
    rw [natDegree_prod_of_monic (s := Finset.univ) (f := fun i ↦ X - C (w i)) hmon]
    simp
  let qmon : ℝ[X] := C q.leadingCoeff⁻¹ * q
  have hqmon : IsMonicOfDegree qmon n := by
    refine ⟨?_, ?_⟩
    · dsimp [qmon]
      rw [natDegree_C_mul (inv_ne_zero hlead.ne'), hdegree]
    · rw [Monic]
      dsimp [qmon]
      rw [leadingCoeff_mul]
      simp [hlead.ne']
  have hsubdeg : (qmon - rootProduct).natDegree < n :=
    hqmon.natDegree_sub_lt hn.ne' hrootMonic
  have hsubzero : qmon - rootProduct = 0 := by
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hw
    · intro i
      have hqmonzero : qmon.eval (w i) = 0 := by simp [qmon, hzero]
      have hrootzero : rootProduct.eval (w i) = 0 := by
        rw [← hrootExplicit, eval_prod]
        exact Finset.prod_eq_zero
          (f := fun j ↦ (X - C (w j) : ℝ[X]).eval (w i))
          (s := Finset.univ) (i := i) (by simp) (by simp)
      simp [eval_sub, hqmonzero, hrootzero]
    · simpa using hsubdeg
  have hqmon_eq : qmon = rootProduct := sub_eq_zero.mp hsubzero
  calc
    q = C q.leadingCoeff * (C q.leadingCoeff⁻¹ * q) := by
      rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hlead.ne']
      simp
    _ = C q.leadingCoeff * rootProduct := by
      rw [show C q.leadingCoeff⁻¹ * q = rootProduct by simpa [qmon] using hqmon_eq]

/-- Unconditional strict real-rootedness for the generalized recurrence. -/
theorem eulerianTypePoly_hasOrderedNegativeRootsUpToPositiveScale
    {β : ℝ} {alpha : ℕ → ℝ} (hβ : 0 < β) (halpha : ∀ n, 0 < alpha n) :
    ∀ n, HasOrderedNegativeRootsUpToPositiveScale (eulerianTypePoly β alpha n) n := by
  intro n
  induction n with
  | zero =>
      refine ⟨1, zero_lt_one, Fin.elim0, Subsingleton.strictMono _, ?_, ?_⟩
      · exact fun i ↦ Fin.elim0 i
      · simp
  | succ n ih =>
      cases n with
      | zero =>
          let z : Fin 1 → ℝ := fun _ ↦ -(alpha 0)⁻¹
          refine ⟨alpha 0, halpha 0, z, Subsingleton.strictMono z, ?_, ?_⟩
          · intro i
            exact neg_neg_of_pos (inv_pos.mpr (halpha 0))
          · simp [z, eulerianTypePoly_succ]
            rw [mul_add]
            rw [← C_mul, mul_inv_cancel₀ (halpha 0).ne']
            simp
            ring
      | succ m =>
          classical
          obtain ⟨c, hc, z, hzmono, hzneg, hp⟩ := ih
          have hp_explicit : eulerianTypePoly β alpha (m + 1) =
              C c * (Finset.univ : Finset (Fin (m + 1))).prod
                (fun j ↦ (X - C (z j) : ℝ[X])) := by
            simpa using hp
          have hpzero (i : Fin (m + 1)) :
              (eulerianTypePoly β alpha (m + 1)).eval (z i) = 0 := by
            rw [hp_explicit, eval_mul, eval_C, eval_prod]
            rw [Finset.prod_eq_zero
              (f := fun j ↦ (X - C (z j) : ℝ[X]).eval (z i))
              (s := Finset.univ) (i := i) (by simp) (by simp), mul_zero]
          have hder (i : Fin (m + 1)) :
              0 < (-1 : ℝ) ^ (m + 1 - 1 - i.1) *
                (eulerianTypePoly β alpha (m + 1)).derivative.eval (z i) := by
            have hbase := negOnePow_mul_eval_derivative_prod_pos z hzmono i
            have hpos := mul_pos hc hbase
            calc
              0 < c * ((-1 : ℝ) ^ (m + 1 - 1 - i.1) *
                  (derivative ((Finset.univ : Finset (Fin (m + 1))).prod
                    (fun j ↦ (X - C (z j) : ℝ[X])))).eval (z i)) := hpos
              _ = (-1 : ℝ) ^ (m + 1 - 1 - i.1) *
                  (eulerianTypePoly β alpha (m + 1)).derivative.eval (z i) := by
                rw [hp_explicit, derivative_mul]
                simp
                ring
          have hsign (i : Fin (m + 1)) :
              0 < (-1 : ℝ) ^ (m + 1 - i.1) *
                (eulerianTypePoly β alpha (m + 2)).eval (z i) := by
            have heval := eulerianTypePoly_eval_succ β alpha (m + 1) (z i)
            rw [hpzero i] at heval
            simp only [mul_zero, zero_add] at heval
            have hzx : z i * (1 - z i) < 0 :=
              mul_neg_of_neg_of_pos (hzneg i) (by linarith [hzneg i])
            have hcneg : β * z i * (1 - z i) < 0 := by
              nlinarith [mul_neg_of_pos_of_neg hβ hzx]
            have hk : m + 1 - i.1 = (m + 1 - 1 - i.1) + 1 := by omega
            rw [hk, pow_succ, heval]
            calc
              0 < -(β * z i * (1 - z i)) *
                  ((-1 : ℝ) ^ (m + 1 - 1 - i.1) *
                    (eulerianTypePoly β alpha (m + 1)).derivative.eval (z i)) :=
                mul_pos (neg_pos.mpr hcneg) (hder i)
              _ = (-1 : ℝ) ^ (m + 1 - 1 - i.1) * -1 *
                  (β * z i * (1 - z i) *
                    (eulerianTypePoly β alpha (m + 1)).derivative.eval (z i)) := by ring
          have hmiddle_exists (j : Fin m) :
              ∃ x : ℝ, z j.castSucc < x ∧ x < z j.succ ∧
                (eulerianTypePoly β alpha (m + 2)).eval x = 0 := by
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
              (eulerianTypePoly β alpha (m + 2)).eval (z (Fin.last m)) < 0 := by
            have h := hsign (Fin.last m)
            simpa using h
          obtain ⟨lastRoot, hlast_lower, hlast_upper, hlast_zero⟩ :=
            exists_eval_eq_zero_between (eulerianTypePoly β alpha (m + 2))
              (hzneg (Fin.last m)) (by simpa using hlast_sign)
          have hqlead : 0 < (eulerianTypePoly β alpha (m + 2)).leadingCoeff := by
            rw [leadingCoeff, eulerianTypePoly_natDegree hβ halpha]
            exact eulerianTypePoly_coeff_pos hβ halpha (by omega)
          obtain ⟨L, hL, hLsign⟩ :=
            exists_lt_eval_with_positive_leading_sign
              (eulerianTypePoly_natDegree hβ halpha (m + 2)) hqlead (by omega) (z 0)
          have hLsign' :
              0 < (-1 : ℝ) ^ ((m + 1) + 1) *
                (eulerianTypePoly β alpha (m + 2)).eval L := by
            simpa only [Nat.add_assoc] using hLsign
          have hzzero_sign :
              0 < (-1 : ℝ) ^ (m + 1) *
                (eulerianTypePoly β alpha (m + 2)).eval (z 0) := by
            simpa using hsign (0 : Fin (m + 1))
          obtain ⟨leftRoot, hleft_lower, hleft_upper, hleft_zero⟩ :=
            exists_eval_eq_zero_between (eulerianTypePoly β alpha (m + 2)) hL
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
              (eulerianTypePoly β alpha (m + 2)).eval (right i) = 0 := by
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
              (eulerianTypePoly β alpha (m + 2)).eval (w i) = 0 := by
            refine Fin.cases ?_ (fun j ↦ ?_) i
            · simpa [w] using hleft_zero
            · simpa [w] using hright_zero j
          have hfactor := eq_C_leadingCoeff_mul_prod_of_distinct_roots
            (eulerianTypePoly_natDegree hβ halpha (m + 2)) hqlead (by omega)
            w hwmono.injective hwzero
          exact ⟨(eulerianTypePoly β alpha (m + 2)).leadingCoeff, hqlead,
            w, hwmono, hwneg, hfactor⟩

theorem eulerianTypePoly_roots_nodup {β : ℝ} {alpha : ℕ → ℝ}
    (hβ : 0 < β) (halpha : ∀ n, 0 < alpha n) (n : ℕ) :
    (eulerianTypePoly β alpha n).roots.Nodup :=
  (eulerianTypePoly_hasOrderedNegativeRootsUpToPositiveScale hβ halpha n).roots_nodup

theorem eulerianTypePoly_splits {β : ℝ} {alpha : ℕ → ℝ}
    (hβ : 0 < β) (halpha : ∀ n, 0 < alpha n) (n : ℕ) :
    (eulerianTypePoly β alpha n).Splits :=
  (eulerianTypePoly_hasOrderedNegativeRootsUpToPositiveScale hβ halpha n).splits

theorem eulerianTypePoly_isRoot_lt_zero {β : ℝ} {alpha : ℕ → ℝ}
    (hβ : 0 < β) (halpha : ∀ n, 0 < alpha n) (n : ℕ) {x : ℝ}
    (hx : (eulerianTypePoly β alpha n).IsRoot x) : x < 0 := by
  apply (eulerianTypePoly_hasOrderedNegativeRootsUpToPositiveScale hβ halpha n).root_lt_zero
  exact (mem_roots (by
    intro hp
    have := eulerianTypePoly_eval_zero β alpha n
    simp [hp] at this)).2 hx

theorem eulerianTypePoly_rootMultiplicity_eq_one {β : ℝ} {alpha : ℕ → ℝ}
    (hβ : 0 < β) (halpha : ∀ n, 0 < alpha n) (n : ℕ) {x : ℝ}
    (hx : (eulerianTypePoly β alpha n).IsRoot x) :
    rootMultiplicity x (eulerianTypePoly β alpha n) = 1 := by
  rw [← count_roots]
  apply Multiset.count_eq_one_of_mem (eulerianTypePoly_roots_nodup hβ halpha n)
  exact (mem_roots (by
    intro hp
    have := eulerianTypePoly_eval_zero β alpha n
    simp [hp] at this)).2 hx

/-- The normalized positive linear-factor form used in Theorem 4.1. -/
theorem eulerianTypePoly_exists_positive_linearFactors
    {β : ℝ} {alpha : ℕ → ℝ} (hβ : 0 < β) (halpha : ∀ n, 0 < alpha n)
    (n : ℕ) : ∃ r : Fin n → ℝ, (∀ i, 0 < r i) ∧
      eulerianTypePoly β alpha n = ∏ i, (1 + C (r i) * X) :=
  (eulerianTypePoly_hasOrderedNegativeRootsUpToPositiveScale hβ halpha n).exists_positive_linearFactors
    (eulerianTypePoly_eval_zero β alpha n)


end LeanCo.EulerianTP3
