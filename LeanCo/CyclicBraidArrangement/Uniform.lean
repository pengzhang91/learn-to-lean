import LeanCo.CyclicBraidArrangement.CyclePolynomial

/-! Uniform interval matrices and their compatibility. -/

namespace CyclicBraidArrangement

namespace DeformationMatrix

/-- Matrix encoding the interval arrangement `[-u,v]`. -/
def uniform (n u v : ℕ) : DeformationMatrix n where
  entry i j := if i = j then 0 else if i < j then u else v
  diagonal_zero i := by simp

theorem uniform_entry_of_lt {n u v : ℕ} {i j : Fin n} (h : i < j) :
    (uniform n u v).entry i j = u := by
  simp [uniform, h, ne_of_lt h]

theorem uniform_entry_of_gt {n u v : ℕ} {i j : Fin n} (h : j < i) :
    (uniform n u v).entry i j = v := by
  simp [uniform, ne_of_gt h, not_lt_of_ge (le_of_lt h)]

theorem cyclicallyCompatible_uniform (n u v : ℕ) :
    (uniform n u v).CyclicallyCompatible := by
  intro a b c hab hac hbc
  simp only [uniform, hac, hab, hbc, if_false]
  split_ifs <;> omega

/-- A cyclic descent in a word represented by a permutation. -/
def cyclicDescent {n : ℕ} [NeZero n] (w : CyclicOrdering n) (k : Fin n) : Prop :=
  w (nextPosition n k) < w k

noncomputable def cyclicDescents {n : ℕ} [NeZero n]
    (w : CyclicOrdering n) : ℕ := by
  classical
  exact (Finset.univ.filter (cyclicDescent w)).card

open scoped Classical in
theorem uniform_cycleWeight_as_indicator {n u v : ℕ} [NeZero n]
    (hn : 2 ≤ n) (w : CyclicOrdering n) :
    (uniform n u v).cycleWeight w =
      ∑ k, if cyclicDescent w k then v else u := by
  classical
  apply Finset.sum_congr rfl
  intro k hk
  have hne : w k ≠ w (nextPosition n k) :=
    w.injective.ne (nextPosition_ne_self hn k).symm
  by_cases hd : w (nextPosition n k) < w k
  · have ha : ¬w k < w (nextPosition n k) := hd.asymm
    simp [uniform, cyclicDescent, hne, hd, ha]
  · have ha : w k < w (nextPosition n k) :=
      lt_of_le_of_ne (le_of_not_gt hd) hne
    simp [uniform, cyclicDescent, hne, hd, ha]

open scoped Classical in
/-- The cyclic weight of the uniform interval matrix is `n u` plus the
signed increment `v-u` for every cyclic descent.  Stating the identity in
`ℤ` avoids imposing an artificial order on `u` and `v`. -/
theorem uniform_cycleWeight_eq_descents {n u v : ℕ} [NeZero n]
    (hn : 2 ≤ n) (w : CyclicOrdering n) :
    ((uniform n u v).cycleWeight w : ℤ) =
      (n : ℤ) * u + ((v : ℤ) - u) * cyclicDescents w := by
  rw [uniform_cycleWeight_as_indicator hn w]
  push_cast
  calc
    (∑ k : Fin n, (if cyclicDescent w k then (v : ℤ) else u)) =
        ∑ k : Fin n, ((u : ℤ) + ((v : ℤ) - u) *
          if cyclicDescent w k then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro k hk
      by_cases h : cyclicDescent w k <;> simp [h]
    _ = (n : ℤ) * u + ((v : ℤ) - u) * cyclicDescents w := by
      rw [Finset.sum_add_distrib]
      rw [← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Finset.sum_boole, cyclicDescents]

/-- Substitution of the uniform descent statistic into the paper's cyclic
binomial expression. -/
theorem cycleFormula_uniform {n u v : ℕ} [NeZero n] (hn : 2 ≤ n) (t : ℚ) :
    cycleFormula (uniform n u v) t =
      ∑ w : NormalizedCycle n,
        generalizedChoose
          (t - (((n : ℤ) * u + ((v : ℤ) - u) * cyclicDescents w.1 : ℤ) : ℚ) - 1)
          (n - 1) := by
  classical
  unfold cycleFormula
  apply Finset.sum_congr rfl
  intro w hw
  have h := uniform_cycleWeight_eq_descents (u := u) (v := v) hn w.1
  have hq : ((uniform n u v).cycleWeight w.1 : ℚ) =
      (((n : ℤ) * u + ((v : ℤ) - u) * cyclicDescents w.1 : ℤ) : ℚ) := by
    exact_mod_cast h
  rw [hq]

theorem uniform_symmetric_cycleWeight {n m : ℕ} [NeZero n]
    (hn : 2 ≤ n) (w : CyclicOrdering n) :
    (uniform n m m).cycleWeight w = n * m := by
  have h := uniform_cycleWeight_eq_descents (u := m) (v := m) hn w
  norm_num at h
  exact_mod_cast h

/-- Symmetric uniform intervals collapse the cyclic sum to `(n-1)!`
identical summands. -/
theorem cycleFormula_uniform_symmetric {n m : ℕ} [NeZero n]
    (hn : 2 ≤ n) (t : ℚ) :
    cycleFormula (uniform n m m) t =
      ((n - 1).factorial : ℚ) * generalizedChoose (t - n * m - 1) (n - 1) := by
  classical
  unfold cycleFormula
  simp_rw [uniform_symmetric_cycleWeight hn]
  rw [Finset.sum_const, Finset.card_univ, card_normalizedCycle]
  simp only [nsmul_eq_mul]
  push_cast
  rfl

/-- Falling-factorial form of the symmetric uniform specialization. -/
theorem cycleFormula_uniform_symmetric_falling {n m : ℕ} [NeZero n]
    (hn : 2 ≤ n) (t : ℚ) :
    cycleFormula (uniform n m m) t =
      ∏ i ∈ Finset.range (n - 1), (t - n * m - 1 - i) := by
  rw [cycleFormula_uniform_symmetric hn]
  unfold generalizedChoose
  have hfac : ((n - 1).factorial : ℚ) ≠ 0 := by positivity
  field_simp

/-- Two-sided symmetric interval formula, depending on the parameters only
through their total sum. -/
theorem cycleFormula_uniform_symmetric_extend {n m : ℕ} [NeZero n]
    (hn : 2 ≤ n) (α β : Fin n → ℕ) (t : ℚ) :
    cycleFormula ((uniform n m m).extend α β) t =
      ∏ i ∈ Finset.range (n - 1),
        (t - ((∑ j, α j) + ∑ j, β j) - n * m - 1 - i) := by
  rw [cycleFormula_extend_shift hn,
    cycleFormula_uniform_symmetric_falling hn]

/-- Factorization of the full cyclic-formula candidate for a two-sided
symmetric uniform interval deformation.  The independent finite-field bridge
turns this candidate identity into the characteristic-polynomial statement. -/
theorem eval_fullCyclePolynomialCandidate_uniform_symmetric_extend
    {n m : ℕ} [NeZero n] (hn : 2 ≤ n)
    (α β : Fin n → ℕ) (t : ℚ) :
    Polynomial.eval t
        (fullCyclePolynomialCandidate ((uniform n m m).extend α β)) =
      t * ∏ i ∈ Finset.range (n - 1),
        (t - ((∑ j, α j) + ∑ j, β j) - n * m - 1 - i) := by
  rw [fullCyclePolynomialCandidate, Polynomial.eval_mul, Polynomial.eval_X,
    eval_cyclePolynomial, cycleFormula_uniform_symmetric_extend hn]

end DeformationMatrix
end CyclicBraidArrangement
