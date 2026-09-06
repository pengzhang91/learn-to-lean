import LeanCo.SizeRamsey.GraphBasics
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Mass dichotomy for the approximately regular decomposition

This file isolates the arithmetic ``mass halving'' step used in the v1 proof
of Beke--Li--Sahasrabudhe Lemma 2.1.  All graph edge counts remain natural
numbers in the decomposition identity and are cast to `ℝ` before any
fractional comparison is made.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open Finset SimpleGraph

noncomputable section

universe u

/-! ## The finite geometric estimate -/

/-- If `0 ≤ c < 2/5`, then every finite tail `c + ⋯ + c^T` is strictly
less than `2/3`.  The strict upper bound is what turns the negations of both
alternatives in the mass dichotomy into a contradiction. -/
theorem sum_pow_Icc_one_lt_two_thirds {c : ℝ} (hc0 : 0 ≤ c)
    (hc : c < 2 / 5) (T : ℕ) :
    ∑ j ∈ Finset.Icc 1 T, c ^ j < 2 / 3 := by
  rw [← Finset.Ico_add_one_right_eq_Icc]
  have hcOne : c < 1 := hc.trans (by norm_num)
  have honeSub : 0 < 1 - c := sub_pos.mpr hcOne
  have hgeom := geom_sum_Ico_mul_neg c (show 1 ≤ T + 1 by omega)
  have hpowNonneg : 0 ≤ c ^ (T + 1) := pow_nonneg hc0 _
  have hmul :
      (∑ j ∈ Finset.Ico 1 (T + 1), c ^ j) * (1 - c) ≤ c := by
    rw [hgeom]
    simpa using sub_le_self c hpowNonneg
  have hsum :
      (∑ j ∈ Finset.Ico 1 (T + 1), c ^ j) ≤ c / (1 - c) := by
    exact (le_div_iff₀ honeSub).2 hmul
  have hfraction : c / (1 - c) < 2 / 3 := by
    rw [div_lt_iff₀ honeSub]
    nlinarith
  exact hsum.trans_lt hfraction

/-! ## Natural-number mass identities -/

/-- Generic mass dichotomy.  The decomposition identity is kept in `ℕ`;
the two alternatives are stated only after casting all masses to `ℝ`.

The index condition is written explicitly as `1 ≤ j ∧ j ≤ T`, matching
the paper's `j = 1, …, T` convention. -/
theorem approxRegularMass_dichotomy_generic
    (total residual T : ℕ) (piece : ℕ → ℕ)
    (hmass : total = residual + ∑ j ∈ Finset.Icc 1 T, piece j)
    {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 2 / 5) :
    (total : ℝ) / 3 ≤ (residual : ℝ) ∨
      ∃ j : ℕ, 1 ≤ j ∧ j ≤ T ∧
        c ^ j * (total : ℝ) ≤ (piece j : ℝ) := by
  by_cases hresidual : (total : ℝ) / 3 ≤ (residual : ℝ)
  · exact Or.inl hresidual
  · right
    by_contra hpiece
    push Not at hpiece
    have hresidualLt : (residual : ℝ) < (total : ℝ) / 3 :=
      lt_of_not_ge hresidual
    have htotalPos : (0 : ℝ) < (total : ℝ) := by
      have hresidualNonneg : (0 : ℝ) ≤ (residual : ℝ) := by positivity
      nlinarith
    have hmassReal :
        (total : ℝ) = (residual : ℝ) +
          ∑ j ∈ Finset.Icc 1 T, (piece j : ℝ) := by
      exact_mod_cast hmass
    have hpieces :
        (∑ j ∈ Finset.Icc 1 T, (piece j : ℝ)) ≤
          (∑ j ∈ Finset.Icc 1 T, c ^ j) * (total : ℝ) := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro j hj
      have hjBounds := Finset.mem_Icc.mp hj
      exact (hpiece j hjBounds.1 hjBounds.2).le
    have hgeometric := sum_pow_Icc_one_lt_two_thirds hc0 hc T
    have hpiecesLt :
        (∑ j ∈ Finset.Icc 1 T, (piece j : ℝ)) <
          (2 / 3 : ℝ) * total := by
      exact hpieces.trans_lt (mul_lt_mul_of_pos_right hgeometric htotalPos)
    have hsumLt :
        (residual : ℝ) + ∑ j ∈ Finset.Icc 1 T, (piece j : ℝ) <
          (total : ℝ) := by
      calc
        (residual : ℝ) +
              ∑ j ∈ Finset.Icc 1 T, (piece j : ℝ) <
            (total : ℝ) / 3 + (2 / 3 : ℝ) * total :=
          add_lt_add hresidualLt hpiecesLt
        _ = (total : ℝ) := by ring
    rw [← hmassReal] at hsumLt
    exact (lt_irrefl _ hsumLt)

/-- The paper's fixed constant `c₂ = exp (-1)` satisfies the generic
hypotheses, so the mass dichotomy specializes without an external numerical
assumption. -/
theorem approxRegularMass_dichotomy_exp_neg_one
    (total residual T : ℕ) (piece : ℕ → ℕ)
    (hmass : total = residual + ∑ j ∈ Finset.Icc 1 T, piece j) :
    (total : ℝ) / 3 ≤ (residual : ℝ) ∨
      ∃ j : ℕ, 1 ≤ j ∧ j ≤ T ∧
        Real.exp (-1) ^ j * (total : ℝ) ≤ (piece j : ℝ) := by
  apply approxRegularMass_dichotomy_generic total residual T piece hmass
  · exact (Real.exp_pos (-1)).le
  · exact Real.exp_neg_one_lt_d9.trans (by norm_num)

/-! ## Graph-facing specialization -/

/-- Graph-facing statement of the mass dichotomy.  No adjacency decisions
are used: the proof sees only the natural-number values of `edgeCount`. -/
theorem approxRegularEdgeCount_mass_dichotomy
    {V : Type u} [Fintype V]
    (G R : SimpleGraph V) (E : ℕ → SimpleGraph V) (T : ℕ)
    (hmass : edgeCount G = edgeCount R +
      ∑ j ∈ Finset.Icc 1 T, edgeCount (E j)) :
    (edgeCount G : ℝ) / 3 ≤ (edgeCount R : ℝ) ∨
      ∃ j : ℕ, 1 ≤ j ∧ j ≤ T ∧
        Real.exp (-1) ^ j * (edgeCount G : ℝ) ≤
          (edgeCount (E j) : ℝ) := by
  exact approxRegularMass_dichotomy_exp_neg_one
    (edgeCount G) (edgeCount R) T (fun j ↦ edgeCount (E j)) hmass

end

end LeanCo.SizeRamsey
