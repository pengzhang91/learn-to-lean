import Mathlib

/-!
# Telescoping products for the generating-function identity

The functional equation used in Theorem 3.1 of the paper has the abstract form

`I (k + 1) / I k = F k`.

This file separates the completely algebraic finite telescoping argument from the
analytic passage to an infinite product.  In particular, the infinite statement never
treats a formal iteration as an infinite product without an explicit convergence
hypothesis.
-/

open Filter Topology
open scoped BigOperators Topology

namespace LeanCo.GeneratingFunction

section FiniteProduct

variable {G : Type*} [CommGroup G]

/-- The finite telescoping core of Theorem 3.1. -/
theorem prod_range_eq_div (I F : ℕ → G)
    (hstep : ∀ k, I (Nat.succ k) / I k = F k) (N : ℕ) :
    (∏ k ∈ Finset.range N, F k) = I N / I 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.prod_range_succ, ih, ← hstep N]
      rw [← Nat.succ_eq_add_one]
      calc
        I N / I 0 * (I N.succ / I N) =
            (I N * (I N)⁻¹) * (I N.succ * (I 0)⁻¹) := by
              simp only [div_eq_mul_inv]
              ac_rfl
        _ = I N.succ / I 0 := by simp [div_eq_mul_inv]

end FiniteProduct

section InfiniteProduct

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

/--
If the iterates tend to `1`, the finite products tend to the reciprocal of the initial
value.  This is the precise limit statement behind the infinite iteration in the paper.
-/
theorem tendsto_prod_range_of_tendsto_one (I F : ℕ → G)
    (hstep : ∀ k, I (Nat.succ k) / I k = F k)
    (hI : Tendsto I atTop (nhds 1)) :
    Tendsto (fun N => ∏ k ∈ Finset.range N, F k) atTop (nhds (I 0)⁻¹) := by
  have hquot : Tendsto (fun N => I N / I 0) atTop (nhds (1 / I 0)) :=
    hI.div' tendsto_const_nhds
  simpa only [prod_range_eq_div I F hstep, one_div] using hquot

/--
If the factors are (unconditionally) `Multipliable`, the preceding sequential limit
identifies their `HasProd`.  The extra hypothesis is essential in this generality:
convergence of ordered partial products alone need not imply unconditional convergence.
-/
theorem hasProd_of_tendsto_one [T2Space G] (I F : ℕ → G)
    (hstep : ∀ k, I (Nat.succ k) / I k = F k)
    (hI : Tendsto I atTop (nhds 1))
    (hF : Multipliable F) :
    HasProd F (I 0)⁻¹ := by
  exact hF.hasProd_iff_tendsto_nat.mpr
    (tendsto_prod_range_of_tendsto_one I F hstep hI)

/--
Paper-style conclusion stated purely with ordered partial products: if those products
also tend to `P`, then the initial generating-function value is `P⁻¹`.
-/
theorem initial_eq_inv_of_tendsto_prod [T2Space G] (I F : ℕ → G) (P : G)
    (hstep : ∀ k, I (Nat.succ k) / I k = F k)
    (hI : Tendsto I atTop (nhds 1))
    (hP : Tendsto (fun N => ∏ k ∈ Finset.range N, F k) atTop (nhds P)) :
    I 0 = P⁻¹ := by
  have hcanonical := tendsto_prod_range_of_tendsto_one I F hstep hI
  have hP_eq : P = (I 0)⁻¹ := tendsto_nhds_unique hP hcanonical
  rw [hP_eq]
  simp

/--
Paper-style conclusion: if `P` is asserted to be the infinite product, then the initial
generating-function value is `P⁻¹`.  Hausdorffness is used only to make limits unique.
-/
theorem initial_eq_inv_of_hasProd [T2Space G] (I F : ℕ → G) (P : G)
    (hstep : ∀ k, I (Nat.succ k) / I k = F k)
    (hI : Tendsto I atTop (nhds 1))
    (hP : HasProd F P) :
    I 0 = P⁻¹ := by
  exact initial_eq_inv_of_tendsto_prod I F P hstep hI hP.tendsto_prod_nat

/-- The literal `tprod` version of the product formula in Theorem 3.1. -/
theorem initial_eq_inv_tprod [T2Space G] (I F : ℕ → G)
    (hstep : ∀ k, I (Nat.succ k) / I k = F k)
    (hI : Tendsto I atTop (nhds 1))
    (hF : Multipliable F) :
    I 0 = (∏' k, F k)⁻¹ := by
  exact initial_eq_inv_of_hasProd I F (∏' k, F k) hstep hI hF.hasProd

end InfiniteProduct

end LeanCo.GeneratingFunction
