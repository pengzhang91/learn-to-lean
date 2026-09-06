import LeanCo.CyclicBraidArrangement.WeakSumDirect
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Pi

/-!
# The directed-Hamiltonian affine hull, without an external premise

The paper cites the dimension of the asymmetric travelling-salesman
polytope in its proof of Lemma 3.1.  Here the required direction-space
statement is recovered from the direct constant-tour/weak-sum theorem and
finite-dimensional dual separation.  Consequently the paper-facing affine
hull lemma below has no hypothesis standing for the cited result.
-/

namespace CyclicBraidArrangement

open scoped BigOperators

namespace WeakSumConverse

private theorem sum_by_arc_tail {n : ℕ} (ρ : Fin n → ℝ) (x : ArcSpace n) :
    (∑ e, ρ e.1.1 * x e) =
      ∑ i, ρ i * ∑ e, if e.1.1 = i then x e else 0 := by
  classical
  calc
    (∑ e, ρ e.1.1 * x e) =
        ∑ e, ∑ i, if e.1.1 = i then ρ i * x e else 0 := by
          apply Finset.sum_congr rfl
          intro e he
          simp
    _ = ∑ i, ∑ e, if e.1.1 = i then ρ i * x e else 0 :=
      Finset.sum_comm
    _ = ∑ i, ρ i * ∑ e, if e.1.1 = i then x e else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      split_ifs <;> simp_all

private theorem sum_by_arc_head {n : ℕ} (γ : Fin n → ℝ) (x : ArcSpace n) :
    (∑ e, γ e.1.2 * x e) =
      ∑ j, γ j * ∑ e, if e.1.2 = j then x e else 0 := by
  classical
  calc
    (∑ e, γ e.1.2 * x e) =
        ∑ e, ∑ j, if e.1.2 = j then γ j * x e else 0 := by
          apply Finset.sum_congr rfl
          intro e he
          simp
    _ = ∑ j, ∑ e, if e.1.2 = j then γ j * x e else 0 :=
      Finset.sum_comm
    _ = ∑ j, γ j * ∑ e, if e.1.2 = j then x e else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      split_ifs <;> simp_all

/-- A weak row-plus-column coefficient matrix annihilates every balanced arc
flow. -/
theorem coefficientFunctional_eq_zero_of_weakSum_of_balanced {n : ℕ}
    (D : Fin n → Fin n → ℝ) (hD : IsWeakSum D)
    (x : ArcSpace n) (hx : degreeMap n x = 0) :
    coefficientFunctional D x = 0 := by
  classical
  rcases hD with ⟨ρ, γ, hD⟩
  have hout (i : Fin n) :
      (∑ e, if e.1.1 = i then x e else 0) = 0 := by
    have h := congrFun (congrArg Prod.fst hx) i
    simpa [degreeMap] using h
  have hin (j : Fin n) :
      (∑ e, if e.1.2 = j then x e else 0) = 0 := by
    have h := congrFun (congrArg Prod.snd hx) j
    simpa [degreeMap] using h
  unfold coefficientFunctional
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  calc
    (∑ e, D e.1.1 e.1.2 * x e) =
        ∑ e, (ρ e.1.1 + γ e.1.2) * x e := by
          apply Finset.sum_congr rfl
          intro e he
          rw [hD _ _ e.2]
    _ = (∑ e, ρ e.1.1 * x e) + ∑ e, γ e.1.2 * x e := by
      simp only [add_mul, Finset.sum_add_distrib]
    _ = _ := by
      rw [sum_by_arc_tail, sum_by_arc_head]
      simp [hout, hin]

/-- Every functional on the finite arc-coordinate space is the coefficient
functional of its values on the coordinate vectors. -/
theorem exists_coefficientMatrix (n : ℕ) (ℓ : ArcSpace n →ₗ[ℝ] ℝ) :
    ∃ D : Fin n → Fin n → ℝ, coefficientFunctional D = ℓ := by
  classical
  let D : Fin n → Fin n → ℝ := fun i j ↦
    if h : i ≠ j then ℓ (arcBasis ⟨(i, j), h⟩) else 0
  refine ⟨D, ?_⟩
  apply LinearMap.ext
  intro x
  rw [LinearMap.pi_apply_eq_sum_univ ℓ x]
  unfold coefficientFunctional
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  apply Finset.sum_congr rfl
  intro e he
  have hD : D e.1.1 e.1.2 = ℓ (arcBasis e) := by
    simp [D, e.2]
  rw [hD]
  change ℓ (arcBasis e) * x e = x e •
    ℓ (fun j ↦ if e = j then 1 else 0)
  simp only [smul_eq_mul]
  have hb : (fun j ↦ if e = j then (1 : ℝ) else 0) = arcBasis e := by
    funext j
    simp [arcBasis, eq_comm]
  rw [hb]
  ring

/-- Lemma 3.1 in direction-space form: differences of directed Hamiltonian
cycle incidence vectors span the full space cut out by the homogeneous
in/out-degree equations.  This is the direction-space statement equivalent
to equality of the two affine hulls in the paper. -/
theorem hamiltonianAffineHull_direct {n : ℕ} [NeZero n] (hn : 2 ≤ n) :
    HamiltonianAffineHull hn := by
  intro x hx
  let S : Subspace ℝ (ArcSpace n) :=
    Submodule.span ℝ (differenceSet (cycleIncidence hn))
  rw [← S.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro ℓ hℓ
  obtain ⟨D, hD⟩ := exists_coefficientMatrix n ℓ
  have hconst : ∀ a b : DeformationMatrix.CyclicOrdering n,
      additiveCycleWeight D a = additiveCycleWeight D b := by
    intro a b
    rw [← coefficientFunctional_cycleIncidence hn,
      ← coefficientFunctional_cycleIncidence hn, hD]
    have hdiff : cycleIncidence hn a - cycleIncidence hn b ∈ S := by
      apply Submodule.subset_span
      exact ⟨a, b, rfl⟩
    have hzero := (Submodule.mem_dualAnnihilator ℓ).mp hℓ _ hdiff
    exact sub_eq_zero.mp (by simpa using hzero)
  have hweak : IsWeakSum D :=
    (constant_hamiltonian_weight_iff_weakSum_direct hn D).mp hconst
  rw [← hD]
  exact coefficientFunctional_eq_zero_of_weakSum_of_balanced D hweak x
    (LinearMap.mem_ker.mp hx)

/-- Every directed Hamiltonian-cycle incidence vector has one outgoing and
one incoming arc at each vertex. -/
theorem degreeMap_cycleIncidence {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (w : DeformationMatrix.CyclicOrdering n) :
    degreeMap n (cycleIncidence hn w) =
      (fun _ ↦ (1 : ℝ), fun _ ↦ (1 : ℝ)) := by
  classical
  have hinc : cycleIncidence hn w = ∑ k, arcBasis (cycleArc hn w k) := by
    funext e
    simp [cycleIncidence, arcBasis, eq_comm]
  rw [hinc, map_sum]
  simp_rw [degreeMap_arcBasis]
  ext i
  · simp only [Prod.fst_sum, Finset.sum_apply]
    change (∑ k, if (cycleArc hn w k).1.1 = i then (1 : ℝ) else 0) = 1
    calc
      (∑ k, if (cycleArc hn w k).1.1 = i then (1 : ℝ) else 0) =
          ∑ k, if w k = i then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro k hk
        by_cases hki : w k = i <;> simp [cycleArc, hki]
      _ = ∑ j, if j = i then (1 : ℝ) else 0 :=
        Equiv.sum_comp w (fun j ↦ if j = i then (1 : ℝ) else 0)
      _ = 1 := by simp
  · simp only [Prod.snd_sum, Finset.sum_apply]
    change (∑ k, if (cycleArc hn w k).1.2 = i then (1 : ℝ) else 0) = 1
    let f : Fin n → ℝ := fun j ↦ if j = i then 1 else 0
    calc
      (∑ k, if (cycleArc hn w k).1.2 = i then (1 : ℝ) else 0) =
          ∑ k, f (w (DeformationMatrix.nextPosition n k)) := by
        apply Finset.sum_congr rfl
        intro k hk
        by_cases hki : w (DeformationMatrix.nextPosition n k) = i <;>
          simp [cycleArc, f, hki]
      _ = ∑ j, f j := by
        simpa only [Equiv.trans_apply] using
          Equiv.sum_comp ((DeformationMatrix.nextPosition n).trans w) f
      _ = 1 := by simp [f]

/-- The reverse containment in the affine-hull direction statement: every
cycle-incidence difference is balanced. -/
theorem span_cycleIncidence_differences_le_balanced
    {n : ℕ} [NeZero n] (hn : 2 ≤ n) :
    Submodule.span ℝ (differenceSet (cycleIncidence hn)) ≤
      LinearMap.ker (degreeMap n) := by
  rw [Submodule.span_le]
  intro x hx
  rcases hx with ⟨a, b, rfl⟩
  change degreeMap n (cycleIncidence hn a - cycleIncidence hn b) = 0
  rw [map_sub, degreeMap_cycleIncidence hn,
    degreeMap_cycleIncidence hn, sub_self]

/-- Lemma 3.1 as equality of direction spaces: the span of all differences
of directed Hamiltonian-cycle incidence vectors is exactly the homogeneous
solution space of the in/out-degree equations. -/
theorem span_cycleIncidence_differences_eq_balanced
    {n : ℕ} [NeZero n] (hn : 2 ≤ n) :
    Submodule.span ℝ (differenceSet (cycleIncidence hn)) =
      LinearMap.ker (degreeMap n) := by
  apply le_antisymm
  · exact span_cycleIncidence_differences_le_balanced hn
  · exact hamiltonianAffineHull_direct hn

end WeakSumConverse

end CyclicBraidArrangement
