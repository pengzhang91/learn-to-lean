import LeanCo.LaplacianLFunctions.GraphInvariants
import LeanCo.LaplacianLFunctions.LFunctionPolynomial
import LeanCo.LaplacianLFunctions.Example310
import Mathlib.Tactic

/-!
# Explicit examples from arXiv:2608.29981

This file gives kernel-checkable certificates for the concrete graphs in
Examples 3.10 and 4.6.  All finite computations are expanded by ordinary
Lean reduction and tactics; no native or bit-vector decision procedure is
used.
-/

open scoped BigOperators

namespace LeanCo.LaplacianLFunctions

noncomputable section

/-! ## Example 4.6: nonisomorphic graphs with the same Laplacian lattice -/

/-- Multiplicity table of the graph `X` in Example 4.6. -/
def example46XMultiplicity : Fin 5 → Fin 5 → ℕ := ![
  ![0, 0, 0, 0, 2],
  ![0, 0, 0, 0, 2],
  ![0, 0, 0, 1, 1],
  ![0, 0, 1, 0, 1],
  ![2, 2, 1, 1, 0]]

/-- The graph `X` in Example 4.6. -/
def example46X : LooplessMultigraph (Fin 5) where
  multiplicity := example46XMultiplicity
  multiplicity_symm i j := by
    fin_cases i <;> fin_cases j <;> rfl
  multiplicity_self i := by
    fin_cases i <;> rfl

/-- Multiplicity table of the graph `X'` in Example 4.6. -/
def example46X'Multiplicity : Fin 5 → Fin 5 → ℕ := ![
  ![0, 2, 0, 0, 0],
  ![2, 0, 0, 0, 2],
  ![0, 0, 0, 1, 1],
  ![0, 0, 1, 0, 1],
  ![0, 2, 1, 1, 0]]

/-- The graph `X'` in Example 4.6. -/
def example46X' : LooplessMultigraph (Fin 5) where
  multiplicity := example46X'Multiplicity
  multiplicity_symm i j := by
    fin_cases i <;> fin_cases j <;> rfl
  multiplicity_self i := by
    fin_cases i <;> rfl

/-- Unimodular change of firing potentials witnessing one inclusion of the
two Laplacian lattices in Example 4.6. -/
def example46PotentialToX' (D : Divisor (Fin 5)) : Divisor (Fin 5) := ![
  2 * D 0 + D 1 - 2 * D 4,
  D 0 + D 1 - D 4,
  D 2,
  D 3,
  D 4]

/-- The inverse integral change of firing potentials. -/
def example46PotentialToX (D : Divisor (Fin 5)) : Divisor (Fin 5) := ![
  D 0 - D 1 + D 4,
  -D 0 + 2 * D 1,
  D 2,
  D 3,
  D 4]

/-- The displayed change of potentials takes the `X` Laplacian to the
`X'` Laplacian. -/
theorem example46_laplacian_toX' (D : Divisor (Fin 5)) :
    example46X.laplacian D =
      example46X'.laplacian (example46PotentialToX' D) := by
  funext i
  fin_cases i <;>
    simp [LooplessMultigraph.laplacian_apply, example46X,
      example46X', example46XMultiplicity, example46X'Multiplicity,
      example46PotentialToX', Fin.sum_univ_succ] <;> ring

/-- The inverse displayed change of potentials takes the `X'` Laplacian to
the `X` Laplacian. -/
theorem example46_laplacian_toX (D : Divisor (Fin 5)) :
    example46X'.laplacian D =
      example46X.laplacian (example46PotentialToX D) := by
  funext i
  fin_cases i <;>
    simp [LooplessMultigraph.laplacian_apply, example46X,
      example46X', example46XMultiplicity, example46X'Multiplicity,
      example46PotentialToX, Fin.sum_univ_succ] <;> ring

/-- The actual claim of Example 4.6: under the paper's common vertex labels,
the two graphs have literally equal Laplacian lattices. -/
theorem example46_laplacianLattice_eq :
    example46X.laplacianLattice = example46X'.laplacianLattice := by
  apply le_antisymm
  · rintro D ⟨f, rfl⟩
    exact ⟨example46PotentialToX' f,
      (example46_laplacian_toX' f).symm⟩
  · rintro D ⟨f, rfl⟩
    exact ⟨example46PotentialToX f,
      (example46_laplacian_toX f).symm⟩

/-- Ordered valency formula for `X`; its degree multiset is
`{6,2,2,2,2}`. -/
theorem example46X_valency (i : Fin 5) :
    example46X.valency i = if i = 4 then 6 else 2 := by
  fin_cases i <;>
    simp [LooplessMultigraph.valency, example46X,
      example46XMultiplicity, Fin.sum_univ_succ]

/-- Ordered valency formula for `X'`; its degree multiset is
`{4,4,2,2,2}`. -/
theorem example46X'_valency (i : Fin 5) :
    example46X'.valency i = if i = 1 ∨ i = 4 then 4 else 2 := by
  fin_cases i <;>
    simp [LooplessMultigraph.valency, example46X',
      example46X'Multiplicity, Fin.sum_univ_succ]

/-- No relabelling can preserve the valencies of the two Example 4.6
graphs; in particular they cannot be isomorphic. -/
theorem example46_no_valency_preserving_equiv :
    ¬ ∃ σ : Fin 5 ≃ Fin 5,
      ∀ i, example46X.valency i = example46X'.valency (σ i) := by
  rintro ⟨σ, hσ⟩
  have h := hσ 4
  rw [example46X_valency, example46X'_valency] at h
  split_ifs at h <;> omega

end

end LeanCo.LaplacianLFunctions
