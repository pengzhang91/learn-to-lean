import LeanCo.LaplacianLFunctions.Divisors

/-!
# The Laplacian lattice

For a finite loopless multigraph `G`, its Laplacian sends a divisor `D` to

`v ↦ ∑ w, multiplicity v w * (D v - D w)`.

The Laplacian lattice is its range over `ℤ`.  Symmetry of edge
multiplicities implies that every principal divisor has degree zero.
-/

namespace LeanCo.LaplacianLFunctions

namespace LooplessMultigraph

variable {V : Type*} [Fintype V]

/-- The integral graph Laplacian, acting on divisors. -/
def laplacian (G : LooplessMultigraph V) : Divisor V →ₗ[ℤ] Divisor V where
  toFun D v := ∑ w, (G.multiplicity v w : ℤ) * (D v - D w)
  map_add' D E := by
    funext v
    simp only [Pi.add_apply]
    simp_rw [add_sub_add_comm]
    simp_rw [mul_add]
    exact Finset.sum_add_distrib
  map_smul' n D := by
    funext v
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w hw
    simp only [RingHom.id_apply]
    ring

@[simp]
theorem laplacian_apply (G : LooplessMultigraph V) (D : Divisor V) (v : V) :
    G.laplacian D v = ∑ w, (G.multiplicity v w : ℤ) * (D v - D w) :=
  rfl

@[simp]
theorem laplacian_zero (G : LooplessMultigraph V) : G.laplacian (0 : Divisor V) = 0 := by
  simp

/-- The Laplacian lattice (equivalently, the group of principal divisors). -/
def laplacianLattice (G : LooplessMultigraph V) : Submodule ℤ (Divisor V) :=
  LinearMap.range G.laplacian

@[simp]
theorem mem_laplacianLattice_iff (G : LooplessMultigraph V) (D : Divisor V) :
    D ∈ G.laplacianLattice ↔ ∃ E : Divisor V, G.laplacian E = D :=
  Iff.rfl

/-- The sum of the coefficients of a Laplacian divisor is zero. -/
theorem degree_laplacian (G : LooplessMultigraph V) (D : Divisor V) :
    Divisor.degree (G.laplacian D) = 0 := by
  classical
  let A : ℤ := ∑ v, ∑ w, (G.multiplicity v w : ℤ) * D v
  let B : ℤ := ∑ v, ∑ w, (G.multiplicity v w : ℤ) * D w
  have hAB : A = B := by
    dsimp only [A, B]
    calc
      (∑ v, ∑ w, (G.multiplicity v w : ℤ) * D v) =
          ∑ w, ∑ v, (G.multiplicity v w : ℤ) * D v := by
            exact Finset.sum_comm
      _ = ∑ w, ∑ v, (G.multiplicity w v : ℤ) * D v := by
            apply Finset.sum_congr rfl
            intro w hw
            apply Finset.sum_congr rfl
            intro v hv
            rw [G.multiplicity_swap]
      _ = (∑ v, ∑ w, (G.multiplicity v w : ℤ) * D w) := by
            rfl
  change (∑ v, ∑ w, (G.multiplicity v w : ℤ) * (D v - D w)) = 0
  calc
    (∑ v, ∑ w, (G.multiplicity v w : ℤ) * (D v - D w)) = A - B := by
      dsimp only [A, B]
      simp_rw [mul_sub, Finset.sum_sub_distrib]
    _ = 0 := sub_eq_zero.mpr hAB

/-- The Laplacian lattice is contained in the degree-zero submodule. -/
theorem laplacianLattice_le_degree_ker (G : LooplessMultigraph V) :
    G.laplacianLattice ≤ LinearMap.ker Divisor.degree := by
  rintro D ⟨E, rfl⟩
  exact G.degree_laplacian E

end LooplessMultigraph

end LeanCo.LaplacianLFunctions
