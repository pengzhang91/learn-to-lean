import LeanCo.HypercubeTuran.Defs

/-!
# Elementary hypercube facts and the paper's parity coloring

The color of an edge in direction `i` is the parity of the coordinates
strictly before `i` in either endpoint.  Excluding `i` makes the definition
independent of the orientation of the unordered edge.
-/

open scoped SimpleGraph symmDiff

namespace LeanCo.HypercubeTuran

open Finset SimpleGraph

universe u

variable {ι : Type u} [DecidableEq ι]

/-- An adjacent pair has a unique direction. -/
noncomputable def cubeDirection {A B : Finset ι}
    (h : (hypercubeGraph ι).Adj A B) : ι :=
  (Finset.card_eq_one.mp ((hypercubeGraph_adj A B).mp h)).choose

theorem symmDiff_eq_singleton_cubeDirection {A B : Finset ι}
    (h : (hypercubeGraph ι).Adj A B) :
    A ∆ B = {cubeDirection h} :=
  (Finset.card_eq_one.mp ((hypercubeGraph_adj A B).mp h)).choose_spec

theorem cubeDirection_symm {A B : Finset ι}
    (h : (hypercubeGraph ι).Adj A B) :
    cubeDirection h.symm = cubeDirection h := by
  apply Finset.singleton_injective
  calc
    {cubeDirection h.symm} = B ∆ A :=
      (symmDiff_eq_singleton_cubeDirection h.symm).symm
    _ = A ∆ B := symmDiff_comm B A
    _ = {cubeDirection h} := symmDiff_eq_singleton_cubeDirection h

/-- Toggling the unique direction carries either endpoint of a cube edge to
the other. -/
theorem symmDiff_singleton_cubeDirection {A B : Finset ι}
    (h : (hypercubeGraph ι).Adj A B) :
    A ∆ {cubeDirection h} = B := by
  rw [← symmDiff_eq_singleton_cubeDirection h]
  exact symmDiff_symmDiff_cancel_left A B

/-- Away from the toggled coordinate, adjacent cube vertices have identical
membership. -/
theorem mem_iff_mem_of_ne_cubeDirection {A B : Finset ι}
    (h : (hypercubeGraph ι).Adj A B) {j : ι}
    (hj : j ≠ cubeDirection h) :
    j ∈ A ↔ j ∈ B := by
  have hs := symmDiff_eq_singleton_cubeDirection h
  have hjnot : j ∉ A ∆ B := by
    rw [hs]
    simpa
  simp only [Finset.mem_symmDiff, not_or, not_and] at hjnot
  tauto

section LinearOrder

variable [LinearOrder ι]

/-- Coordinates strictly preceding `i` that occur in `A`. -/
def cubePrefix (A : Finset ι) (i : ι) : Finset ι :=
  A.filter fun j => j < i

/-- The prefix parity, as one of two colors. -/
def prefixParity (A : Finset ι) (i : ι) : Fin 2 :=
  ⟨(cubePrefix A i).card % 2, Nat.mod_lt _ (by decide)⟩

theorem prefix_eq_of_symmDiff_eq_singleton {A B : Finset ι} {i : ι}
    (h : A ∆ B = {i}) :
    cubePrefix A i = cubePrefix B i := by
  ext j
  simp only [cubePrefix, mem_filter]
  constructor
  · rintro ⟨hjA, hji⟩
    refine ⟨?_, hji⟩
    by_contra hjB
    have hjSD : j ∈ A ∆ B := Finset.mem_symmDiff.mpr (Or.inl ⟨hjA, hjB⟩)
    rw [h] at hjSD
    have : j = i := by simpa using hjSD
    exact (ne_of_lt hji) this
  · rintro ⟨hjB, hji⟩
    refine ⟨?_, hji⟩
    by_contra hjA
    have hjSD : j ∈ A ∆ B := Finset.mem_symmDiff.mpr (Or.inr ⟨hjB, hjA⟩)
    rw [h] at hjSD
    have : j = i := by simpa using hjSD
    exact (ne_of_lt hji) this

theorem prefixParity_eq_of_symmDiff_eq_singleton {A B : Finset ι} {i : ι}
    (h : A ∆ B = {i}) :
    prefixParity A i = prefixParity B i := by
  simp [prefixParity, prefix_eq_of_symmDiff_eq_singleton h]

/-- Symmetric vertex-pair form of the parity color. -/
noncomputable def parityColorFn (A B : Finset ι)
    (h : (hypercubeGraph ι).Adj A B) : Fin 2 :=
  prefixParity A (cubeDirection h)

theorem parityColorFn_symm (A B : Finset ι)
    (h : (hypercubeGraph ι).Adj A B) :
    parityColorFn B A h.symm = parityColorFn A B h := by
  rw [parityColorFn, parityColorFn, cubeDirection_symm]
  exact (prefixParity_eq_of_symmDiff_eq_singleton
    (symmDiff_eq_singleton_cubeDirection h)).symm

/-- The explicit two-edge-coloring used in Lemma 2.2 and Proposition 2.3. -/
noncomputable def parityColoring :
    (hypercubeGraph ι).EdgeLabeling (Fin 2) :=
  SimpleGraph.EdgeLabeling.mk parityColorFn parityColorFn_symm

@[simp]
theorem parityColoring_get (A B : Finset ι)
    (h : (hypercubeGraph ι).Adj A B) :
    parityColoring.get A B h = prefixParity A (cubeDirection h) :=
  rfl

end LinearOrder

end LeanCo.HypercubeTuran
