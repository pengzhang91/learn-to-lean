import LeanCo.LaplacianLFunctions.Divisors
import Mathlib.Algebra.BigOperators.Sym
import Mathlib.Order.Extension.Well
import Mathlib.Tactic

/-!
# Basic invariants of a finite loopless multigraph

This file records the numerical graph invariants used in §2 and §3 of
arXiv:2608.29981.  Edges and valencies are counted with multiplicity.  The
genus is integer-valued, avoiding truncated natural-number subtraction; for a
connected graph it is the usual cycle rank.
-/

namespace LeanCo.LaplacianLFunctions

open scoped BigOperators

namespace LooplessMultigraph

variable {V : Type*}

/-- The multiplicity function descended from ordered pairs to unordered
pairs. -/
def edgeMultiplicity (G : LooplessMultigraph V) : Sym2 V → ℕ :=
  Sym2.lift ⟨G.multiplicity, G.multiplicity_symm⟩

@[simp]
theorem edgeMultiplicity_mk (G : LooplessMultigraph V) (v w : V) :
    G.edgeMultiplicity s(v, w) = G.multiplicity v w := by
  rfl

@[simp]
theorem edgeMultiplicity_diag (G : LooplessMultigraph V) (v : V) :
    G.edgeMultiplicity s(v, v) = 0 := by
  simp

variable [Fintype V]

/-- The number of (unordered) edges, with each parallel edge counted. -/
noncomputable def edgeCount (G : LooplessMultigraph V) : ℕ := by
  classical
  exact ∑ e : Sym2 V, G.edgeMultiplicity e

/-- Valency of a vertex, counting parallel edges with multiplicity. -/
noncomputable def valency (G : LooplessMultigraph V) (v : V) : ℕ := by
  classical
  exact ∑ w, G.multiplicity v w

private theorem sum_offDiag_eq_two_mul_sum_lt
    (G : LooplessMultigraph V) [LinearOrder V] :
    ∑ p ∈ (Finset.univ : Finset V).offDiag, G.multiplicity p.1 p.2 =
      2 * ∑ p ∈ (Finset.univ : Finset V).offDiag with p.1 < p.2,
        G.multiplicity p.1 p.2 := by
  let upper := (Finset.univ : Finset V).offDiag.filter fun p ↦ p.1 < p.2
  let lower := (Finset.univ : Finset V).offDiag.filter fun p ↦ p.2 < p.1
  have h_union : upper ∪ lower = (Finset.univ : Finset V).offDiag := by
    ext p
    simp only [upper, lower, Finset.mem_union, Finset.mem_filter,
      Finset.mem_offDiag, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨hne, _⟩ | ⟨hne, _⟩)
      · exact hne
      · exact hne
    · intro hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact Or.inl ⟨hne, hlt⟩
      · exact Or.inr ⟨hne, hgt⟩
  have h_disjoint : Disjoint upper lower := by
    refine Finset.disjoint_left.mpr ?_
    intro p hpU hpL
    have hlt : p.1 < p.2 := (Finset.mem_filter.mp hpU).2
    have hgt : p.2 < p.1 := (Finset.mem_filter.mp hpL).2
    exact asymm hlt hgt
  have h_swap :
      ∑ p ∈ lower, G.multiplicity p.1 p.2 =
        ∑ p ∈ upper, G.multiplicity p.1 p.2 := by
    apply Finset.sum_bij (fun p _ ↦ (p.2, p.1))
    · intro p hp
      have hp' := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨by
        simpa [Finset.mem_offDiag, ne_comm] using hp'.1, hp'.2⟩
    · intro a ha b hb hab
      exact Prod.ext (congrArg Prod.snd hab) (congrArg Prod.fst hab)
    · intro b hb
      refine ⟨(b.2, b.1), ?_, by simp⟩
      have hb' := Finset.mem_filter.mp hb
      exact Finset.mem_filter.mpr ⟨by
        simpa [Finset.mem_offDiag, ne_comm] using hb'.1, hb'.2⟩
    · intro p hp
      exact G.multiplicity_symm p.1 p.2
  calc
    ∑ p ∈ (Finset.univ : Finset V).offDiag, G.multiplicity p.1 p.2 =
        (∑ p ∈ upper, G.multiplicity p.1 p.2) +
          ∑ p ∈ lower, G.multiplicity p.1 p.2 := by
      rw [← h_union, Finset.sum_union h_disjoint]
    _ = 2 * ∑ p ∈ upper, G.multiplicity p.1 p.2 := by
      rw [h_swap]
      omega
    _ = 2 * ∑ p ∈ (Finset.univ : Finset V).offDiag with p.1 < p.2,
        G.multiplicity p.1 p.2 := by rfl

/-- The handshake identity for a finite loopless multigraph, with all
quantities counted with multiplicity. -/
theorem sum_valency_eq_two_mul_edgeCount (G : LooplessMultigraph V) :
    ∑ v, G.valency v = 2 * G.edgeCount := by
  classical
  letI : LinearOrder V := WellOrderingRel.isWellOrder.linearOrder
  have hordered :
      ∑ v, G.valency v =
        ∑ p ∈ (Finset.univ : Finset V).offDiag, G.multiplicity p.1 p.2 := by
    change (∑ v ∈ (Finset.univ : Finset V),
      ∑ w ∈ (Finset.univ : Finset V), G.multiplicity v w) = _
    rw [← Finset.sum_product (Finset.univ : Finset V) (Finset.univ : Finset V)
      (fun p ↦ G.multiplicity p.1 p.2)]
    rw [← Finset.diag_union_offDiag,
      Finset.sum_union (Finset.disjoint_diag_offDiag (Finset.univ : Finset V))]
    simp
  rw [hordered, sum_offDiag_eq_two_mul_sum_lt]
  congr 1
  rw [edgeCount, ← Finset.sym2_univ]
  rw [← Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset V).sym2 (fun e ↦ e.IsDiag)]
  simp only [Finset.sum_sym2_filter_not_isDiag]
  have hdiagzero :
      ∑ e ∈ (Finset.univ : Finset V).sym2 with e.IsDiag,
          G.edgeMultiplicity e = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    rcases e with ⟨v, w⟩
    simp_all [Sym2.IsDiag]
  rw [hdiagzero, zero_add]
  rfl

/-- Euler genus `|E| - |V| + 1`.  It is stated in `ℤ` so that the
definition makes sense without a connectedness hypothesis or truncated
subtraction. -/
noncomputable def genus (G : LooplessMultigraph V) : ℤ :=
  (G.edgeCount : ℤ) - (Fintype.card V : ℤ) + 1

/-- The canonical divisor `K(v) = val(v) - 2`. -/
noncomputable def canonicalDivisor (G : LooplessMultigraph V) : Divisor V :=
  fun v ↦ (G.valency v : ℤ) - 2

@[simp]
theorem canonicalDivisor_apply (G : LooplessMultigraph V) (v : V) :
    G.canonicalDivisor v = (G.valency v : ℤ) - 2 :=
  rfl

/-- The degree of the canonical divisor is `2g - 2`. -/
theorem degree_canonicalDivisor (G : LooplessMultigraph V) :
    Divisor.degree G.canonicalDivisor = 2 * G.genus - 2 := by
  rw [Divisor.degree_apply]
  simp only [canonicalDivisor, Finset.sum_sub_distrib, Finset.sum_const,
    nsmul_eq_mul, ← Nat.cast_sum]
  rw [G.sum_valency_eq_two_mul_edgeCount]
  simp [genus]
  ring

end LooplessMultigraph

end LeanCo.LaplacianLFunctions
