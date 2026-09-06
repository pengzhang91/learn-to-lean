import LeanCo.PackingEdgeColoring.LocalColoring
import LeanCo.PackingEdgeColoring.MaximumAverageDegree

/-!
# Finite capacity bounds for packing edge-colour classes

This file isolates the counting argument used by the explicit lower-bound
examples.  A matching uses two distinct vertices per edge, while a family in
which no three distinct edges can be pairwise compatible has size at most two.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open Finset SimpleGraph

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The finite fibre of a semantic edge colouring. -/
def semanticColorClass {k : ℕ} (colour : G.edgeSet → OneTwoColor k)
    (a : OneTwoColor k) : Finset G.edgeSet :=
  Finset.univ.filter fun e ↦ colour e = a

@[simp] theorem mem_semanticColorClass {k : ℕ}
    (colour : G.edgeSet → OneTwoColor k) (a : OneTwoColor k)
    (e : G.edgeSet) :
    e ∈ semanticColorClass G colour a ↔ colour e = a := by
  simp [semanticColorClass]

/-- Colour fibres partition the finite edge set. -/
theorem edge_count_eq_sum_semanticColorClass {k : ℕ}
    (colour : G.edgeSet → OneTwoColor k) :
    G.edgeFinset.card =
      ∑ a : OneTwoColor k, (semanticColorClass G colour a).card := by
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset G.edgeSet))
    (t := (Finset.univ : Finset (OneTwoColor k)))
    (f := colour) (by simp)
  simpa [semanticColorClass, G.edgeSet_univ_card] using h

/-- A finite matching consumes two distinct vertices per edge. -/
theorem two_mul_card_le_of_pairwise_endpointDisjoint
    (M : Finset G.edgeSet)
    (hM : ∀ e ∈ M, ∀ f ∈ M, e ≠ f → EndpointDisjoint G e f) :
    2 * M.card ≤ Fintype.card V := by
  classical
  let A := {e : G.edgeSet // e ∈ M}
  let R : A → V → Prop := fun e v ↦ v ∈ (e.1 : Sym2 V)
  letI : DecidableRel R := fun _ _ ↦ Classical.propDecidable _
  have hleft : ∀ e : A,
      2 ≤ (Finset.univ.filter fun v : V ↦ R e v).card := by
    intro e
    have heq :
        (Finset.univ.filter fun v : V ↦ R e v) =
          (e.1.1 : Sym2 V).toFinset := by
      ext v
      simp [R, Sym2.mem_toFinset]
    rw [heq, Sym2.card_toFinset_of_not_isDiag]
    exact G.not_isDiag_of_mem_edgeSet e.1.2
  have hright : ∀ v : V,
      (Finset.univ.filter fun e : A ↦ R e v).card ≤ 1 := by
    intro v
    apply Finset.card_le_one_iff.mpr
    intro e f he hf
    apply Subtype.ext
    by_contra hef
    have hdisj := hM e.1 e.2 f.1 f.2 hef
    exact hdisj v (by simpa [R] using he) (by simpa [R] using hf)
  have hcount := mul_card_le_mul_card_of_relation R 2 1 hleft hright
  simpa [A] using hcount

/-- A matching colour class in a valid semantic colouring satisfies the
usual vertex-capacity bound. -/
theorem two_mul_matchingClass_card_le {k : ℕ}
    {colour : G.edgeSet → OneTwoColor k}
    (hcolour : IsOneTwoColoring G colour) :
    2 * (semanticColorClass G colour none).card ≤ Fintype.card V := by
  apply two_mul_card_le_of_pairwise_endpointDisjoint G
  intro e he f hf hef
  have hp := hcolour e (by simp) f (by simp) hef
  simpa [(mem_semanticColorClass G colour none e).mp he,
    (mem_semanticColorClass G colour none f).mp hf] using hp

/-- If a relation cannot hold pairwise on three distinct members of a finite
set, that set has cardinality at most two. -/
theorem card_le_two_of_no_pairwise_triple {A : Type*} [DecidableEq A]
    (R : A → A → Prop) (M : Finset A)
    (hpair : ∀ e ∈ M, ∀ f ∈ M, e ≠ f → R e f)
    (htriple : ∀ e f g : A, e ≠ f → e ≠ g → f ≠ g →
      ¬ (R e f ∧ R e g ∧ R f g)) :
    M.card ≤ 2 := by
  by_contra hcard
  have hlt : 2 < M.card := Nat.lt_of_not_ge hcard
  obtain ⟨e, f, g, he, hf, hg, hef, heg, hfg⟩ :=
    Finset.two_lt_card_iff.mp hlt
  exact htriple e f g hef heg hfg
    ⟨hpair e he f hf hef, hpair e he g hg heg,
      hpair f hf g hg hfg⟩

/-- A colour class has size at most two whenever the host graph admits no
three distinct pairwise induced-separated edges. -/
theorem inducedColorClass_card_le_two_of_no_triple {k : ℕ}
    {colour : G.edgeSet → OneTwoColor k}
    (hcolour : IsOneTwoColoring G colour)
    (htriple : ∀ e f g : G.edgeSet, e ≠ f → e ≠ g → f ≠ g →
      ¬ (InducedSeparated G e f ∧ InducedSeparated G e g ∧
        InducedSeparated G f g))
    (i : Fin k) :
    (semanticColorClass G colour (some i)).card ≤ 2 := by
  apply card_le_two_of_no_pairwise_triple (InducedSeparated G)
    (semanticColorClass G colour (some i))
  · intro e he f hf hef
    have hp := hcolour e (by simp) f (by simp) hef
    simpa [(mem_semanticColorClass G colour (some i) e).mp he,
      (mem_semanticColorClass G colour (some i) f).mp hf] using hp
  · exact htriple

/-- Sum the matching and induced-colour capacity bounds. -/
theorem edge_count_le_of_semanticColorClass_bounds {k matchingCap inducedCap : ℕ}
    (colour : G.edgeSet → OneTwoColor k)
    (hmatching : (semanticColorClass G colour none).card ≤ matchingCap)
    (hinduced : ∀ i : Fin k,
      (semanticColorClass G colour (some i)).card ≤ inducedCap) :
    G.edgeFinset.card ≤ matchingCap + k * inducedCap := by
  rw [edge_count_eq_sum_semanticColorClass G colour, Fintype.sum_option]
  apply Nat.add_le_add hmatching
  calc
    (∑ i : Fin k, (semanticColorClass G colour (some i)).card) ≤
        ∑ _i : Fin k, inducedCap :=
      Finset.sum_le_sum fun i _ ↦ hinduced i
    _ = k * inducedCap := by simp

end Finite

end

end LeanCo.PackingEdgeColoring
