import LeanCo.PackingEdgeColoring.Defs
import LeanCo.PackingEdgeColoring.GirthTools
import LeanCo.PackingEdgeColoring.PackingCapacity

/-!
# The two finite lower-bound graphs

This file records the graphs `G₁` and `G₂` from Figure 1 of
Kim--Liu--Xu by explicit edge tables.  Later files prove their packing
edge-colouring obstructions.  Keeping the tables here gives those proofs a
small, fully reducible finite model.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open SimpleGraph

namespace Counterexamples

/-- Vertex numbering for Figure 1(a): `u₁,...,u₄` are `0,...,3` and
`v₁,...,v₇` are `4,...,10`. -/
abbrev G₁Vertex := Fin 11

private def G₁Edges : List (G₁Vertex × G₁Vertex) :=
  [ (0, 1), (1, 2), (2, 3), (3, 0),
    (4, 5), (5, 6), (6, 7), (7, 8), (8, 9), (9, 10), (10, 4),
    (0, 4), (1, 6), (2, 7), (3, 9),
    (5, 8) ]

/-- The 11-vertex graph `G₁` from Figure 1(a). -/
def G₁ : SimpleGraph G₁Vertex :=
  SimpleGraph.fromRel fun u v ↦ (u, v) ∈ G₁Edges

instance : DecidableRel G₁.Adj := by
  dsimp [G₁]
  infer_instance

/-- Vertex numbering for Figure 1(b): `u₁,...,u₅` are `0,...,4` and
`v₁,...,v₁₀` are `5,...,14`. -/
abbrev G₂Vertex := Fin 15

private def G₂Edges : List (G₂Vertex × G₂Vertex) :=
  [ (0, 1), (1, 2), (2, 3), (3, 4), (4, 0),
    (5, 6), (6, 7), (7, 8), (8, 9), (9, 10),
    (10, 11), (11, 12), (12, 13), (13, 14), (14, 5),
    (0, 5), (1, 7), (2, 9), (3, 11), (4, 13),
    (8, 12) ]

/-- The 15-vertex graph `G₂` from Figure 1(b). -/
def G₂ : SimpleGraph G₂Vertex :=
  SimpleGraph.fromRel fun u v ↦ (u, v) ∈ G₂Edges

instance : DecidableRel G₂.Adj := by
  dsimp [G₂]
  infer_instance

theorem G₁_edge_count : G₁.edgeFinset.card = 16 := by
  decide

theorem G₂_edge_count : G₂.edgeFinset.card = 21 := by
  decide

theorem G₁_subcubic : IsSubcubic G₁ := by
  change ∀ v, G₁.degree v ≤ 3
  decide

theorem G₂_subcubic : IsSubcubic G₂ := by
  change ∀ v, G₂.degree v ≤ 3
  decide

theorem G₁_hasNoTriangle : HasNoTriangle G₁ := by
  change ∀ a b c, ¬(G₁.Adj a b ∧ G₁.Adj b c ∧ G₁.Adj c a)
  decide

theorem G₂_hasNoTriangle : HasNoTriangle G₂ := by
  change ∀ a b c, ¬(G₂.Adj a b ∧ G₂.Adj b c ∧ G₂.Adj c a)
  decide

theorem G₂_hasNoFourCycle : HasNoFourCycle G₂ := by
  change ∀ a b c d, a ≠ c → b ≠ d →
    ¬(G₂.Adj a b ∧ G₂.Adj b c ∧ G₂.Adj c d ∧ G₂.Adj d a)
  decide

/-- The displayed inner 4-cycle of `G₁`. -/
def G₁FourCycle : G₁.Walk (0 : G₁Vertex) 0 :=
  .cons (by decide : G₁.Adj 0 1) <|
    .cons (by decide : G₁.Adj 1 2) <|
      .cons (by decide : G₁.Adj 2 3) <|
        .cons (by decide : G₁.Adj 3 0) .nil

theorem G₁FourCycle_isCycle : G₁FourCycle.IsCycle := by
  simp [Walk.isCycle_def, Walk.isTrail_def, G₁FourCycle]

@[simp] theorem G₁FourCycle_length : G₁FourCycle.length = 4 := rfl

/-- The displayed inner 5-cycle of `G₂`. -/
def G₂FiveCycle : G₂.Walk (0 : G₂Vertex) 0 :=
  .cons (by decide : G₂.Adj 0 1) <|
    .cons (by decide : G₂.Adj 1 2) <|
      .cons (by decide : G₂.Adj 2 3) <|
        .cons (by decide : G₂.Adj 3 4) <|
          .cons (by decide : G₂.Adj 4 0) .nil

theorem G₂FiveCycle_isCycle : G₂FiveCycle.IsCycle := by
  simp [Walk.isCycle_def, Walk.isTrail_def, G₂FiveCycle]

@[simp] theorem G₂FiveCycle_length : G₂FiveCycle.length = 5 := rfl

theorem G₁_egirth_eq_four : G₁.egirth = 4 := by
  apply le_antisymm
  · simpa using egirth_le_length G₁FourCycle_isCycle
  · exact four_le_egirth_of_hasNoTriangle G₁ G₁_hasNoTriangle

theorem G₂_egirth_eq_five : G₂.egirth = 5 := by
  apply le_antisymm
  · simpa using egirth_le_length G₂FiveCycle_isCycle
  · exact five_le_egirth_of_hasNoTriangle_hasNoFourCycle G₂
      G₂_hasNoTriangle G₂_hasNoFourCycle

/-! ## The `(1,2^5)` obstruction on `G₁` -/

set_option maxHeartbeats 5000000 in
/-- Exhaustive finite certificate for the only graph-specific step in the
`G₁` counting proof: no three distinct edges form one induced matching. -/
theorem G₁_no_three_pairwise_inducedSeparated :
    ∀ e f g : G₁.edgeSet, e ≠ f → e ≠ g → f ≠ g →
      ¬ (InducedSeparated G₁ e f ∧ InducedSeparated G₁ e g ∧
        InducedSeparated G₁ f g) := by
  letI : DecidableRel (EndpointDisjoint G₁) :=
    fun _ _ ↦ Fintype.decidableForallFintype
  letI : DecidableRel (HasCrossEdge G₁) :=
    fun _ _ ↦ Fintype.decidableExistsFintype
  letI : DecidableRel (InducedSeparated G₁) :=
    fun _ _ ↦ by
      unfold InducedSeparated
      infer_instance
  letI tripleDecidable (e f g : G₁.edgeSet) : Decidable
      (e ≠ f → e ≠ g → f ≠ g →
        ¬ (InducedSeparated G₁ e f ∧ InducedSeparated G₁ e g ∧
          InducedSeparated G₁ f g)) := inferInstance
  letI thirdDecidable (e f : G₁.edgeSet) : Decidable
      (∀ g : G₁.edgeSet, e ≠ f → e ≠ g → f ≠ g →
        ¬ (InducedSeparated G₁ e f ∧ InducedSeparated G₁ e g ∧
          InducedSeparated G₁ f g)) :=
    Fintype.decidableForallFintype
  letI secondDecidable (e : G₁.edgeSet) : Decidable
      (∀ f g : G₁.edgeSet, e ≠ f → e ≠ g → f ≠ g →
        ¬ (InducedSeparated G₁ e f ∧ InducedSeparated G₁ e g ∧
          InducedSeparated G₁ f g)) :=
    Fintype.decidableForallFintype
  letI : Decidable
      (∀ e f g : G₁.edgeSet, e ≠ f → e ≠ g → f ≠ g →
        ¬ (InducedSeparated G₁ e f ∧ InducedSeparated G₁ e g ∧
          InducedSeparated G₁ f g)) :=
    Fintype.decidableForallFintype
  decide

/-- Figure 1(a) has no `(1,2^5)` packing edge-colouring.  The matching
colour contains at most five edges on eleven vertices, each of the five
induced colours contains at most two edges, but `G₁` has sixteen edges. -/
theorem G₁_not_hasOneTwoPackingEdgeColoring :
    ¬ HasOneTwoPackingEdgeColoring G₁ 5 := by
  rw [hasOneTwoPackingEdgeColoring_iff_exists_local]
  rintro ⟨colour, hcolour⟩
  have hmatchingTwo := two_mul_matchingClass_card_le G₁ hcolour
  have hmatching :
      (semanticColorClass G₁ colour none).card ≤ 5 := by
    have hvertices : Fintype.card G₁Vertex = 11 := by simp [G₁Vertex]
    rw [hvertices] at hmatchingTwo
    omega
  have hinduced : ∀ i : Fin 5,
      (semanticColorClass G₁ colour (some i)).card ≤ 2 :=
    inducedColorClass_card_le_two_of_no_triple G₁ hcolour
      G₁_no_three_pairwise_inducedSeparated
  have hcapacity := edge_count_le_of_semanticColorClass_bounds
    G₁ colour hmatching hinduced
  rw [G₁_edge_count] at hcapacity
  omega

end Counterexamples

end LeanCo.PackingEdgeColoring
