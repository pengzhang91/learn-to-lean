import LeanCo.PackingEdgeColoring.Defs

/-!
# Degree counting for the `12/5` discharging contradiction

The paper phrases the last step of Section 3 as a discharging argument.  For
a graph whose vertices all have degree two or three, it is exactly the
integer inequality proved below: if every degree-two vertex can be charged
to two degree-three endpoints and every degree-three vertex receives at most
three charges, then `2 n₂ ≤ 3 n₃`, hence the average degree is at least
`12/5`.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open SimpleGraph

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The ambient degree-two vertices. -/
def degreeTwoVertices : Finset V :=
  Finset.univ.filter fun v ↦ G.degree v = 2

/-- The ambient degree-three vertices. -/
def degreeThreeVertices : Finset V :=
  Finset.univ.filter fun v ↦ G.degree v = 3

@[simp] theorem mem_degreeTwoVertices {v : V} :
    v ∈ degreeTwoVertices G ↔ G.degree v = 2 := by
  simp [degreeTwoVertices]

@[simp] theorem mem_degreeThreeVertices {v : V} :
    v ∈ degreeThreeVertices G ↔ G.degree v = 3 := by
  simp [degreeThreeVertices]

theorem degreeTwoVertices_disjoint_degreeThreeVertices :
    Disjoint (degreeTwoVertices G) (degreeThreeVertices G) := by
  rw [Finset.disjoint_left]
  intro v hv2 hv3
  have h2 := (mem_degreeTwoVertices (G := G)).mp hv2
  have h3 := (mem_degreeThreeVertices (G := G)).mp hv3
  omega

theorem degreeTwoVertices_union_degreeThreeVertices
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3) :
    degreeTwoVertices G ∪ degreeThreeVertices G = Finset.univ := by
  ext v
  simp only [Finset.mem_union, mem_degreeTwoVertices, mem_degreeThreeVertices,
    Finset.mem_univ, iff_true]
  exact hdeg v

theorem card_degreeTwo_add_card_degreeThree
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3) :
    (degreeTwoVertices G).card + (degreeThreeVertices G).card = Fintype.card V := by
  rw [← Finset.card_union_of_disjoint
    (degreeTwoVertices_disjoint_degreeThreeVertices G)]
  rw [degreeTwoVertices_union_degreeThreeVertices G hdeg, Finset.card_univ]

private theorem sum_degrees_on_degreeTwo :
    (∑ v ∈ degreeTwoVertices G, G.degree v) =
      2 * (degreeTwoVertices G).card := by
  calc
    (∑ v ∈ degreeTwoVertices G, G.degree v) =
        ∑ _v ∈ degreeTwoVertices G, 2 := by
          apply Finset.sum_congr rfl
          intro v hv
          exact (mem_degreeTwoVertices (G := G)).mp hv
    _ = 2 * (degreeTwoVertices G).card := by simp [Nat.mul_comm]

private theorem sum_degrees_on_degreeThree :
    (∑ v ∈ degreeThreeVertices G, G.degree v) =
      3 * (degreeThreeVertices G).card := by
  calc
    (∑ v ∈ degreeThreeVertices G, G.degree v) =
        ∑ _v ∈ degreeThreeVertices G, 3 := by
          apply Finset.sum_congr rfl
          intro v hv
          exact (mem_degreeThreeVertices (G := G)).mp hv
    _ = 3 * (degreeThreeVertices G).card := by simp [Nat.mul_comm]

theorem sum_degrees_eq_two_three_counts
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3) :
    (∑ v, G.degree v) =
      2 * (degreeTwoVertices G).card + 3 * (degreeThreeVertices G).card := by
  calc
    (∑ v, G.degree v) =
        ∑ v ∈ degreeTwoVertices G ∪ degreeThreeVertices G, G.degree v := by
          rw [degreeTwoVertices_union_degreeThreeVertices G hdeg]
    _ = (∑ v ∈ degreeTwoVertices G, G.degree v) +
        ∑ v ∈ degreeThreeVertices G, G.degree v := by
          exact Finset.sum_union (degreeTwoVertices_disjoint_degreeThreeVertices G)
    _ = 2 * (degreeTwoVertices G).card + 3 * (degreeThreeVertices G).card := by
          rw [sum_degrees_on_degreeTwo, sum_degrees_on_degreeThree]

/-- The integer arithmetic at the heart of the `12/5` discharging step. -/
theorem twelve_mul_vertices_le_five_mul_degreeSum_of_counts
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hcount : 2 * (degreeTwoVertices G).card ≤ 3 * (degreeThreeVertices G).card) :
    12 * Fintype.card V ≤ 5 * ∑ v, G.degree v := by
  rw [sum_degrees_eq_two_three_counts G hdeg,
    ← card_degreeTwo_add_card_degreeThree G hdeg]
  omega

/-- Graph-theoretic form of the closing inequality: the average degree is
at least `12/5`, with division cleared. -/
theorem twelve_mul_vertices_le_ten_mul_edges_of_counts
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hcount : 2 * (degreeTwoVertices G).card ≤ 3 * (degreeThreeVertices G).card) :
    12 * Fintype.card V ≤ 5 * (2 * G.edgeFinset.card) := by
  rw [← G.sum_degrees_eq_twice_card_edges]
  exact twelve_mul_vertices_le_five_mul_degreeSum_of_counts G hdeg hcount

end Finite

end

end LeanCo.PackingEdgeColoring
