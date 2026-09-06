import Mathlib

/-!
# Packing edge-colourings

This file gives the graph-theoretic language used in Kim--Liu--Xu,
*On (1,2^4) and (1,2^5)-packing edge-coloring of sparse subcubic graphs*
(arXiv:2608.29163).  Edges are vertices of the line graph, so the definition
below is the paper's definition literally: two distinct edges receiving a
colour of radius `s` must be at line-graph distance at least `s + 1`.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open SimpleGraph

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

/-- A packing edge-colouring with prescribed separation radius for each
colour. -/
def IsPackingEdgeColoring {t : ℕ} (radius : Fin t → ℕ)
    (colour : G.edgeSet → Fin t) : Prop :=
  ∀ e f : G.edgeSet, e ≠ f → colour e = colour f →
    ((radius (colour e) + 1 : ℕ) : ℕ∞) ≤ G.lineGraph.edist e f

/-- The radius sequence `(1, 2, ..., 2)` with one matching colour and `k`
induced-matching colours. -/
def oneTwoRadius (k : ℕ) (i : Fin (k + 1)) : ℕ :=
  if i = 0 then 1 else 2

/-- Existence of a `(1,2^k)`-packing edge-colouring. -/
def HasOneTwoPackingEdgeColoring (k : ℕ) : Prop :=
  ∃ colour : G.edgeSet → Fin (k + 1),
    IsPackingEdgeColoring G (oneTwoRadius k) colour

/-- A set of edges whose pairwise line-graph distance is greater than `s`.
For `s = 1` this is a matching; for `s = 2` this is an induced matching. -/
def IsEdgePacking (s : ℕ) (M : Set G.edgeSet) : Prop :=
  ∀ ⦃e⦄, e ∈ M → ∀ ⦃f⦄, f ∈ M → e ≠ f →
    ((s + 1 : ℕ) : ℕ∞) ≤ G.lineGraph.edist e f

theorem isPackingEdgeColoring_iff_colourClasses {t : ℕ}
    (radius : Fin t → ℕ) (colour : G.edgeSet → Fin t) :
    IsPackingEdgeColoring G radius colour ↔
      ∀ i, IsEdgePacking G (radius i) {e | colour e = i} := by
  constructor
  · intro h i e he f hf hef
    change colour e = i at he
    change colour f = i at hf
    simpa only [he] using h e f hef (he.trans hf.symm)
  · intro h e f hef hcolour
    exact h (colour e) (by rfl) hcolour.symm hef

@[simp] theorem oneTwoRadius_zero (k : ℕ) :
    oneTwoRadius k (0 : Fin (k + 1)) = 1 := by
  simp [oneTwoRadius]

theorem oneTwoRadius_ne_zero {k : ℕ} {i : Fin (k + 1)} (hi : i ≠ 0) :
    oneTwoRadius k i = 2 := by
  simp [oneTwoRadius, hi]

/-- The matching colour class of a `(1,2^k)`-colouring. -/
theorem IsPackingEdgeColoring.matchingClass {k : ℕ}
    {colour : G.edgeSet → Fin (k + 1)}
    (h : IsPackingEdgeColoring G (oneTwoRadius k) colour) :
    IsEdgePacking G 1 {e | colour e = 0} := by
  rw [isPackingEdgeColoring_iff_colourClasses] at h
  simpa using h 0

/-- Every nonzero colour class of a `(1,2^k)`-colouring is an induced
matching, expressed as a radius-two edge packing. -/
theorem IsPackingEdgeColoring.inducedClass {k : ℕ}
    {colour : G.edgeSet → Fin (k + 1)}
    (h : IsPackingEdgeColoring G (oneTwoRadius k) colour)
    {i : Fin (k + 1)} (hi : i ≠ 0) :
    IsEdgePacking G 2 {e | colour e = i} := by
  rw [isPackingEdgeColoring_iff_colourClasses] at h
  simpa [oneTwoRadius_ne_zero hi] using h i

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- A finite simple graph is subcubic when every vertex has degree at most
three. -/
def IsSubcubic : Prop := ∀ v, G.degree v ≤ 3

omit [DecidableEq V] in
theorem isSubcubic_iff_maxDegree_le :
    IsSubcubic G ↔ G.maxDegree ≤ 3 := by
  constructor
  · exact fun h ↦ maxDegree_le_of_forall_degree_le _ _ h
  · exact fun h v ↦ (degree_le_maxDegree G v).trans h

/-- The paper's maximum-average-degree hypothesis, written without division:
every nonempty induced subgraph on a vertex set `S` has
`q * 2|E(G[S])| < p * |S|`.  This is `mad(G) < p/q`. -/
def MaximumAverageDegreeLT (p q : ℕ) : Prop :=
  ∀ S : Finset V, S.Nonempty →
    q * (2 * (G.induce (S : Set V)).edgeFinset.card) < p * S.card

end Finite

end

end LeanCo.PackingEdgeColoring
