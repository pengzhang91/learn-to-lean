import LeanCo.SizeRamsey.VizingTypeRefinement

/-!
# Restricting the high core to its actual vertex set

`highCoreGraph G Δ` is a spanning graph on the ambient vertex type and hence
retains low vertices as isolates.  The graph used for recursive arguments is
instead the induced graph on the finite set of high vertices.  This file
relates the two representations, lifts avoiding colourings from the induced
subtype to the spanning core, and glues that colouring to the low-degree
part from `VizingTypeRefinement`.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open Finset SimpleGraph

noncomputable section

universe u w

variable {V : Type u} {K : Type w}

/-- The high core with its vertex type restricted to the vertices that it
actually retains. -/
def highCoreRestriction
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) :
    SimpleGraph ↥(highCoreVertexFinset G Δ) :=
  G.induce (↑(highCoreVertexFinset G Δ) : Set V)

/-- On high vertices, adjacency in the induced restriction is exactly
adjacency in the spanning high-core graph. -/
@[simp] theorem highCoreRestriction_adj_iff_highCoreGraph
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ)
    {x y : ↥(highCoreVertexFinset G Δ)} :
    (highCoreRestriction G Δ).Adj x y ↔
      (highCoreGraph G Δ).Adj x.1 y.1 := by
  simp only [highCoreRestriction, SimpleGraph.induce_adj,
    highCoreGraph_adj_iff_mem]
  exact ⟨fun h => ⟨h, x.2, y.2⟩, fun h => h.1⟩

/-- `Subtype.val` embeds the restricted core in the spanning core and
reflects adjacency. -/
def highCoreRestrictionEmbedding
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) :
    highCoreRestriction G Δ ↪g highCoreGraph G Δ where
  toFun := Subtype.val
  inj' := Subtype.val_injective
  map_rel_iff' := (highCoreRestriction_adj_iff_highCoreGraph G Δ).symm

/-- The restricted vertex type has exactly the cardinality of the defining
high-vertex finset. -/
@[simp] theorem card_highCoreRestriction_vertices
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) :
    Fintype.card ↥(highCoreVertexFinset G Δ) =
      (highCoreVertexFinset G Δ).card := by
  exact Fintype.card_coe _

/-- Lift an edge colouring from the induced subtype to the spanning high
core.  Every edge of the spanning core has high endpoints, so its colour is
read from the corresponding subtype edge. -/
def liftHighCoreColoring
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ)
    (C : (highCoreRestriction G Δ).EdgeLabeling K) :
    (highCoreGraph G Δ).EdgeLabeling K := by
  refine EdgeLabeling.mk (fun x y hxy =>
    C.get
      ⟨x, (highCoreGraph_adj_iff_mem G Δ).mp hxy |>.2.1⟩
      ⟨y, (highCoreGraph_adj_iff_mem G Δ).mp hxy |>.2.2⟩
      ((highCoreRestriction_adj_iff_highCoreGraph G Δ).mpr hxy)) ?_
  intro x y hxy
  exact C.get_comm _ _ _

/-- Pointwise description of the lifted colouring, independent of the proof
terms witnessing membership in the high set. -/
theorem liftHighCoreColoring_get
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ)
    (C : (highCoreRestriction G Δ).EdgeLabeling K)
    (x y : V) (hxy : (highCoreGraph G Δ).Adj x y)
    (hx : x ∈ highCoreVertexFinset G Δ)
    (hy : y ∈ highCoreVertexFinset G Δ) :
    (liftHighCoreColoring G Δ C).get x y hxy =
      C.get ⟨x, hx⟩ ⟨y, hy⟩
        ((highCoreRestriction_adj_iff_highCoreGraph G Δ).mpr hxy) := by
  rfl

/-- For paths with an edge, lifting from the induced subtype to the spanning
core preserves avoidance.  The lower bound `2 ≤ n` is necessary because a
one-vertex path can use an isolated ambient vertex. -/
theorem liftHighCoreColoring_avoids_pathGraph
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ)
    {n : ℕ} (hn : 2 ≤ n)
    (C : (highCoreRestriction G Δ).EdgeLabeling K)
    (hC : AvoidsMonochromaticCopy (pathGraph n) C) :
    AvoidsMonochromaticCopy (pathGraph n)
      (liftHighCoreColoring G Δ C) := by
  intro colour hcopy
  obtain ⟨f⟩ := hcopy
  letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  have hall : ∀ x : Fin n,
      f x ∈ highCoreVertexFinset G Δ := by
    intro x
    have hx : x ∈ (pathGraph n).support := by
      rw [(pathGraph_preconnected n).support_eq_univ]
      trivial
    obtain ⟨y, hxy⟩ := (pathGraph n).mem_support.mp hx
    have hlift := f.toHom.map_adj hxy
    have hhigh : (highCoreGraph G Δ).Adj (f x) (f y) :=
      (liftHighCoreColoring G Δ C).labelGraph_le hlift
    exact (highCoreGraph_adj_iff_mem G Δ).mp hhigh |>.2.1
  apply hC colour
  refine ⟨{
    toHom := {
      toFun := fun x => ⟨f x, hall x⟩
      map_rel' := ?_ }
    injective' := ?_ }⟩
  · intro x y hxy
    have hlift := f.toHom.map_adj hxy
    rw [EdgeLabeling.labelGraph_adj] at hlift ⊢
    obtain ⟨hhigh, hcolour⟩ := hlift
    let hrestricted : (highCoreRestriction G Δ).Adj
        (⟨f x, hall x⟩ : ↥(highCoreVertexFinset G Δ))
        (⟨f y, hall y⟩ : ↥(highCoreVertexFinset G Δ)) :=
      (highCoreRestriction_adj_iff_highCoreGraph G Δ).mpr hhigh
    refine ⟨hrestricted, ?_⟩
    change C.get ⟨f x, hall x⟩ ⟨f y, hall y⟩ hrestricted = colour
    rw [← liftHighCoreColoring_get G Δ C (f x) (f y)
      hhigh (hall x) (hall y)]
    exact hcolour
  · intro x y hxy
    apply f.injective
    exact congrArg Subtype.val hxy

/-! ## Gluing the restricted core to the low-degree part -/

/-- The two pieces in the final low-degree/high-core cover. -/
def highCoreSplitPiece
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) :
    Bool → SimpleGraph V
  | false => lowDegreePart G Δ
  | true => highCoreGraph G Δ

/-- Palette sizes of the low-degree and high-core pieces. -/
def highCoreSplitBudget (Δ k : ℕ) : Bool → ℕ
  | false => 3 * Δ + 2
  | true => k

@[simp] theorem sum_highCoreSplitBudget (Δ k : ℕ) :
    ∑ i, highCoreSplitBudget Δ k i = (3 * Δ + 2) + k := by
  simp [highCoreSplitBudget, Nat.add_comm]

theorem highCoreSplitPiece_le
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) :
    ∀ i, highCoreSplitPiece G Δ i ≤ G := by
  intro i
  cases i
  · exact sup_le (lowLowGraph_le G Δ) (lowHighGraph_le G Δ)
  · exact highCoreGraph_le G Δ

theorem highCoreSplitPiece_covers
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) :
    EdgesCoveredBy G (highCoreSplitPiece G Δ) := by
  intro e he
  have he' : e ∈ (lowDegreePart G Δ ⊔ highCoreGraph G Δ).edgeSet := by
    rw [lowDegreePart_sup_highCore G Δ]
    exact he
  rw [SimpleGraph.edgeSet_sup] at he'
  rcases he' with hlow | hhigh
  · exact ⟨false, hlow⟩
  · exact ⟨true, hhigh⟩

/-- Given an avoiding colouring of the restricted high core, glue it to the
explicit low-degree colouring. -/
theorem exists_path_avoidingColoring_of_highCoreRestriction
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (Δ n k : ℕ) (hn : 4 ≤ n)
    (Ccore : (highCoreRestriction G Δ).EdgeLabeling (Fin k))
    (hCcore : AvoidsMonochromaticCopy (pathGraph n) Ccore) :
    ∃ C : G.EdgeLabeling (Fin ((3 * Δ + 2) + k)),
      AvoidsMonochromaticCopy (pathGraph n) C := by
  obtain ⟨Clow, hClow⟩ :=
    exists_lowDegreePart_path_avoidingColoring G Δ n hn
  let Chigh := liftHighCoreColoring G Δ Ccore
  have hChigh : AvoidsMonochromaticCopy (pathGraph n) Chigh :=
    liftHighCoreColoring_avoids_pathGraph G Δ (by omega) Ccore hCcore
  apply exists_fin_path_avoidingColoring_of_cover
    G (highCoreSplitPiece G Δ) (highCoreSplitBudget Δ k) (by omega)
  · exact highCoreSplitPiece_le G Δ
  · exact highCoreSplitPiece_covers G Δ
  · intro i
    cases i
    · exact ⟨Clow, hClow⟩
    · exact ⟨Chigh, hChigh⟩
  · exact le_of_eq (sum_highCoreSplitBudget Δ k)

/-- Bundled paper-facing interface: a `k`-colour avoiding colouring of the
restricted core produces a `(3Δ+2)+k`-colour avoiding colouring of `G`, while
also exposing the exact restricted vertex count and the handshaking bound. -/
theorem exists_bundled_highCoreRestriction_coloring
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (Δ n k : ℕ) (hn : 4 ≤ n)
    (hcore : ∃ Ccore : (highCoreRestriction G Δ).EdgeLabeling (Fin k),
      AvoidsMonochromaticCopy (pathGraph n) Ccore) :
    ∃ C : G.EdgeLabeling (Fin ((3 * Δ + 2) + k)),
      AvoidsMonochromaticCopy (pathGraph n) C ∧
      Fintype.card ↥(highCoreVertexFinset G Δ) =
        (highCoreVertexFinset G Δ).card ∧
      (Δ + 1) * (highCoreVertexFinset G Δ).card ≤
        2 * edgeCount G := by
  obtain ⟨Ccore, hCcore⟩ := hcore
  obtain ⟨C, hC⟩ := exists_path_avoidingColoring_of_highCoreRestriction
    G Δ n k hn Ccore hCcore
  exact ⟨C, hC, card_highCoreRestriction_vertices G Δ,
    highCoreVertexFinset_card_bound G Δ⟩

end

end LeanCo.SizeRamsey
