import LeanCo.SizeRamsey.HighCoreRestriction
import LeanCo.SizeRamsey.ColoringSplit
import LeanCo.SizeRamsey.GraphBasics

/-!
# Initial star cleanup on the restricted high core

The first cleanup is performed after changing the vertex type to the actual
high vertices.  Lemma 2.3 (`exists_starTypeDecomposition`) colours a star
part and leaves a bounded-degree residual.  We restrict that star colouring
to `core \ R`, retain all quantitative facts needed later, and provide the
two-stage glue back to the original ambient graph.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open SimpleGraph

noncomputable section

universe u w

variable {V : Type u} {W : Type w}

/-- Restricting the vertex type to the high core cannot increase the number
of edges relative to the original graph. -/
theorem edgeCount_highCoreRestriction_le_original
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) :
    edgeCount (highCoreRestriction G Δ) ≤ edgeCount G := by
  unfold highCoreRestriction
  exact edgeCount_le_of_copy
    (Copy.induce G (↑(highCoreVertexFinset G Δ) : Set V))

/-- If `Q = H ⊔ R`, then every edge of `Q \ R` belongs to `H`. -/
private theorem initialCore_sdiff_le_left_of_eq_sup
    {Q H R : SimpleGraph W} (hsplit : Q = H ⊔ R) : Q \ R ≤ H := by
  intro x y hxy
  have hout := (SimpleGraph.sdiff_adj Q R x y).mp hxy
  have hcases : H.Adj x y ∨ R.Adj x y := by
    have hadj := congrArg (fun L : SimpleGraph W => L.Adj x y) hsplit
    simpa only [SimpleGraph.sup_adj] using hadj.mp hout.1
  exact hcases.resolve_right hout.2

/-- Avoidance is inherited when a colouring is restricted along a spanning
subgraph inclusion. -/
private theorem initialCore_avoids_pullback_ofLE
    {F : SimpleGraph W} {Q' Q : SimpleGraph V} (h : Q' ≤ Q)
    {K : Type*} (C : Q.EdgeLabeling K)
    (hC : AvoidsMonochromaticCopy F C) :
    AvoidsMonochromaticCopy F
      (C.pullback (SimpleGraph.Hom.ofLE h)) := by
  intro colour hcopy
  apply hC colour
  refine hcopy.trans_le ?_
  intro x y hxy
  rw [EdgeLabeling.labelGraph_adj] at hxy ⊢
  obtain ⟨hQ', hcolour⟩ := hxy
  refine ⟨h hQ', ?_⟩
  let e' : Q'.edgeSet := ⟨s(x, y), hQ'⟩
  let e : Q.edgeSet := ⟨s(x, y), h hQ'⟩
  have hcolour' : C ((SimpleGraph.Hom.ofLE h).mapEdgeSet e') = colour := by
    simpa only [EdgeLabeling.pullback_apply, e'] using hcolour
  have hedge : (SimpleGraph.Hom.ofLE h).mapEdgeSet e' = e := by
    apply Subtype.ext
    simp [SimpleGraph.Hom.mapEdgeSet, e', e]
  have hCe : C e = colour := by
    rw [← hedge]
    exact hcolour'
  simpa only [e] using hCe

/-- Star cleanup on the restricted high core.  Besides the residual and its
pointwise degree bound, the result retains the exact restricted vertex count
and both edge-count monotonicity facts used by the main lower-bound proof. -/
theorem exists_initialCoreCleanup
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (Δ : ℕ) {s n : ℕ} (hs : 0 < s) (hn : 12 ≤ n) :
    ∃ R : SimpleGraph ↥(highCoreVertexFinset G Δ),
      R ≤ highCoreRestriction G Δ ∧
      (∀ v, Nat.card (R.neighborSet v) ≤
        8 * edgeCount (highCoreRestriction G Δ) / (n * s)) ∧
      ∃ Cclean : (highCoreRestriction G Δ \ R).EdgeLabeling (Fin s),
        AvoidsMonochromaticCopy (pathGraph n) Cclean ∧
        Fintype.card ↥(highCoreVertexFinset G Δ) =
          (highCoreVertexFinset G Δ).card ∧
        edgeCount R ≤ edgeCount (highCoreRestriction G Δ) ∧
        edgeCount (highCoreRestriction G Δ) ≤ edgeCount G := by
  let core := highCoreRestriction G Δ
  letI : DecidableRel core.Adj := Classical.decRel _
  obtain ⟨H, R, hHcore, hRcore, hsplit, hdegree,
      Cstar, hCstar⟩ := exists_starTypeDecomposition core hs hn
  have hdiff : core \ R ≤ H :=
    initialCore_sdiff_le_left_of_eq_sup hsplit
  let Cclean : (core \ R).EdgeLabeling (Fin s) :=
    Cstar.pullback (SimpleGraph.Hom.ofLE hdiff)
  have hCclean : AvoidsMonochromaticCopy (pathGraph n) Cclean :=
    initialCore_avoids_pullback_ofLE hdiff Cstar hCstar
  have hRedges : edgeCount R ≤ edgeCount core := edgeCount_mono hRcore
  have hcoreEdges : edgeCount core ≤ edgeCount G := by
    simpa only [core] using edgeCount_highCoreRestriction_le_original G Δ
  refine ⟨R, ?_, ?_, Cclean, hCclean,
    card_highCoreRestriction_vertices G Δ, ?_, hcoreEdges⟩
  · simpa only [core] using hRcore
  · simpa only [core] using hdegree
  · simpa only [core] using hRedges

/-- Complete a fixed cleanup residual.  `ColoringSplit` first combines the
`s` cleanup colours with the `k` residual colours on the restricted core;
the high-core restriction interface then adds the `3Δ+2` low-degree colours
and lifts everything back to `G`. -/
theorem exists_path_avoidingColoring_of_completed_initialCoreCleanup
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (Δ : ℕ) {s k n : ℕ} (hn : 12 ≤ n)
    (R : SimpleGraph ↥(highCoreVertexFinset G Δ))
    (hR : R ≤ highCoreRestriction G Δ)
    (Cclean : (highCoreRestriction G Δ \ R).EdgeLabeling (Fin s))
    (hCclean : AvoidsMonochromaticCopy (pathGraph n) Cclean)
    (Cresidual : R.EdgeLabeling (Fin k))
    (hCresidual : AvoidsMonochromaticCopy (pathGraph n) Cresidual) :
    ∃ C : G.EdgeLabeling (Fin ((3 * Δ + 2) + (s + k))),
      AvoidsMonochromaticCopy (pathGraph n) C := by
  obtain ⟨Ccore, hCcore⟩ := exists_path_avoidingColoring_of_split
    (G := highCoreRestriction G Δ) (R := R)
    (a := s) (b := k) (n := n) (r := s + k)
    hR (by omega) Cclean hCclean Cresidual hCresidual le_rfl
  exact exists_path_avoidingColoring_of_highCoreRestriction
    G Δ n (s + k) (by omega) Ccore hCcore

end

end LeanCo.SizeRamsey
