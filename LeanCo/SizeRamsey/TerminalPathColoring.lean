import LeanCo.SizeRamsey.LowDegreeEdgeColoring
import LeanCo.SizeRamsey.PathLowerBound
import LeanCo.SizeRamsey.ColoringSplit

/-!
# Terminal path-avoiding colourings

This file packages the two deterministic terminal steps used by the BLS
iteration.  A bounded-degree graph is finished by the coarse line-graph
colouring.  In the general case, the star-type cleanup is coloured first and
its bounded-degree remainder is finished in the same way; `ColoringSplit`
then combines the two palettes.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open SimpleGraph

noncomputable section

universe u w

variable {V : Type u} {W : Type w}

/-! ## Restricting an avoiding colouring -/

/-- Pulling an edge colouring back along a spanning-subgraph inclusion only
shrinks each colour graph. -/
theorem terminal_labelGraph_pullback_ofLE_le
    {G' G : SimpleGraph V} (h : G' ≤ G)
    {K : Type*} (C : G.EdgeLabeling K) (k : K) :
    (C.pullback (SimpleGraph.Hom.ofLE h)).labelGraph k ≤ C.labelGraph k := by
  intro x y hxy
  rw [EdgeLabeling.labelGraph_adj] at hxy ⊢
  obtain ⟨hG', hk⟩ := hxy
  refine ⟨h hG', ?_⟩
  let e' : G'.edgeSet := ⟨s(x, y), hG'⟩
  let e : G.edgeSet := ⟨s(x, y), h hG'⟩
  have hk' : C ((SimpleGraph.Hom.ofLE h).mapEdgeSet e') = k := by
    simpa only [EdgeLabeling.pullback_apply, e'] using hk
  have hedge : (SimpleGraph.Hom.ofLE h).mapEdgeSet e' = e := by
    apply Subtype.ext
    simp [SimpleGraph.Hom.mapEdgeSet, e', e]
  have hCe : C e = k := by
    rw [← hedge]
    exact hk'
  simpa only [e] using hCe

/-- Avoidance is inherited by every spanning subgraph. -/
theorem terminal_avoids_pullback_ofLE
    {F : SimpleGraph W} {G' G : SimpleGraph V} (h : G' ≤ G)
    {K : Type*} (C : G.EdgeLabeling K)
    (hC : AvoidsMonochromaticCopy F C) :
    AvoidsMonochromaticCopy F
      (C.pullback (SimpleGraph.Hom.ofLE h)) := by
  intro k hcopy
  exact hC k (hcopy.trans_le (terminal_labelGraph_pullback_ofLE_le h C k))

/-! ## Direct bounded-degree terminal step -/

/-- A finite graph of maximum degree bounded pointwise by `D` has a
`(2D+1)`-edge-colouring avoiding every path on at least three vertices. -/
theorem exists_terminalPathColoring_of_degree_le
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D n : ℕ)
    (hn : 3 ≤ n) (hdegree : ∀ v, G.degree v ≤ D) :
    ∃ C : G.EdgeLabeling (Fin (2 * D + 1)),
      AvoidsMonochromaticCopy (pathGraph n) C :=
  exists_edgeLabeling_fin_two_mul_add_one_avoids_pathGraph
    G D n hdegree hn

/-- Maximum-degree formulation of the direct terminal step. -/
theorem exists_terminalPathColoring_of_maxDegree_le
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D n : ℕ)
    (hn : 3 ≤ n) (hmax : G.maxDegree ≤ D) :
    ∃ C : G.EdgeLabeling (Fin (2 * D + 1)),
      AvoidsMonochromaticCopy (pathGraph n) C := by
  apply exists_terminalPathColoring_of_degree_le G D n hn
  intro v
  exact (G.degree_le_maxDegree v).trans hmax

/-- Exact maximum-degree palette wrapper. -/
theorem exists_terminalPathColoring_maxDegree
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ)
    (hn : 3 ≤ n) :
    ∃ C : G.EdgeLabeling (Fin (2 * G.maxDegree + 1)),
      AvoidsMonochromaticCopy (pathGraph n) C :=
  exists_terminalPathColoring_of_maxDegree_le G G.maxDegree n hn le_rfl

/-! ## Star cleanup followed by the bounded-degree terminal step -/

/-- The complement of the remainder returned by the star decomposition lies
inside its star-coloured part.  Only the exact union identity is needed. -/
theorem sdiff_le_left_of_eq_sup
    {G H R : SimpleGraph V} (hsplit : G = H ⊔ R) : G \ R ≤ H := by
  intro x y hxy
  have hout := (SimpleGraph.sdiff_adj G R x y).mp hxy
  have hcases : H.Adj x y ∨ R.Adj x y := by
    have hadj := congrArg (fun Q : SimpleGraph V ↦ Q.Adj x y) hsplit
    simpa only [SimpleGraph.sup_adj] using hadj.mp hout.1
  exact hcases.resolve_right hout.2

/-- Terminal cleanup interface: use `s` colours on the star part and
`2D+1` colours on the bounded-degree remainder. -/
theorem exists_terminalPathColoring_after_star_cleanup
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {s n D : ℕ} (hs : 0 < s) (hn : 12 ≤ n)
    (hquotient : 8 * edgeCount G / (n * s) ≤ D) :
    ∃ C : G.EdgeLabeling (Fin (s + (2 * D + 1))),
      AvoidsMonochromaticCopy (pathGraph n) C := by
  obtain ⟨H, R, _hHG, hRG, hsplit, hRdegree, Cstar, hCstar⟩ :=
    exists_starTypeDecomposition G hs hn
  letI : DecidableRel R.Adj := Classical.decRel _
  have hdegree : ∀ v, R.degree v ≤ D := by
    intro v
    have hv := hRdegree v
    rw [Nat.card_eq_fintype_card, R.card_neighborSet_eq_degree] at hv
    exact hv.trans hquotient
  obtain ⟨Cres, hCres⟩ :=
    exists_terminalPathColoring_of_degree_le R D n (by omega) hdegree
  have hdiff : G \ R ≤ H := sdiff_le_left_of_eq_sup hsplit
  let Cleft : (G \ R).EdgeLabeling (Fin s) :=
    Cstar.pullback (SimpleGraph.Hom.ofLE hdiff)
  have hCleft : AvoidsMonochromaticCopy (pathGraph n) Cleft :=
    terminal_avoids_pullback_ofLE hdiff Cstar hCstar
  exact exists_path_avoidingColoring_of_split
    (G := G) (R := R) (a := s) (b := 2 * D + 1)
      (n := n) (r := s + (2 * D + 1)) hRG (by omega)
      Cleft hCleft Cres hCres le_rfl

/-- Canonical cleanup bound obtained by taking `D` to be the quotient supplied
by the star decomposition itself. -/
theorem exists_terminalPathColoring_after_star_cleanup_exact
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {s n : ℕ} (hs : 0 < s) (hn : 12 ≤ n) :
    ∃ C : G.EdgeLabeling
        (Fin (s + (2 * (8 * edgeCount G / (n * s)) + 1))),
      AvoidsMonochromaticCopy (pathGraph n) C :=
  exists_terminalPathColoring_after_star_cleanup G hs hn le_rfl

/-- Maximum-degree-sized palette wrapper for the cleanup interface. -/
theorem exists_terminalPathColoring_after_star_cleanup_maxDegree
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {s n : ℕ} (hs : 0 < s) (hn : 12 ≤ n)
    (hquotient : 8 * edgeCount G / (n * s) ≤ G.maxDegree) :
    ∃ C : G.EdgeLabeling (Fin (s + (2 * G.maxDegree + 1))),
      AvoidsMonochromaticCopy (pathGraph n) C :=
  exists_terminalPathColoring_after_star_cleanup G hs hn hquotient

end

end LeanCo.SizeRamsey
