import LeanCo.HypercubeTuran.Defs
import Mathlib.Tactic

/-!
# From an avoiding two-colouring to a half-density witness

The larger of the two colour classes contains at least half of all cube
edges, and is free of the forbidden graph.
-/

open scoped SimpleGraph

namespace LeanCo.HypercubeTuran

open Finset SimpleGraph

universe u v

variable {V : Type u} [Fintype V] [DecidableEq V]

lemma card_edgeFinset_eq_edgeSet_ncard (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    #G.edgeFinset = G.edgeSet.ncard := by
  rw [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card']

lemma labelGraph_zero_sup_one {G : SimpleGraph V} [DecidableRel G.Adj]
    (C : G.EdgeLabeling (Fin 2)) :
    C.labelGraph 0 ⊔ C.labelGraph 1 = G := by
  ext x y
  constructor
  · intro hxy
    rcases hxy with hxy | hxy
    · exact C.labelGraph_le hxy
    · exact C.labelGraph_le hxy
  · intro hxy
    have hval : (C.get x y hxy).val = 0 ∨ (C.get x y hxy).val = 1 := by
      have hlt := (C.get x y hxy).isLt
      omega
    have hc : C.get x y hxy = 0 ∨ C.get x y hxy = 1 := by
      rcases hval with hval | hval
      · exact Or.inl (Fin.ext hval)
      · exact Or.inr (Fin.ext hval)
    rcases hc with hc | hc
    · exact Or.inl ((C.labelGraph_adj x y).mpr ⟨hxy, hc⟩)
    · exact Or.inr ((C.labelGraph_adj x y).mpr ⟨hxy, hc⟩)

lemma card_edgeFinset_eq_add_labelGraph (G : SimpleGraph V)
    [DecidableRel G.Adj] (C : G.EdgeLabeling (Fin 2)) :
    #G.edgeFinset =
      #(C.labelGraph 0).edgeFinset + #(C.labelGraph 1).edgeFinset := by
  classical
  have hdisGraph : Disjoint (C.labelGraph 0) (C.labelGraph 1) :=
    C.pairwise_disjoint_labelGraph (by decide)
  have hdis : Disjoint (C.labelGraph 0).edgeFinset
      (C.labelGraph 1).edgeFinset := SimpleGraph.disjoint_edgeFinset.mpr hdisGraph
  have hunion :
      (C.labelGraph 0).edgeFinset ∪ (C.labelGraph 1).edgeFinset =
        G.edgeFinset := by
    have hedge :
        (C.labelGraph 0).edgeSet ∪ (C.labelGraph 1).edgeSet = G.edgeSet := by
      rw [← SimpleGraph.edgeSet_sup, labelGraph_zero_sup_one C]
    ext e
    simpa only [Finset.mem_union, SimpleGraph.mem_edgeFinset,
      Set.mem_union] using Set.ext_iff.mp hedge e
  rw [← hunion, Finset.card_union_of_disjoint hdis]

/-- Any avoiding two-colouring supplies an `H`-free subgraph containing at
least half of the host graph's edges. -/
theorem half_witness_of_avoiding_twoColoring
    {W : Type v} (H : SimpleGraph W) (G : SimpleGraph V)
    [DecidableRel G.Adj] (C : G.EdgeLabeling (Fin 2))
    (havoid : AvoidsMonochromaticCopy H C) :
    ∃ K : SimpleGraph V, ∃ _ : DecidableRel K.Adj,
      K ≤ G ∧ H.Free K ∧ #G.edgeFinset ≤ 2 * #K.edgeFinset := by
  have hcard := card_edgeFinset_eq_add_labelGraph G C
  rcases le_total (#(C.labelGraph 0).edgeFinset)
      (#(C.labelGraph 1).edgeFinset) with h01 | h10
  · refine ⟨C.labelGraph 1, inferInstance, C.labelGraph_le, havoid 1, ?_⟩
    omega
  · refine ⟨C.labelGraph 0, inferInstance, C.labelGraph_le, havoid 0, ?_⟩
    omega

/-- Specialization to the finite hypercube. -/
theorem hasHalfCubeWitness_of_hasAvoidingTwoColoring
    {W : Type u} (H : SimpleGraph W) {n : ℕ}
    (h : HasAvoidingTwoColoring H n) : HasHalfCubeWitness H n := by
  classical
  obtain ⟨C, havoid⟩ := h
  obtain ⟨K, _instK, hKG, hfree, hhalf⟩ :=
    half_witness_of_avoiding_twoColoring H (hypercubeGraph (Fin n)) C havoid
  refine ⟨K, hKG, hfree, ?_⟩
  rw [cubeEdgeCount, ← card_edgeFinset_eq_edgeSet_ncard
    (hypercubeGraph (Fin n)), ← card_edgeFinset_eq_edgeSet_ncard K]
  exact hhalf

open Classical in
lemma edgeNcard_le_cubeExtremalNumber
    {W : Type u} (H : SimpleGraph W) {n : ℕ}
    (K : SimpleGraph (Finset (Fin n)))
    (hK : K ≤ hypercubeGraph (Fin n)) (hfree : H.Free K) :
    K.edgeSet.ncard ≤ cubeExtremalNumber H n := by
  rw [cubeExtremalNumber]
  apply @Finset.le_sup _ _ _ _
    (Finset.univ.filter fun G : SimpleGraph (Finset (Fin n)) =>
      G ≤ hypercubeGraph (Fin n) ∧ H.Free G)
    (fun G => G.edgeSet.ncard) K
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hK, hfree⟩

/-- Concrete half-edge witnesses imply the pointwise real lower-density
statement used as the finite form of cube Turan density. -/
theorem hasCubeTuranLowerBound_half_of_witnesses
    {W : Type u} (H : SimpleGraph W)
    (h : ∀ n : ℕ, HasHalfCubeWitness H n) :
    HasCubeTuranLowerBound H (1 / 2 : ℝ) := by
  intro n
  obtain ⟨K, hKG, hfree, hhalf⟩ := h n
  have hKext := edgeNcard_le_cubeExtremalNumber H K hKG hfree
  have hNat : cubeEdgeCount n ≤ 2 * cubeExtremalNumber H n :=
    hhalf.trans (Nat.mul_le_mul_left 2 hKext)
  have hReal : (cubeEdgeCount n : ℝ) ≤
      2 * (cubeExtremalNumber H n : ℝ) := by
    exact_mod_cast hNat
  norm_num
  linarith

/-- Avoiding two-colourings in every dimension imply the paper's finite
half-density conclusion. -/
theorem hasCubeTuranLowerBound_half_of_avoiding
    {W : Type u} (H : SimpleGraph W)
    (h : ∀ n : ℕ, HasAvoidingTwoColoring H n) :
    HasCubeTuranLowerBound H (1 / 2 : ℝ) :=
  hasCubeTuranLowerBound_half_of_witnesses H fun n =>
    hasHalfCubeWitness_of_hasAvoidingTwoColoring H (h n)

end LeanCo.HypercubeTuran
