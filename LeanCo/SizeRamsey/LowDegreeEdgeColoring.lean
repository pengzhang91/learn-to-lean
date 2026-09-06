import LeanCo.SizeRamsey.Defs
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.LineGraph

/-!
# A coarse finite edge-colouring bound

We prove the elementary greedy substitute for Vizing's theorem: a graph of
maximum degree at most `Δ` has a proper edge-labelling with `2 * Δ + 1`
labels.  Equivalently, we greedily vertex-colour its line graph.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open Finset Function SimpleGraph

noncomputable section

/-- Greedy vertex colouring on a graph whose vertex type is `Fin n`. -/
private theorem greedyColoringFin (D : ℕ) :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ v, G.degree v ≤ D) → Nonempty (G.Coloring (Fin (D + 1))) := by
  intro n
  induction n with
  | zero =>
      intro G _ hdeg
      exact ⟨Coloring.ofIsEmpty⟩
  | succ n ih =>
      intro G _ hdeg
      classical
      let emb : Fin n ↪ Fin (n + 1) :=
        ⟨Fin.castSucc, Fin.castSucc_injective n⟩
      let H : SimpleGraph (Fin n) := G.comap emb
      have hHdeg : ∀ v, H.degree v ≤ D := by
        intro v
        have hle : H.degree v ≤ G.degree (emb v) := by
          have hle' := (SimpleGraph.Embedding.comap emb G).toCopy.degree_le v
          change H.degree v ≤
            G.degree ((SimpleGraph.Embedding.comap emb G).toCopy v) at hle'
          exact hle'
        exact hle.trans (hdeg (emb v))
      obtain ⟨C⟩ := ih H hHdeg
      let N : Finset (Fin n) :=
        Finset.univ.filter fun v ↦ G.Adj v.castSucc (Fin.last n)
      let used : Finset (Fin (D + 1)) := N.image C
      have hNcard : N.card ≤ G.degree (Fin.last n) := by
        calc
          N.card = (N.image Fin.castSucc).card := by
            rw [Finset.card_image_of_injective N (Fin.castSucc_injective n)]
          _ ≤ (G.neighborFinset (Fin.last n)).card := by
            apply Finset.card_le_card
            intro v hv
            rw [Finset.mem_image] at hv
            obtain ⟨u, hu, rfl⟩ := hv
            rw [SimpleGraph.mem_neighborFinset]
            exact ((Finset.mem_filter.mp hu).2).symm
          _ = G.degree (Fin.last n) := rfl
      have hused : used.card ≤ D := by
        exact (Finset.card_image_le.trans hNcard).trans (hdeg (Fin.last n))
      have husedlt : used.card <
          (Finset.univ : Finset (Fin (D + 1))).card := by
        simpa using Nat.lt_succ_of_le hused
      obtain ⟨c, _hcuniv, hc⟩ :=
        Finset.exists_mem_notMem_of_card_lt_card husedlt
      refine ⟨Coloring.mk (Fin.lastCases c C) ?_⟩
      intro x y hxy
      induction x using Fin.lastCases with
      | last =>
          induction y using Fin.lastCases with
          | last => exact (hxy.ne rfl).elim
          | cast y =>
              simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
              intro hcy
              apply hc
              simp only [used, Finset.mem_image]
              refine ⟨y, ?_, hcy.symm⟩
              simp only [N, Finset.mem_filter, Finset.mem_univ, true_and]
              exact hxy.symm
      | cast x =>
          induction y using Fin.lastCases with
          | last =>
              simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
              intro hxc
              apply hc
              simp only [used, Finset.mem_image]
              refine ⟨x, ?_, hxc⟩
              simp only [N, Finset.mem_filter, Finset.mem_univ, true_and]
              exact hxy
          | cast y =>
              simp only [Fin.lastCases_castSucc]
              apply C.valid
              exact hxy

/-- The usual finite greedy bound: maximum degree `D` needs at most `D+1`
vertex colours. -/
theorem exists_vertexColoring_of_degree_le
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (D : ℕ) (hdeg : ∀ v, G.degree v ≤ D) :
    Nonempty (G.Coloring (Fin (D + 1))) := by
  classical
  let H : SimpleGraph (Fin (Fintype.card V)) := G.overFin rfl
  let e : G ≃g H := G.overFinIso rfl
  have hHdeg : ∀ v, H.degree v ≤ D := by
    intro v
    have h := hdeg (e.symm v)
    have heq := e.degree_eq (e.symm v)
    rw [e.apply_symm_apply] at heq
    rw [heq]
    exact h
  obtain ⟨C⟩ := greedyColoringFin D (Fintype.card V) H hHdeg
  exact ⟨C.comp e.toHom⟩

/-- A vertex of the line graph corresponding to `uv` has at most the sum
of the degrees of `u` and `v`.  The harmless overcount includes `uv`
itself twice. -/
theorem lineGraph_degree_le_two_mul
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel G.lineGraph.Adj] (Δ : ℕ)
    (hdeg : ∀ v, G.degree v ≤ Δ) (e : G.edgeSet) :
    G.lineGraph.degree e ≤ 2 * Δ := by
  classical
  rcases e with ⟨⟨u, v⟩, huv⟩
  let e : G.edgeSet := ⟨s(u, v), huv⟩
  let N : Finset G.edgeSet := G.lineGraph.neighborFinset e
  have hsubset : N.image Subtype.val ⊆
      G.incidenceFinset u ∪ G.incidenceFinset v := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨f, hfN, rfl⟩ := hz
    have hadj : G.lineGraph.Adj e f := by
      simpa only [N, SimpleGraph.mem_neighborFinset] using hfN
    obtain ⟨_hne, w, hwe, hwf⟩ :=
      SimpleGraph.lineGraph_adj_iff_exists.mp hadj
    change w ∈ s(u, v) at hwe
    have hwe' : w = u ∨ w = v := Sym2.mem_iff'.mp hwe
    rw [Finset.mem_union]
    rcases hwe' with rfl | rfl
    · left
      rw [G.mem_incidenceFinset, G.edge_mem_incidenceSet_iff]
      exact hwf
    · right
      rw [G.mem_incidenceFinset, G.edge_mem_incidenceSet_iff]
      exact hwf
  calc
    G.lineGraph.degree e = N.card := rfl
    _ = (N.image Subtype.val).card := by
      symm
      exact Finset.card_image_of_injective N Subtype.val_injective
    _ ≤ (G.incidenceFinset u ∪ G.incidenceFinset v).card :=
      Finset.card_le_card hsubset
    _ ≤ (G.incidenceFinset u).card + (G.incidenceFinset v).card :=
      Finset.card_union_le _ _
    _ = G.degree u + G.degree v := by simp
    _ ≤ 2 * Δ := by
      have hu := hdeg u
      have hv := hdeg v
      omega

/-- A vertex colouring of the line graph is a proper edge labelling of the
original graph. -/
def edgeLabelingOfLineColoring
    {V K : Type*} {G : SimpleGraph V}
    (C : G.lineGraph.Coloring K) : G.EdgeLabeling K :=
  fun e ↦ C e

/-- Every colour class of the edge labelling induced by a line-graph
colouring is a matching, expressed as exclusion of `pathGraph 3`. -/
theorem pathGraph_three_free_labelGraph_of_lineColoring
    {V K : Type*} {G : SimpleGraph V}
    (C : G.lineGraph.Coloring K) (color : K) :
    (pathGraph 3).Free ((edgeLabelingOfLineColoring C).labelGraph color) := by
  intro hcopy
  obtain ⟨φ⟩ := hcopy
  let a : Fin 3 := ⟨0, by omega⟩
  let b : Fin 3 := ⟨1, by omega⟩
  let c : Fin 3 := ⟨2, by omega⟩
  have hab : (pathGraph 3).Adj a b := by
    simp [a, b, pathGraph_adj]
  have hbc : (pathGraph 3).Adj b c := by
    simp [b, c, pathGraph_adj]
  have hLabAB := φ.toHom.map_adj hab
  have hLabBC := φ.toHom.map_adj hbc
  rw [EdgeLabeling.labelGraph_adj] at hLabAB hLabBC
  obtain ⟨hGab, hcolAB⟩ := hLabAB
  obtain ⟨hGbc, hcolBC⟩ := hLabBC
  let eab : G.edgeSet := ⟨s(φ a, φ b), hGab⟩
  let ebc : G.edgeSet := ⟨s(φ b, φ c), hGbc⟩
  have hene : eab ≠ ebc := by
    intro heq
    have hsym : s(φ a, φ b) = s(φ b, φ c) :=
      congrArg Subtype.val heq
    rw [Sym2.eq_iff] at hsym
    rcases hsym with h | h
    · have habEq : a = b := φ.injective h.1
      simp [a, b] at habEq
    · have hacEq : a = c := φ.injective h.1
      simp [a, c] at hacEq
  have hline : G.lineGraph.Adj eab ebc :=
    SimpleGraph.lineGraph_adj_iff_exists.mpr
      ⟨hene, φ b, Sym2.mem_mk_right _ _, Sym2.mem_mk_left _ _⟩
  have hne := C.valid hline
  apply hne
  change C eab = color at hcolAB
  change C ebc = color at hcolBC
  exact hcolAB.trans hcolBC.symm

/-- The first three vertices embed into every path on at least three vertices. -/
def pathGraphThreeEmbedding (n : ℕ) (h : 3 ≤ n) :
    pathGraph 3 ↪g pathGraph n where
  toFun v := ⟨v, v.2.trans_le h⟩
  inj' := by
    intro v w hvw
    have hval : v.val = w.val :=
      congrArg (fun z : Fin n ↦ z.val) hvw
    exact Fin.ext hval
  map_rel_iff' := by simp [pathGraph]

/-- Excluding a three-vertex path excludes every longer path. -/
theorem pathGraph_free_of_three_le
    {V : Type*} {G : SimpleGraph V} {n : ℕ} (hn : 3 ≤ n)
    (hthree : (pathGraph 3).Free G) : (pathGraph n).Free G := by
  intro hncopy
  apply hthree
  exact (pathGraphThreeEmbedding n hn).isContained.trans hncopy

/-- A finite graph of maximum degree at most `Δ` has an edge labelling by
`2 * Δ + 1` labels whose colour classes are matchings (and hence contain no
three-vertex path). -/
theorem exists_edgeLabeling_fin_two_mul_add_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ)
    (hdeg : ∀ v, G.degree v ≤ Δ) :
    ∃ C : G.EdgeLabeling (Fin (2 * Δ + 1)),
      ∀ color, (pathGraph 3).Free (C.labelGraph color) := by
  classical
  letI : DecidableRel G.lineGraph.Adj := Classical.decRel _
  have hline : ∀ e, G.lineGraph.degree e ≤ 2 * Δ :=
    lineGraph_degree_le_two_mul G Δ hdeg
  obtain ⟨C⟩ := exists_vertexColoring_of_degree_le G.lineGraph (2 * Δ) hline
  refine ⟨edgeLabelingOfLineColoring C, ?_⟩
  exact pathGraph_three_free_labelGraph_of_lineColoring C

/-- Uniform long-path wrapper for the coarse edge-colouring bound. -/
theorem exists_edgeLabeling_fin_two_mul_add_one_avoids_pathGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Δ n : ℕ)
    (hdeg : ∀ v, G.degree v ≤ Δ) (hn : 3 ≤ n) :
    ∃ C : G.EdgeLabeling (Fin (2 * Δ + 1)),
      AvoidsMonochromaticCopy (pathGraph n) C := by
  obtain ⟨C, hC⟩ := exists_edgeLabeling_fin_two_mul_add_one G Δ hdeg
  exact ⟨C, fun color ↦ pathGraph_free_of_three_le hn (hC color)⟩

end

end LeanCo.SizeRamsey
