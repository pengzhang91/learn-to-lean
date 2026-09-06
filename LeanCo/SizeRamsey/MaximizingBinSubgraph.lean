import LeanCo.SizeRamsey.PathLowerBound
import LeanCo.SizeRamsey.GraphBasics
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-!
# The maximizing-bin subgraph in the BLS path lower bound

This file formalizes the deterministic graph produced after one outcome of
the random partition in Beke--Li--Sahasrabudhe Lemma 4.5.  The left side is
labelled by bins.  Every vertex on the right keeps precisely the incident
edges going to a bin of maximum load.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open Finset SimpleGraph

noncomputable section

universe u

variable {V : Type u}

/-- The number of neighbours of `b` in the left side which receive label
`i`.  The equivalence `eA` gives the left side the canonical labels
`Fin a` used by the finite probability space. -/
def cutBinLoad [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {a q : Nat} (A : Finset V) (eA : Fin a ≃ A)
    (f : Fin a → Fin q) (b : V) (i : Fin q) : Nat :=
  #{j : Fin a | G.Adj (eA j) b ∧ f j = i}

/-- Maximum left-neighbour load seen from a fixed right vertex. -/
def cutMaxBinLoad [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {a q : Nat} (A : Finset V) (eA : Fin a ≃ A)
    (f : Fin a → Fin q) (b : V) : Nat :=
  (Finset.univ : Finset (Fin q)).sup (cutBinLoad G A eA f b)

/-- A deterministic choice of a maximum-load bin, with arbitrary tie
breaking. -/
def maximizingCutBin [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {a q : Nat} (hq : 0 < q) (A : Finset V) (eA : Fin a ≃ A)
    (f : Fin a → Fin q) (b : V) : Fin q :=
  Classical.choose
    (Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin q))
      ⟨⟨0, hq⟩, Finset.mem_univ _⟩
      (cutBinLoad G A eA f b))

theorem cutBinLoad_maximizingCutBin [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {a q : Nat} (hq : 0 < q) (A : Finset V) (eA : Fin a ≃ A)
    (f : Fin a → Fin q) (b : V) :
    cutBinLoad G A eA f b (maximizingCutBin G hq A eA f b) =
      cutMaxBinLoad G A eA f b := by
  have h := Classical.choose_spec
    (Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin q))
      ⟨⟨0, hq⟩, Finset.mem_univ _⟩
      (cutBinLoad G A eA f b))
  exact h.2.symm

/-- Extend the left allocation to all vertices: left vertices retain their
assigned bin and all other vertices choose a maximum-load bin. -/
def maximizingCutGroup [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {a q : Nat} (hq : 0 < q) (A : Finset V) (eA : Fin a ≃ A)
    (f : Fin a → Fin q) (x : V) : Fin q :=
  if hx : x ∈ A then f (eA.symm ⟨x, hx⟩)
  else maximizingCutBin G hq A eA f x

@[simp]
theorem maximizingCutGroup_left [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {a q : Nat} (hq : 0 < q) (A : Finset V) (eA : Fin a ≃ A)
    (f : Fin a → Fin q) (j : Fin a) :
    maximizingCutGroup G hq A eA f (eA j) = f j := by
  simp [maximizingCutGroup]

theorem maximizingCutGroup_right [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {a q : Nat} (hq : 0 < q) (A B : Finset V)
    (hAB : Disjoint A B) (eA : Fin a ≃ A)
    (f : Fin a → Fin q) {b : V} (hb : b ∈ B) :
    maximizingCutGroup G hq A eA f b =
      maximizingCutBin G hq A eA f b := by
  have hbA : b ∉ A := by
    intro hbA
    exact Finset.disjoint_left.mp hAB hbA hb
  simp [maximizingCutGroup, hbA]

/-- Keep exactly those cross edges whose endpoints receive the same group
label. -/
def maximizingBinSubgraph [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {a q : Nat} (hq : 0 < q) (A B : Finset V) (eA : Fin a ≃ A)
    (f : Fin a → Fin q) : SimpleGraph V where
  Adj x y :=
    G.Adj x y ∧
      ((x ∈ A ∧ y ∈ B) ∨ (x ∈ B ∧ y ∈ A)) ∧
      maximizingCutGroup G hq A eA f x =
        maximizingCutGroup G hq A eA f y
  symm.symm x y hxy := ⟨hxy.1.symm, hxy.2.1.elim
    (fun h ↦ Or.inr ⟨h.2, h.1⟩)
    (fun h ↦ Or.inl ⟨h.2, h.1⟩), hxy.2.2.symm⟩

@[simp]
theorem maximizingBinSubgraph_adj [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {a q : Nat} (hq : 0 < q) (A B : Finset V) (eA : Fin a ≃ A)
    (f : Fin a → Fin q) (x y : V) :
    (maximizingBinSubgraph G hq A B eA f).Adj x y ↔
      G.Adj x y ∧
        ((x ∈ A ∧ y ∈ B) ∨ (x ∈ B ∧ y ∈ A)) ∧
        maximizingCutGroup G hq A eA f x =
          maximizingCutGroup G hq A eA f y :=
  Iff.rfl

instance maximizingBinSubgraph_decidableRel [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {a q : Nat} (hq : 0 < q) (A B : Finset V) (eA : Fin a ≃ A)
    (f : Fin a → Fin q) :
    DecidableRel (maximizingBinSubgraph G hq A B eA f).Adj :=
  Classical.decRel _

theorem maximizingBinSubgraph_le [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {a q : Nat} (hq : 0 < q) (A B : Finset V) (eA : Fin a ≃ A)
    (f : Fin a → Fin q) :
    maximizingBinSubgraph G hq A B eA f ≤ G :=
  fun _ _ hxy ↦ hxy.1

theorem maximizingBinSubgraph_isBipartiteWith
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {a q : Nat} (hq : 0 < q) (A B : Finset V)
    (hAB : Disjoint A B) (eA : Fin a ≃ A)
    (f : Fin a → Fin q) :
    (maximizingBinSubgraph G hq A B eA f).IsBipartiteWith
      (↑A : Set V) (↑B : Set V) where
  disjoint := by simpa only [Finset.disjoint_coe] using hAB
  mem_of_adj := by
    intro x y hxy
    exact hxy.2.1

/-- The image of one left allocation fibre in the ambient vertex type. -/
def leftBinFiber [Fintype V] [DecidableEq V]
    {a q : Nat} (eA : Fin a ≃ V) (f : Fin a → Fin q)
    (i : Fin q) : Finset V :=
  ((Finset.univ : Finset (Fin a)).filter fun j ↦ f j = i).map
    eA.toEmbedding

/- The preceding definition is useful for standalone equivalences.  For an
actual left finset we use the codomain-subtype equivalence directly. -/
def leftBinFiberIn [Fintype V] [DecidableEq V]
    {a q : Nat} {A : Finset V} (eA : Fin a ≃ A)
    (f : Fin a → Fin q) (i : Fin q) : Finset V :=
  ((Finset.univ : Finset (Fin a)).filter fun j ↦ f j = i).map
    (eA.toEmbedding.trans (Function.Embedding.subtype _))

theorem card_leftBinFiberIn [Fintype V] [DecidableEq V]
    {a q : Nat} {A : Finset V} (eA : Fin a ≃ A)
    (f : Fin a → Fin q) (i : Fin q) :
    (leftBinFiberIn eA f i).card = binLoad f i := by
  simp [leftBinFiberIn, binLoad]

theorem mem_leftBinFiberIn_iff [Fintype V] [DecidableEq V]
    {a q : Nat} {A : Finset V} (eA : Fin a ≃ A)
    (f : Fin a → Fin q) (i : Fin q) (x : V) :
    x ∈ leftBinFiberIn eA f i ↔
      ∃ j : Fin a, (eA j : V) = x ∧ f j = i := by
  constructor
  · intro hx
    simp only [leftBinFiberIn, Finset.mem_map, Finset.mem_filter,
      Finset.mem_univ, true_and] at hx
    obtain ⟨j, hj, hjeq⟩ := hx
    exact ⟨j, hjeq, hj⟩
  · rintro ⟨j, hjeq, hj⟩
    simp only [leftBinFiberIn, Finset.mem_map, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨j, hj, hjeq⟩

/-- Safe allocations make the maximizing-bin graph `P_n`-free. -/
theorem maximizingBinSubgraph_pathFree_of_safe
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {a q n : Nat} (hq : 0 < q) (A B : Finset V)
    (eA : Fin a ≃ A) (f : Fin a → Fin q)
    (hsafe : ∀ i, 2 * binLoad f i + 1 < n) :
    (pathGraph n).Free (maximizingBinSubgraph G hq A B eA f) := by
  let group : V → Fin q := maximizingCutGroup G hq A eA f
  let S : Fin q → Finset V := fun i ↦ leftBinFiberIn eA f i
  apply pathGraph_free_of_grouped_vertexCovers
    (maximizingBinSubgraph G hq A B eA f) hq group S
  · intro x y hxy
    refine ⟨hxy.2.2, ?_⟩
    rcases hxy.2.1 with hxyAB | hxyBA
    · left
      have hxGroup : group x = f (eA.symm ⟨x, hxyAB.1⟩) := by
        simp [group, maximizingCutGroup, hxyAB.1]
      rw [mem_leftBinFiberIn_iff]
      refine ⟨eA.symm ⟨x, hxyAB.1⟩, ?_, ?_⟩
      · simp
      · exact hxGroup.symm
    · right
      have hyGroup : group y = f (eA.symm ⟨y, hxyBA.2⟩) := by
        simp [group, maximizingCutGroup, hxyBA.2]
      rw [mem_leftBinFiberIn_iff]
      refine ⟨eA.symm ⟨y, hxyBA.2⟩, ?_, ?_⟩
      · simp
      · exact hyGroup.symm
  · intro i
    dsimp only [S]
    rw [card_leftBinFiberIn]
    exact hsafe i

/-! ## Exact retained-edge count -/

/-- The kept neighbours of a right vertex, represented using the canonical
`Fin a` labels of the left side. -/
def keptLeftNeighbors [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {a q : Nat} (hq : 0 < q) (A : Finset V) (eA : Fin a ≃ A)
    (f : Fin a → Fin q) (b : V) : Finset V :=
  ((Finset.univ : Finset (Fin a)).filter fun j ↦
      G.Adj (eA j) b ∧ f j = maximizingCutBin G hq A eA f b).map
    (eA.toEmbedding.trans (Function.Embedding.subtype _))

theorem neighborFinset_maximizingBinSubgraph_right
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {a q : Nat} (hq : 0 < q) (A B : Finset V)
    (hAB : Disjoint A B) (eA : Fin a ≃ A)
    (f : Fin a → Fin q) {b : V} (hb : b ∈ B) :
    (maximizingBinSubgraph G hq A B eA f).neighborFinset b =
      keptLeftNeighbors G hq A eA f b := by
  ext x
  rw [SimpleGraph.mem_neighborFinset]
  constructor
  · intro hbx
    have hbA : b ∉ A := by
      intro hbA
      exact Finset.disjoint_left.mp hAB hbA hb
    have hxA : x ∈ A := by
      rcases hbx.2.1 with hbad | hgood
      · exact False.elim (hbA hbad.1)
      · exact hgood.2
    let j : Fin a := eA.symm ⟨x, hxA⟩
    have hej : (eA j : V) = x := by simp [j]
    have hG : G.Adj (eA j) b := by
      rw [hej]
      exact hbx.1.symm
    have hlabel : f j = maximizingCutBin G hq A eA f b := by
      have hgroupB := maximizingCutGroup_right
        G hq A B hAB eA f hb
      have hgroupJ := maximizingCutGroup_left G hq A eA f j
      have hgroup := hbx.2.2
      rw [hgroupB, ← hej, hgroupJ] at hgroup
      exact hgroup.symm
    simp only [keptLeftNeighbors, Finset.mem_map, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨j, ⟨hG, hlabel⟩, hej⟩
  · intro hx
    simp only [keptLeftNeighbors, Finset.mem_map, Finset.mem_filter,
      Finset.mem_univ, true_and] at hx
    obtain ⟨j, hj, hej⟩ := hx
    have hjA : (eA j : V) ∈ A := (eA j).prop
    have hgroupB := maximizingCutGroup_right
      G hq A B hAB eA f hb
    have hgroupJ := maximizingCutGroup_left G hq A eA f j
    subst x
    refine ⟨hj.1.symm, Or.inr ⟨hb, hjA⟩, ?_⟩
    rw [hgroupB]
    change maximizingCutBin G hq A eA f b =
      maximizingCutGroup G hq A eA f (eA j)
    rw [hgroupJ]
    exact hj.2.symm

/-- The degree retained at a right vertex is exactly its maximum bin load. -/
theorem degree_maximizingBinSubgraph_right
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {a q : Nat} (hq : 0 < q) (A B : Finset V)
    (hAB : Disjoint A B) (eA : Fin a ≃ A)
    (f : Fin a → Fin q) {b : V} (hb : b ∈ B) :
    (maximizingBinSubgraph G hq A B eA f).degree b =
      cutMaxBinLoad G A eA f b := by
  rw [← (maximizingBinSubgraph G hq A B eA f).card_neighborFinset_eq_degree]
  rw [neighborFinset_maximizingBinSubgraph_right G hq A B hAB eA f hb]
  calc
    #(keptLeftNeighbors G hq A eA f b) =
        cutBinLoad G A eA f b (maximizingCutBin G hq A eA f b) := by
      simp [keptLeftNeighbors, cutBinLoad]
    _ = cutMaxBinLoad G A eA f b :=
      cutBinLoad_maximizingCutBin G hq A eA f b

/-- Summing the maximum loads over the right side gives the exact number of
edges in the maximizing-bin subgraph. -/
theorem edgeCount_maximizingBinSubgraph
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {a q : Nat} (hq : 0 < q) (A B : Finset V)
    (hAB : Disjoint A B) (eA : Fin a ≃ A)
    (f : Fin a → Fin q) :
    edgeCount (maximizingBinSubgraph G hq A B eA f) =
      ∑ b ∈ B, cutMaxBinLoad G A eA f b := by
  let H := maximizingBinSubgraph G hq A B eA f
  have hbip : H.IsBipartiteWith (↑A : Set V) (↑B : Set V) :=
    maximizingBinSubgraph_isBipartiteWith G hq A B hAB eA f
  rw [edgeCount_eq_card_edgeFinset]
  rw [← SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges' hbip]
  apply Finset.sum_congr rfl
  intro b hb
  exact degree_maximizingBinSubgraph_right G hq A B hAB eA f hb

/-- The local maximum used by the graph construction is definitionally the
restriction statistic used in the global finite-probability calculation. -/
theorem cutBinLoad_eq_restrictedBinLoad
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {a q : Nat} (A : Finset V) (eA : Fin a ≃ A)
    (f : Fin a → Fin q) (b : V) (i : Fin q) :
    cutBinLoad G A eA f b i =
      binLoadOn
        (fun x : {j : Fin a // G.Adj (eA j) b} ↦ f x) i := by
  unfold cutBinLoad binLoadOn
  apply Finset.card_bij
    (fun j hj ↦ ⟨j, (Finset.mem_filter.mp hj).2.1⟩)
  · intro j hj
    have hj' := (Finset.mem_filter.mp hj).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hj'.2
  · intro j hj l hl hjl
    exact Subtype.ext_iff.mp hjl
  · intro x hx
    refine ⟨x.1, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨x.2, (Finset.mem_filter.mp hx).2⟩
    · rfl

theorem cutMaxBinLoad_eq_restrictedMaxBinLoad
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {a q : Nat} (A : Finset V) (eA : Fin a ≃ A)
    (f : Fin a → Fin q) (b : V) :
    cutMaxBinLoad G A eA f b =
      restrictedMaxBinLoad (fun j : Fin a ↦ G.Adj (eA j) b) f := by
  unfold cutMaxBinLoad restrictedMaxBinLoad maxBinLoadOn
  apply congrArg (Finset.sup (Finset.univ : Finset (Fin q)))
  funext i
  exact cutBinLoad_eq_restrictedBinLoad G A eA f b i

/-- Exact compatibility with `maximizingBinYield`, the statistic whose
uniform average is evaluated in `PathLowerBound`. -/
theorem sum_cutMaxBinLoad_eq_maximizingBinYield
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {a q : Nat} (A B : Finset V) (eA : Fin a ≃ A)
    (f : Fin a → Fin q) :
    (∑ b ∈ B, cutMaxBinLoad G A eA f b) =
      maximizingBinYield
        (fun j (b : B) ↦ G.Adj (eA j) (b : V)) f := by
  rw [maximizingBinYield, ← Finset.sum_attach B]
  apply Finset.sum_congr rfl
  intro b hb
  exact cutMaxBinLoad_eq_restrictedMaxBinLoad G A eA f b

/-- Final exact edge-count interface used by Lemma 4.5. -/
theorem edgeCount_maximizingBinSubgraph_eq_yield
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {a q : Nat} (hq : 0 < q) (A B : Finset V)
    (hAB : Disjoint A B) (eA : Fin a ≃ A)
    (f : Fin a → Fin q) :
    edgeCount (maximizingBinSubgraph G hq A B eA f) =
      maximizingBinYield
        (fun j (b : B) ↦ G.Adj (eA j) (b : V)) f := by
  rw [edgeCount_maximizingBinSubgraph G hq A B hAB eA f]
  exact sum_cutMaxBinLoad_eq_maximizingBinYield G A B eA f

/-! ## Relating the abstract yield to a bipartite graph -/

/-- In a graph whose bipartition is exactly `A,B`, the relation degree of a
right vertex is its graph degree. -/
theorem relationDegree_cutRelation_eq_degree
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {a : Nat} (A B : Finset V) (eA : Fin a ≃ A)
    (hbip : G.IsBipartiteWith (↑A : Set V) (↑B : Set V))
    (b : B) :
    relationDegree (fun j (b : B) ↦ G.Adj (eA j) (b : V)) b =
      G.degree b := by
  rw [← G.card_neighborFinset_eq_degree]
  rw [SimpleGraph.isBipartiteWith_neighborFinset' hbip b.prop]
  unfold relationDegree
  apply Finset.card_bij (fun j _ ↦ (eA j : V))
  · intro j hj
    have hj' := (Finset.mem_filter.mp hj).2
    exact Finset.mem_filter.mpr ⟨(eA j).prop, hj'⟩
  · intro j _ l _ hjl
    exact eA.injective (Subtype.ext hjl)
  · intro x hx
    have hx' := Finset.mem_filter.mp hx
    let j : Fin a := eA.symm ⟨x, hx'.1⟩
    refine ⟨j, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        simpa only [j, eA.apply_symm_apply] using hx'.2⟩
    · simp [j]

/-- The sum of relation degrees is exactly the edge count of the bipartite
cut graph. -/
theorem sum_relationDegree_cutRelation_eq_edgeCount
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {a : Nat} (A B : Finset V) (eA : Fin a ≃ A)
    (hbip : G.IsBipartiteWith (↑A : Set V) (↑B : Set V)) :
    ∑ b : B,
        relationDegree (fun j (b : B) ↦ G.Adj (eA j) (b : V)) b =
      edgeCount G := by
  calc
    ∑ b : B,
        relationDegree (fun j (b : B) ↦ G.Adj (eA j) (b : V)) b =
        ∑ b : B, G.degree b := by
      apply Finset.sum_congr rfl
      intro b _
      exact relationDegree_cutRelation_eq_degree G A B eA hbip b
    _ = ∑ b ∈ B, G.degree b := by
      simpa using (Finset.sum_attach B (fun b ↦ G.degree b))
    _ = #G.edgeFinset :=
      SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges' hbip
    _ = edgeCount G := (edgeCount_eq_card_edgeFinset G).symm

/-! ## The graph-valued finite-probability extraction -/

/-- Given the bipartite cut produced in the first step of BLS Lemma 4.5,
the finite balls-and-bins argument returns an actual large `P_n`-free
subgraph.  No probability object remains in the conclusion. -/
theorem exists_large_pathFree_maximizingBinSubgraph
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {r n v Δ : Nat} (A B : Finset V)
    (eA : Fin ((v + 1) / 2) ≃ A)
    (hAB : Disjoint A B)
    (hbip : G.IsBipartiteWith (↑A : Set V) (↑B : Set V))
    (hr : 21 ≤ r)
    (hn : 100 * Real.log (r : Real) ≤ (n : Real))
    (hv : (v : Real) ≤ 2 * (r * Real.log (r : Real)) * n)
    (hqTwo : 2 ≤ subgraphFindingBinCount n v) (hΔ : 0 < Δ)
    (hdegree : ∀ b : B, G.degree b ≤ Δ) :
    ∃ H : SimpleGraph V,
      H ≤ G ∧ (pathGraph n).Free H ∧
        (2 : Real) / 3 * (edgeCount G : Real) *
            ballsBinsWeight (subgraphFindingBinCount n v) Δ ≤
          (edgeCount H : Real) := by
  let q := subgraphFindingBinCount n v
  have hq : 0 < q := by dsimp only [q]; omega
  let R : Fin ((v + 1) / 2) → B → Prop :=
    fun j b ↦ G.Adj (eA j) (b : V)
  letI : DecidableRel R := fun j b ↦
    inferInstanceAs (Decidable (G.Adj (eA j) (b : V)))
  have hrelationDegree : ∀ b, relationDegree R b ≤ Δ := by
    intro b
    rw [show relationDegree R b = G.degree b by
      exact relationDegree_cutRelation_eq_degree G A B eA hbip b]
    exact hdegree b
  obtain ⟨f, hfsafe, hyield⟩ :=
    exists_subgraphFinding_safe_allocation R hr hn hv hqTwo hΔ
      hrelationDegree
  let H := maximizingBinSubgraph G hq A B eA f
  refine ⟨H, maximizingBinSubgraph_le G hq A B eA f, ?_, ?_⟩
  · apply maximizingBinSubgraph_pathFree_of_safe G hq A B eA f
    intro i
    have hs := (Finset.mem_filter.mp hfsafe).2 i
    simpa only [pathSafeAllocationEvent] using hs
  · have hsum :
        (∑ b, (relationDegree R b : Real)) = edgeCount G := by
      exact_mod_cast
        (sum_relationDegree_cutRelation_eq_edgeCount G A B eA hbip)
    have hcount : (edgeCount H : Real) = maximizingBinYield R f := by
      exact_mod_cast
        (edgeCount_maximizingBinSubgraph_eq_yield
          G hq A B hAB eA f)
    rw [hsum] at hyield
    rw [hcount]
    exact hyield

/-- The same graph-valued conclusion in the deterministic `q = 1` branch
of Lemma 4.5. -/
theorem exists_large_pathFree_maximizingBinSubgraph_one_bin
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {n v Δ : Nat} (A B : Finset V)
    (eA : Fin ((v + 1) / 2) ≃ A)
    (hAB : Disjoint A B)
    (hbip : G.IsBipartiteWith (↑A : Set V) (↑B : Set V))
    (hn : 0 < n) (hqOne : subgraphFindingBinCount n v = 1)
    (hΔ : 0 < Δ) :
    ∃ H : SimpleGraph V,
      H ≤ G ∧ (pathGraph n).Free H ∧
        (2 : Real) / 3 * (edgeCount G : Real) *
            ballsBinsWeight (subgraphFindingBinCount n v) Δ ≤
          (edgeCount H : Real) := by
  let q := subgraphFindingBinCount n v
  have hq : 0 < q := by dsimp only [q]; omega
  let R : Fin ((v + 1) / 2) → B → Prop :=
    fun j b ↦ G.Adj (eA j) (b : V)
  letI : DecidableRel R := fun j b ↦
    inferInstanceAs (Decidable (G.Adj (eA j) (b : V)))
  obtain ⟨f, hfsafe, hyield⟩ :=
    exists_subgraphFinding_safe_allocation_one_bin R hn hqOne hΔ
  let H := maximizingBinSubgraph G hq A B eA f
  refine ⟨H, maximizingBinSubgraph_le G hq A B eA f, ?_, ?_⟩
  · apply maximizingBinSubgraph_pathFree_of_safe G hq A B eA f
    intro i
    have hs := (Finset.mem_filter.mp hfsafe).2 i
    simpa only [pathSafeAllocationEvent] using hs
  · have hsum :
        (∑ b, (relationDegree R b : Real)) = edgeCount G := by
      exact_mod_cast
        (sum_relationDegree_cutRelation_eq_edgeCount G A B eA hbip)
    have hcount : (edgeCount H : Real) = maximizingBinYield R f := by
      exact_mod_cast
        (edgeCount_maximizingBinSubgraph_eq_yield
          G hq A B hAB eA f)
    rw [hsum] at hyield
    rw [hcount]
    exact hyield

/-- The numerical last line of Lemma 4.5: a cut retaining at least half of
the original edges turns the `2/3` truncated-expectation estimate into the
advertised `1/3` estimate. -/
theorem one_third_bound_of_two_thirds_cut_bound
    {V W X : Type*} {G : SimpleGraph V} {C : SimpleGraph W}
    {H : SimpleGraph X} {weight : Real}
    (hweight : 0 ≤ weight)
    (hcut : edgeCount G ≤ 2 * edgeCount C)
    (hlarge : (2 : Real) / 3 * (edgeCount C : Real) * weight ≤
      (edgeCount H : Real)) :
    (edgeCount G : Real) / 3 * weight ≤ (edgeCount H : Real) := by
  have hcutReal : (edgeCount G : Real) ≤ 2 * (edgeCount C : Real) := by
    exact_mod_cast hcut
  calc
    (edgeCount G : Real) / 3 * weight ≤
        (2 * (edgeCount C : Real)) / 3 * weight := by
      gcongr
    _ = (2 : Real) / 3 * (edgeCount C : Real) * weight := by ring
    _ ≤ (edgeCount H : Real) := hlarge

/-- Corrected positive-bin form of BLS Lemma 4.5 after a dense bipartite cut
has been chosen.  The maximum-degree hypothesis is imposed on the side whose
neighbourhoods are actually sampled. -/
theorem exists_pathFree_of_dense_bipartite_cut
    [Fintype V] [DecidableEq V]
    (G C : SimpleGraph V) [DecidableRel C.Adj]
    {r n v Δ : Nat} (A B : Finset V)
    (eA : Fin ((v + 1) / 2) ≃ A)
    (hCle : C ≤ G) (hcut : edgeCount G ≤ 2 * edgeCount C)
    (hAB : Disjoint A B)
    (hbip : C.IsBipartiteWith (↑A : Set V) (↑B : Set V))
    (hr : 21 ≤ r)
    (hn : 100 * Real.log (r : Real) ≤ (n : Real))
    (hv : (v : Real) ≤ 2 * (r * Real.log (r : Real)) * n)
    (hqTwo : 2 ≤ subgraphFindingBinCount n v) (hΔ : 0 < Δ)
    (hdegree : ∀ b : B, C.degree b ≤ Δ) :
    ∃ H : SimpleGraph V,
      H ≤ G ∧ (pathGraph n).Free H ∧
        (edgeCount G : Real) / 3 *
            ballsBinsWeight (subgraphFindingBinCount n v) Δ ≤
          (edgeCount H : Real) := by
  obtain ⟨H, hHC, hfree, hlarge⟩ :=
    exists_large_pathFree_maximizingBinSubgraph
      C A B eA hAB hbip hr hn hv hqTwo hΔ hdegree
  refine ⟨H, hHC.trans hCle, hfree, ?_⟩
  apply one_third_bound_of_two_thirds_cut_bound
    (G := G) (C := C) (H := H)
    (weight := ballsBinsWeight (subgraphFindingBinCount n v) Δ)
  · unfold ballsBinsWeight expectedMaxBinLoad
    positivity
  · exact hcut
  · exact hlarge

/-- The deterministic `q=1` companion to
`exists_pathFree_of_dense_bipartite_cut`. -/
theorem exists_pathFree_of_dense_bipartite_cut_one_bin
    [Fintype V] [DecidableEq V]
    (G C : SimpleGraph V) [DecidableRel C.Adj]
    {n v Δ : Nat} (A B : Finset V)
    (eA : Fin ((v + 1) / 2) ≃ A)
    (hCle : C ≤ G) (hcut : edgeCount G ≤ 2 * edgeCount C)
    (hAB : Disjoint A B)
    (hbip : C.IsBipartiteWith (↑A : Set V) (↑B : Set V))
    (hn : 0 < n) (hqOne : subgraphFindingBinCount n v = 1)
    (hΔ : 0 < Δ) :
    ∃ H : SimpleGraph V,
      H ≤ G ∧ (pathGraph n).Free H ∧
        (edgeCount G : Real) / 3 *
            ballsBinsWeight (subgraphFindingBinCount n v) Δ ≤
          (edgeCount H : Real) := by
  obtain ⟨H, hHC, hfree, hlarge⟩ :=
    exists_large_pathFree_maximizingBinSubgraph_one_bin
      C A B eA hAB hbip hn hqOne hΔ
  refine ⟨H, hHC.trans hCle, hfree, ?_⟩
  apply one_third_bound_of_two_thirds_cut_bound
    (G := G) (C := C) (H := H)
    (weight := ballsBinsWeight (subgraphFindingBinCount n v) Δ)
  · unfold ballsBinsWeight expectedMaxBinLoad
    positivity
  · exact hcut
  · exact hlarge

end

end LeanCo.SizeRamsey
