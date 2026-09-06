import LeanCo.SizeRamsey.LowDegreeEdgeColoring
import LeanCo.SizeRamsey.AvoidingColoringGlue
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# The low-degree decomposition behind BLS Lemma 2.2

For a degree threshold `Δ`, the edges of a finite graph split into low--low,
low--high, and high--high edges.  The low--low part has the coarse proper
edge-colouring from `LowDegreeEdgeColoring`.  On the low--high part we number
the edges incident with each low vertex; every monochromatic component is
therefore a star centred at a high vertex.  The high--high part is retained
as the core.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open Finset Function SimpleGraph

noncomputable section

universe u

variable {V : Type u}

/-- A vertex is low at threshold `Δ` when its degree in the original graph
is at most `Δ`. -/
def IsLowAt [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) (v : V) : Prop :=
  G.degree v ≤ Δ

/-- The complementary high-vertex predicate. -/
def IsHighAt [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) (v : V) : Prop :=
  Δ < G.degree v

theorem isHighAt_iff_not_isLowAt [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) (v : V) :
    IsHighAt G Δ v ↔ ¬ IsLowAt G Δ v := by
  simp [IsHighAt, IsLowAt]

/-- Edges whose two endpoints are low. -/
def lowLowGraph [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ IsLowAt G Δ x ∧ IsLowAt G Δ y
  symm.symm x y h := ⟨h.1.symm, h.2.2, h.2.1⟩

/-- Edges with exactly one low endpoint. -/
def lowHighGraph [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) : SimpleGraph V where
  Adj x y := G.Adj x y ∧
    ((IsLowAt G Δ x ∧ IsHighAt G Δ y) ∨
      (IsHighAt G Δ x ∧ IsLowAt G Δ y))
  symm.symm x y h := ⟨h.1.symm, h.2.elim (fun hxy ↦ Or.inr ⟨hxy.2, hxy.1⟩)
    (fun hxy ↦ Or.inl ⟨hxy.2, hxy.1⟩)⟩

/-- The high--high core. -/
def highCoreGraph [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ IsHighAt G Δ x ∧ IsHighAt G Δ y
  symm.symm x y h := ⟨h.1.symm, h.2.2, h.2.1⟩

instance [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] (Δ : ℕ) :
    DecidableRel (lowLowGraph G Δ).Adj :=
  Classical.decRel _

instance [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] (Δ : ℕ) :
    DecidableRel (lowHighGraph G Δ).Adj :=
  Classical.decRel _

instance [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] (Δ : ℕ) :
    DecidableRel (highCoreGraph G Δ).Adj :=
  Classical.decRel _

@[simp] theorem lowLowGraph_adj [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) {x y : V} :
    (lowLowGraph G Δ).Adj x y ↔
      G.Adj x y ∧ IsLowAt G Δ x ∧ IsLowAt G Δ y := Iff.rfl

@[simp] theorem lowHighGraph_adj [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) {x y : V} :
    (lowHighGraph G Δ).Adj x y ↔
      G.Adj x y ∧
        ((IsLowAt G Δ x ∧ IsHighAt G Δ y) ∨
          (IsHighAt G Δ x ∧ IsLowAt G Δ y)) := Iff.rfl

@[simp] theorem highCoreGraph_adj [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) {x y : V} :
    (highCoreGraph G Δ).Adj x y ↔
      G.Adj x y ∧ IsHighAt G Δ x ∧ IsHighAt G Δ y := Iff.rfl

theorem lowLowGraph_le [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) :
    lowLowGraph G Δ ≤ G := fun _ _ h ↦ h.1

theorem lowHighGraph_le [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) :
    lowHighGraph G Δ ≤ G := fun _ _ h ↦ h.1

theorem highCoreGraph_le [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) :
    highCoreGraph G Δ ≤ G := fun _ _ h ↦ h.1

/-- The part discharged by the two low-degree colourings. -/
def lowDegreePart [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) : SimpleGraph V :=
  lowLowGraph G Δ ⊔ lowHighGraph G Δ

/-- The three cases exhaust every edge, with no slack in the cover. -/
theorem lowDegreePart_sup_highCore [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) :
    lowDegreePart G Δ ⊔ highCoreGraph G Δ = G := by
  ext x y
  simp only [lowDegreePart, SimpleGraph.sup_adj, lowLowGraph_adj,
    lowHighGraph_adj, highCoreGraph_adj]
  constructor
  · grind
  · intro hxy
    by_cases hx : IsLowAt G Δ x
    · by_cases hy : IsLowAt G Δ y
      · exact Or.inl (Or.inl ⟨hxy, hx, hy⟩)
      · exact Or.inl (Or.inr ⟨hxy, Or.inl ⟨hx,
          (isHighAt_iff_not_isLowAt G Δ y).2 hy⟩⟩)
    · by_cases hy : IsLowAt G Δ y
      · exact Or.inl (Or.inr ⟨hxy, Or.inr
          ⟨(isHighAt_iff_not_isLowAt G Δ x).2 hx, hy⟩⟩)
      · exact Or.inr ⟨hxy, (isHighAt_iff_not_isLowAt G Δ x).2 hx,
          (isHighAt_iff_not_isLowAt G Δ y).2 hy⟩

/-- Low--low, low--high and high--high edge sets are pairwise disjoint. -/
theorem lowLow_disjoint_lowHigh [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) :
    Disjoint (lowLowGraph G Δ) (lowHighGraph G Δ) := by
  rw [SimpleGraph.disjoint_left]
  intro x y hll hlh
  rcases hlh.2 with h | h
  · exact (isHighAt_iff_not_isLowAt G Δ y).1 h.2 hll.2.2
  · exact (isHighAt_iff_not_isLowAt G Δ x).1 h.1 hll.2.1

theorem lowLow_disjoint_highCore [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) :
    Disjoint (lowLowGraph G Δ) (highCoreGraph G Δ) := by
  rw [SimpleGraph.disjoint_left]
  intro x y hll hhh
  exact (isHighAt_iff_not_isLowAt G Δ x).1 hhh.2.1 hll.2.1

theorem lowHigh_disjoint_highCore [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) :
    Disjoint (lowHighGraph G Δ) (highCoreGraph G Δ) := by
  rw [SimpleGraph.disjoint_left]
  intro x y hlh hhh
  rcases hlh.2 with h | h
  · exact (isHighAt_iff_not_isLowAt G Δ x).1 hhh.2.1 h.1
  · exact (isHighAt_iff_not_isLowAt G Δ y).1 hhh.2.2 h.2

/-! ## Numbering the edges at their unique low endpoint -/

/-- Every low--high edge has a unique low endpoint. -/
theorem lowHigh_edge_existsUnique_low
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Δ : ℕ) (e : (lowHighGraph G Δ).edgeSet) :
    ∃! v : V, v ∈ (e : Sym2 V) ∧ IsLowAt G Δ v := by
  rcases e with ⟨⟨x, y⟩, he⟩
  change (lowHighGraph G Δ).Adj x y at he
  rcases he.2 with hxy | hxy
  · refine ⟨x, ⟨Sym2.mem_mk_left _ _, hxy.1⟩, ?_⟩
    intro z hz
    rcases Sym2.mem_iff'.mp hz.1 with hzx | hzy
    · exact hzx
    · exact ((isHighAt_iff_not_isLowAt G Δ y).1 hxy.2
        (hzy ▸ hz.2)).elim
  · refine ⟨y, ⟨Sym2.mem_mk_right _ _, hxy.2⟩, ?_⟩
    intro z hz
    rcases Sym2.mem_iff'.mp hz.1 with hzx | hzy
    · exact ((isHighAt_iff_not_isLowAt G Δ x).1 hxy.1
        (hzx ▸ hz.2)).elim
    · exact hzy

/-- The unique low endpoint of a low--high edge. -/
def lowEndpoint
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Δ : ℕ) (e : (lowHighGraph G Δ).edgeSet) : V :=
  Classical.choose (lowHigh_edge_existsUnique_low G Δ e)

theorem lowEndpoint_mem
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Δ : ℕ) (e : (lowHighGraph G Δ).edgeSet) :
    lowEndpoint G Δ e ∈ (e : Sym2 V) :=
  (Classical.choose_spec (lowHigh_edge_existsUnique_low G Δ e)).1.1

theorem lowEndpoint_isLow
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Δ : ℕ) (e : (lowHighGraph G Δ).edgeSet) :
    IsLowAt G Δ (lowEndpoint G Δ e) :=
  (Classical.choose_spec (lowHigh_edge_existsUnique_low G Δ e)).1.2

theorem lowEndpoint_eq_of_mem_of_isLow
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Δ : ℕ) (e : (lowHighGraph G Δ).edgeSet) {v : V}
    (hmem : v ∈ (e : Sym2 V)) (hlow : IsLowAt G Δ v) :
    lowEndpoint G Δ e = v :=
  ((Classical.choose_spec (lowHigh_edge_existsUnique_low G Δ e)).2 v
    ⟨hmem, hlow⟩).symm

/-- There are enough labels to injectively number all ambient edges incident
with a low vertex. -/
def lowIncidenceEmbedding
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Δ : ℕ) (v : V) (hv : IsLowAt G Δ v) :
    (G.incidenceFinset v : Type u) ↪ Fin (Δ + 1) := by
  apply Classical.choice
  apply Function.Embedding.nonempty_of_card_le
  simpa only [Fintype.card_coe, Fintype.card_fin,
    G.card_incidenceFinset_eq_degree] using hv.trans (Nat.le_succ Δ)

theorem lowEndpoint_mem_ambientIncidence
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Δ : ℕ) (e : (lowHighGraph G Δ).edgeSet) :
    (e : Sym2 V) ∈ G.incidenceFinset (lowEndpoint G Δ e) := by
  rw [G.mem_incidenceFinset]
  exact ⟨SimpleGraph.edgeSet_mono (lowHighGraph_le G Δ) e.2,
    lowEndpoint_mem G Δ e⟩

/-- Extend the injective numbering at a low vertex to a total function on
unordered pairs.  Values away from its incidence set are irrelevant. -/
def lowIncidenceLabel
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Δ : ℕ) (v : V) (e : Sym2 V) : Fin (Δ + 1) := by
  classical
  exact if hv : IsLowAt G Δ v then
      if he : e ∈ G.incidenceFinset v then
        lowIncidenceEmbedding G Δ v hv ⟨e, he⟩
      else 0
    else 0

theorem lowIncidenceLabel_injectiveOn
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Δ : ℕ) {v : V} (hv : IsLowAt G Δ v) {e f : Sym2 V}
    (he : e ∈ G.incidenceFinset v) (hf : f ∈ G.incidenceFinset v)
    (hlabel : lowIncidenceLabel G Δ v e = lowIncidenceLabel G Δ v f) :
    e = f := by
  simp only [lowIncidenceLabel, dif_pos hv, dif_pos he, dif_pos hf] at hlabel
  have hsub := (lowIncidenceEmbedding G Δ v hv).injective hlabel
  exact congrArg (fun z : G.incidenceFinset v ↦ (z : Sym2 V)) hsub

/-- Number a low--high edge inside the incidence set of its unique low
endpoint. -/
def lowHighColoring
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Δ : ℕ) :
    (lowHighGraph G Δ).EdgeLabeling (Fin (Δ + 1)) :=
  fun e ↦ lowIncidenceLabel G Δ (lowEndpoint G Δ e) e

/-- At a fixed low endpoint the low--high colouring is injective on incident
edges. -/
theorem lowHighColoring_eq_imp_edge_eq_of_low_mem
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Δ : ℕ) {v : V} {e f : (lowHighGraph G Δ).edgeSet}
    (hv : IsLowAt G Δ v) (hve : v ∈ (e : Sym2 V))
    (hvf : v ∈ (f : Sym2 V))
    (hcolor : lowHighColoring G Δ e = lowHighColoring G Δ f) :
    e = f := by
  have he : lowEndpoint G Δ e = v :=
    lowEndpoint_eq_of_mem_of_isLow G Δ e hve hv
  have hf : lowEndpoint G Δ f = v :=
    lowEndpoint_eq_of_mem_of_isLow G Δ f hvf hv
  apply Subtype.ext
  apply lowIncidenceLabel_injectiveOn G Δ hv
  · rw [G.mem_incidenceFinset]
    exact ⟨SimpleGraph.edgeSet_mono (lowHighGraph_le G Δ) e.2, hve⟩
  · rw [G.mem_incidenceFinset]
    exact ⟨SimpleGraph.edgeSet_mono (lowHighGraph_le G Δ) f.2, hvf⟩
  · simpa only [lowHighColoring, he, hf] using hcolor

/-! ## The monochromatic star invariant -/

/-- A graph contained in the low--high part is a high-centred star forest when
the middle of every genuine two-edge path is high.  This local formulation is
exactly what is needed to exclude four-vertex paths. -/
def IsHighCenteredStarForest
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ)
    (H : SimpleGraph V) : Prop :=
  H ≤ lowHighGraph G Δ ∧
    ∀ {x y z : V}, H.Adj x y → H.Adj y z → x ≠ z → IsHighAt G Δ y

/-- Every colour class of the low--high colouring is a star forest whose
nontrivial component centres are high vertices. -/
theorem lowHighColoring_isHighCenteredStarForest
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Δ : ℕ) (color : Fin (Δ + 1)) :
    IsHighCenteredStarForest G Δ ((lowHighColoring G Δ).labelGraph color) := by
  constructor
  · intro x y hxy
    rw [EdgeLabeling.labelGraph_adj] at hxy
    exact hxy.1
  · intro x y z hxy hyz hxz
    rw [EdgeLabeling.labelGraph_adj] at hxy hyz
    by_contra hyHigh
    have hyLow : IsLowAt G Δ y := by
      by_contra hyLow
      exact hyHigh ((isHighAt_iff_not_isLowAt G Δ y).2 hyLow)
    let exy : (lowHighGraph G Δ).edgeSet := ⟨s(x, y), hxy.1⟩
    let eyz : (lowHighGraph G Δ).edgeSet := ⟨s(y, z), hyz.1⟩
    have heq : exy = eyz := by
      apply lowHighColoring_eq_imp_edge_eq_of_low_mem G Δ hyLow
      · exact Sym2.mem_mk_right _ _
      · exact Sym2.mem_mk_left _ _
      · exact hxy.2.trans hyz.2.symm
    have hsym : s(x, y) = s(y, z) := congrArg Subtype.val heq
    rw [Sym2.eq_iff] at hsym
    rcases hsym with h | h
    · exact hxy.1.ne h.1
    · exact hxz h.1

/-- The first four vertices embed in every path on at least four vertices. -/
def pathGraphFourEmbedding (n : ℕ) (h : 4 ≤ n) :
    pathGraph 4 ↪g pathGraph n where
  toFun v := ⟨v, v.2.trans_le h⟩
  inj' := by
    intro v w hvw
    have hval : v.val = w.val :=
      congrArg (fun z : Fin n ↦ z.val) hvw
    exact Fin.ext hval
  map_rel_iff' := by simp [pathGraph]

/-- Excluding a four-vertex path excludes every longer path. -/
theorem pathGraph_free_of_four_le
    {H : SimpleGraph V} {n : ℕ} (hn : 4 ≤ n)
    (hfour : (pathGraph 4).Free H) : (pathGraph n).Free H := by
  intro hncopy
  apply hfour
  exact (pathGraphFourEmbedding n hn).isContained.trans hncopy

/-- A high-centred star forest contains no four-vertex path. -/
theorem pathGraph_four_free_of_isHighCenteredStarForest
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ)
    {H : SimpleGraph V} (hstar : IsHighCenteredStarForest G Δ H) :
    (pathGraph 4).Free H := by
  intro hcopy
  obtain ⟨φ⟩ := hcopy
  let a : Fin 4 := ⟨0, by omega⟩
  let b : Fin 4 := ⟨1, by omega⟩
  let c : Fin 4 := ⟨2, by omega⟩
  let d : Fin 4 := ⟨3, by omega⟩
  have hab : (pathGraph 4).Adj a b := by simp [a, b, pathGraph_adj]
  have hbc : (pathGraph 4).Adj b c := by simp [b, c, pathGraph_adj]
  have hcd : (pathGraph 4).Adj c d := by simp [c, d, pathGraph_adj]
  have hac : φ a ≠ φ c := by
    intro h
    have : a = c := φ.injective h
    simp [a, c] at this
  have hbd : φ b ≠ φ d := by
    intro h
    have : b = d := φ.injective h
    simp [b, d] at this
  have hHab := φ.toHom.map_adj hab
  have hHbc := φ.toHom.map_adj hbc
  have hHcd := φ.toHom.map_adj hcd
  have hbHigh : IsHighAt G Δ (φ b) := hstar.2 hHab hHbc hac
  have hcHigh : IsHighAt G Δ (φ c) := hstar.2 hHbc hHcd hbd
  have hLH := hstar.1 hHbc
  rcases hLH.2 with h | h
  · exact (isHighAt_iff_not_isLowAt G Δ (φ b)).1 hbHigh h.1
  · exact (isHighAt_iff_not_isLowAt G Δ (φ c)).1 hcHigh h.2

/-- The explicit low--high colouring avoids every path on at least four
vertices. -/
theorem lowHighColoring_avoids_pathGraph
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Δ n : ℕ) (hn : 4 ≤ n) :
    AvoidsMonochromaticCopy (pathGraph n) (lowHighColoring G Δ) := by
  intro color
  apply pathGraph_free_of_four_le hn
  exact pathGraph_four_free_of_isHighCenteredStarForest G Δ
    (lowHighColoring_isHighCenteredStarForest G Δ color)

/-! ## Colouring the whole low-degree part -/

theorem lowLowGraph_degree_le
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Δ : ℕ) (v : V) : (lowLowGraph G Δ).degree v ≤ Δ := by
  by_cases hv : IsLowAt G Δ v
  · exact ((lowLowGraph G Δ).degree_le_of_le (lowLowGraph_le G Δ)).trans hv
  · have hz : (lowLowGraph G Δ).degree v = 0 := by
      rw [SimpleGraph.degree_eq_zero]
      intro w hvw
      exact hv hvw.2.1
    omega

/-- The two pieces that are discharged by edge colourings. -/
def lowDegreeCoverPiece
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) :
    Bool → SimpleGraph V
  | false => lowLowGraph G Δ
  | true => lowHighGraph G Δ

/-- Palette sizes for the low--low and low--high pieces. -/
def lowDegreeCoverBudget (Δ : ℕ) : Bool → ℕ
  | false => 2 * Δ + 1
  | true => Δ + 1

theorem lowDegreeCoverPiece_le
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) :
    ∀ i, lowDegreeCoverPiece G Δ i ≤ lowDegreePart G Δ := by
  intro i
  cases i
  · exact le_sup_left
  · exact le_sup_right

theorem lowDegreeCoverPiece_covers
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) :
    EdgesCoveredBy (lowDegreePart G Δ) (lowDegreeCoverPiece G Δ) := by
  intro e he
  rw [lowDegreePart, SimpleGraph.edgeSet_sup] at he
  rcases he with he | he
  · exact ⟨false, he⟩
  · exact ⟨true, he⟩

/-- The low--low and low--high pieces together use at most `3 * Δ + 2`
colours and avoid every path on at least four vertices. -/
theorem exists_lowDegreePart_path_avoidingColoring
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Δ n : ℕ) (hn : 4 ≤ n) :
    ∃ C : (lowDegreePart G Δ).EdgeLabeling (Fin (3 * Δ + 2)),
      AvoidsMonochromaticCopy (pathGraph n) C := by
  apply exists_fin_path_avoidingColoring_of_cover
    (lowDegreePart G Δ) (lowDegreeCoverPiece G Δ)
      (lowDegreeCoverBudget Δ) (show 2 ≤ n by omega)
  · exact lowDegreeCoverPiece_le G Δ
  · exact lowDegreeCoverPiece_covers G Δ
  · intro i
    cases i
    · simpa only [lowDegreeCoverPiece, lowDegreeCoverBudget] using
        exists_edgeLabeling_fin_two_mul_add_one_avoids_pathGraph
          (lowLowGraph G Δ) Δ n (lowLowGraph_degree_le G Δ) (by omega)
    · exact ⟨lowHighColoring G Δ, lowHighColoring_avoids_pathGraph G Δ n hn⟩
  · simp only [Fintype.sum_bool, lowDegreeCoverBudget]
    omega

/-! ## Size of the high core -/

/-- The designated vertex set of the high--high core.  Keeping this set
explicit avoids counting isolated ambient vertices of the spanning graph
representation. -/
def highCoreVertexFinset
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter (IsHighAt G Δ)

@[simp] theorem mem_highCoreVertexFinset
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) (v : V) :
    v ∈ highCoreVertexFinset G Δ ↔ IsHighAt G Δ v := by
  classical
  simp [highCoreVertexFinset]

/-- The high core is precisely the graph induced on the designated high
vertex set, expressed without changing the ambient vertex type. -/
theorem highCoreGraph_adj_iff_mem
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) {x y : V} :
    (highCoreGraph G Δ).Adj x y ↔
      G.Adj x y ∧ x ∈ highCoreVertexFinset G Δ ∧
        y ∈ highCoreVertexFinset G Δ := by
  simp only [highCoreGraph_adj, mem_highCoreVertexFinset]

/-- Handshaking bounds the number of vertices retained by the high core. -/
theorem highCoreVertexFinset_card_bound
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Δ : ℕ) :
    (Δ + 1) * (highCoreVertexFinset G Δ).card ≤ 2 * edgeCount G := by
  classical
  calc
    (Δ + 1) * (highCoreVertexFinset G Δ).card =
        ∑ v ∈ highCoreVertexFinset G Δ, (Δ + 1) := by
          simp [Nat.mul_comm]
    _ ≤ ∑ v ∈ highCoreVertexFinset G Δ, G.degree v := by
      apply Finset.sum_le_sum
      intro v hv
      rw [mem_highCoreVertexFinset] at hv
      exact hv
    _ ≤ ∑ v, G.degree v := by
      exact Finset.sum_le_univ_sum_of_nonneg (fun _ ↦ Nat.zero_le _)
    _ = 2 * edgeCount G := by
      rw [G.sum_degrees_eq_twice_card_edges, edgeCount,
        Nat.card_eq_fintype_card, G.card_edgeSet]

/-- Equivalent division-free cardinal form convenient for later numerical
instantiations. -/
theorem highCoreVertexFinset_card_le_two_mul_edgeCount
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Δ : ℕ) :
    (highCoreVertexFinset G Δ).card ≤ 2 * edgeCount G := by
  exact (Nat.le_mul_of_pos_left _ (Nat.succ_pos Δ)).trans
    (highCoreVertexFinset_card_bound G Δ)

/-! ## Bundled structural interface -/

/-- Generic, division-free structural form of the decomposition used in BLS
Lemma 2.2.  It exposes exactly the data needed by later numerical arguments:
the coloured low-degree part, exact and disjoint edge partition, and the
handshaking bound on the high core. -/
theorem exists_blsLemmaTwoTwo_refinement
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Δ n : ℕ) (hn : 4 ≤ n) :
    ∃ C : (lowDegreePart G Δ).EdgeLabeling (Fin (3 * Δ + 2)),
      AvoidsMonochromaticCopy (pathGraph n) C ∧
      lowDegreePart G Δ ⊔ highCoreGraph G Δ = G ∧
      Disjoint (lowLowGraph G Δ) (lowHighGraph G Δ) ∧
      Disjoint (lowLowGraph G Δ) (highCoreGraph G Δ) ∧
      Disjoint (lowHighGraph G Δ) (highCoreGraph G Δ) ∧
      (Δ + 1) * (highCoreVertexFinset G Δ).card ≤ 2 * edgeCount G := by
  obtain ⟨C, hC⟩ := exists_lowDegreePart_path_avoidingColoring G Δ n hn
  exact ⟨C, hC, lowDegreePart_sup_highCore G Δ,
    lowLow_disjoint_lowHigh G Δ, lowLow_disjoint_highCore G Δ,
    lowHigh_disjoint_highCore G Δ, highCoreVertexFinset_card_bound G Δ⟩

end

end LeanCo.SizeRamsey
