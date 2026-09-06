import LeanCo.HypercubeTuran.BaseGraph
import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Tactic

/-!
# A finite binomial random graph

This file realizes `G(N,p)` on the concrete product probability space of
subsets of the non-diagonal unordered pairs of `Fin N`.  Keeping the edge
coordinates visible is useful later when applying concentration inequalities
to cuts.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal Finset ProbabilityTheory SimpleGraph unitInterval

namespace LeanCo.HypercubeTuran

noncomputable section

local instance (V : Type*) [Countable V] :
    MeasurableSingletonClass (SimpleGraph V) where
  measurableSet_singleton G := by
    apply (SimpleGraph.measurableEmbedding_edgeSet (V := V)).measurableSet_image.mp
    rw [Set.image_singleton]
    exact measurableSet_singleton G.edgeSet

/-- The possible (undirected, loopless) edges on `Fin N`. -/
abbrev RandomEdge (N : ℕ) := (Sym2.diagSetᶜ : Set (Sym2 (Fin N)))

/-- A set of selected edge coordinates, interpreted as a simple graph. -/
def graphOfEdges {N : ℕ} (E : Set (RandomEdge N)) : SimpleGraph (Fin N) :=
  SimpleGraph.fromEdgeSet (Subtype.val '' E)

/-- The product measure in which every possible edge is selected with
probability `p`, independently. -/
def randomEdgeMeasure (N : ℕ) (p : unitInterval) : Measure (Set (RandomEdge N)) :=
  setBer(Set.univ, p)

instance (N : ℕ) (p : unitInterval) : IsProbabilityMeasure (randomEdgeMeasure N p) :=
  by unfold randomEdgeMeasure; infer_instance

theorem measurable_graphOfEdges (N : ℕ) :
    Measurable (graphOfEdges : Set (RandomEdge N) → SimpleGraph (Fin N)) :=
  measurable_of_finite _

/-- The induced probability measure on simple graphs. -/
def randomGraphMeasure (N : ℕ) (p : unitInterval) : Measure (SimpleGraph (Fin N)) :=
  (randomEdgeMeasure N p).map graphOfEdges

instance (N : ℕ) (p : unitInterval) : IsProbabilityMeasure (randomGraphMeasure N p) := by
  unfold randomGraphMeasure
  exact Measure.isProbabilityMeasure_map (measurable_graphOfEdges N).aemeasurable

/-- Restrict a set to a family of coordinates. -/
def restrictSet {ι : Type*} (A : Set ι) (E : Set ι) : Set A :=
  A.restrict E

@[simp]
theorem ncard_restrictSet_eq_inter {ι : Type*} [Finite ι]
    (A E : Set ι) :
    (restrictSet A E).ncard = (E ∩ A).ncard := by
  rw [← Set.ncard_image_of_injective (restrictSet A E) Subtype.val_injective]
  congr 1
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ha, a.property⟩
  · rintro ⟨hxE, hxA⟩
    exact ⟨⟨x, hxA⟩, hxE, rfl⟩

private lemma map_restrictSet_setBernoulli_univ {ι : Type*} [Countable ι]
    (A : Set ι) (p : unitInterval) :
    setBer((Set.univ : Set ι), p).map (restrictSet A) =
      setBer((Set.univ : Set A), p) := by
  rw [setBernoulli_eq_map, setBernoulli_eq_map]
  have hres : Measurable (restrictSet A) := by
    change Measurable (A.restrict (π := fun _ ↦ Prop))
    exact Set.measurable_restrict A
  rw [Measure.map_map hres (by fun_prop)]
  change
    (Measure.infinitePi fun _ : ι ↦
      unitInterval.toNNReal p • Measure.dirac True +
        unitInterval.toNNReal (σ p) • Measure.dirac False).map
          (A.restrict (π := fun _ ↦ Prop)) =
      (Measure.infinitePi fun _ : A ↦
        unitInterval.toNNReal p • Measure.dirac True +
          unitInterval.toNNReal (σ p) • Measure.dirac False).map id
  rw [Measure.infinitePi_map_restrict']
  simp

@[simp]
theorem card_randomEdge (N : ℕ) : Fintype.card (RandomEdge N) = N.choose 2 := by
  simpa using (Sym2.card_diagSet_compl (α := Fin N))

@[simp]
theorem edgeSet_graphOfEdges {N : ℕ} (E : Set (RandomEdge N)) :
    (graphOfEdges E).edgeSet = Subtype.val '' E := by
  rw [graphOfEdges, SimpleGraph.edgeSet_fromEdgeSet]
  apply sdiff_eq_left.mpr
  rw [Set.disjoint_left]
  rintro _ ⟨e, _, rfl⟩
  exact e.property

/-- Edge count without choosing a decidable adjacency relation. -/
def selectedEdgeCount {N : ℕ} (E : Set (RandomEdge N)) : ℕ :=
  Nat.card (graphOfEdges E).edgeSet

@[simp]
theorem selectedEdgeCount_eq_ncard {N : ℕ} (E : Set (RandomEdge N)) :
    selectedEdgeCount E = E.ncard := by
  rw [selectedEdgeCount, edgeSet_graphOfEdges, Nat.card_coe_set_eq,
    Set.ncard_image_of_injective _ Subtype.val_injective]

theorem graphEdgeCount_graphOfEdges {N : ℕ} (E : Set (RandomEdge N))
    [DecidableRel (graphOfEdges E).Adj] :
    graphEdgeCount (graphOfEdges E) = selectedEdgeCount E := by
  rw [graphEdgeCount, selectedEdgeCount, Nat.card_eq_fintype_card,
    SimpleGraph.card_edgeSet]

/-- The ordered coordinates of the cut `S | Sᶜ`.  The order is canonical:
the first endpoint lies in `S` and the second in its complement. -/
abbrev CutIndex {N : ℕ} (S : Finset (Fin N)) := S × (Sᶜ : Finset (Fin N))

/-- A cut coordinate determines its underlying unordered edge. -/
def cutEdgeEmbedding {N : ℕ} (S : Finset (Fin N)) : CutIndex S ↪ RandomEdge N where
  toFun uv := ⟨s(uv.1.1, uv.2.1), by
    simp only [Set.mem_compl_iff, Sym2.mem_diagSet, Sym2.mk_isDiag_iff]
    intro h
    have hu : uv.1.1 ∈ S := uv.1.2
    have hv : uv.2.1 ∉ S := Finset.mem_compl.mp uv.2.2
    exact hv (h ▸ hu)⟩
  inj' := by
    intro uv wz h
    have h' : s(uv.1.1, uv.2.1) = s(wz.1.1, wz.2.1) := congrArg Subtype.val h
    rw [Sym2.eq_iff] at h'
    rcases h' with h' | h'
    · apply Prod.ext <;> apply Subtype.ext
      · exact h'.1
      · exact h'.2
    · exfalso
      have hu : uv.1.1 ∈ S := uv.1.2
      have hw : wz.2.1 ∉ S := Finset.mem_compl.mp wz.2.2
      exact hw (h'.1 ▸ hu)

/-- The possible edges crossing `S | Sᶜ`, viewed as a set of coordinates
in the ambient random graph. -/
def cutEdgeSet {N : ℕ} (S : Finset (Fin N)) : Set (RandomEdge N) :=
  Set.range (cutEdgeEmbedding S)

@[simp]
theorem card_cutIndex {N : ℕ} (S : Finset (Fin N)) :
    Fintype.card (CutIndex S) = #S * (N - #S) := by
  simp [CutIndex]

@[simp]
theorem card_cutEdgeSet {N : ℕ} (S : Finset (Fin N)) :
    Nat.card (cutEdgeSet S) = #S * (N - #S) := by
  rw [cutEdgeSet, Nat.card_range_of_injective (cutEdgeEmbedding S).injective,
    Nat.card_eq_fintype_card, card_cutIndex]

/-- Selected crossing-edge coordinates. -/
def cutSelection {N : ℕ} (S : Finset (Fin N)) (E : Set (RandomEdge N)) :
    Set (cutEdgeSet S) :=
  restrictSet (cutEdgeSet S) E

/-- The number of selected edges crossing `S | Sᶜ`. -/
def sampledCutSize {N : ℕ} (E : Set (RandomEdge N)) (S : Finset (Fin N)) : ℕ :=
  (cutSelection S E).ncard

theorem sampledCutSize_eq_pair_ncard {N : ℕ}
    (E : Set (RandomEdge N)) (S : Finset (Fin N)) :
    sampledCutSize E S =
      {uv : CutIndex S | cutEdgeEmbedding S uv ∈ E}.ncard := by
  rw [sampledCutSize, cutSelection, ncard_restrictSet_eq_inter]
  have himage :
      cutEdgeEmbedding S '' {uv : CutIndex S | cutEdgeEmbedding S uv ∈ E} =
        E ∩ cutEdgeSet S := by
    ext e
    constructor
    · rintro ⟨uv, huv, rfl⟩
      exact ⟨huv, ⟨uv, rfl⟩⟩
    · rintro ⟨he, uv, rfl⟩
      exact ⟨uv, he, rfl⟩
  rw [← himage, Set.ncard_image_of_injective _ (cutEdgeEmbedding S).injective]

@[simp]
theorem cutEdgeEmbedding_mem_iff_adj {N : ℕ}
    (E : Set (RandomEdge N)) (S : Finset (Fin N)) (uv : CutIndex S) :
    cutEdgeEmbedding S uv ∈ E ↔
      (graphOfEdges E).Adj uv.1.1 uv.2.1 := by
  rw [← SimpleGraph.mem_edgeSet, edgeSet_graphOfEdges]
  constructor
  · intro h
    exact ⟨cutEdgeEmbedding S uv, h, rfl⟩
  · rintro ⟨e, he, hval⟩
    have heq : e = cutEdgeEmbedding S uv := Subtype.ext hval
    simpa [heq] using he

private theorem cutSize_eq_pair_ncard {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    cutSize G S =
      {uv : S × (Sᶜ : Finset V) | G.Adj uv.1.1 uv.2.1}.ncard := by
  classical
  rw [cutSize]
  have hfiber (v : V) (hv : v ∈ S) :
      #(G.neighborFinset v \ S) =
        ∑ w ∈ Sᶜ, if G.Adj v w then 1 else 0 := by
    have heq : G.neighborFinset v \ S = (Sᶜ).filter (G.Adj v) := by
      ext w
      simp [SimpleGraph.mem_neighborFinset, and_comm]
    rw [heq, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_congr rfl (fun v hv => hfiber v hv)]
  have hright :
      {uv : S × (Sᶜ : Finset V) | G.Adj uv.1.1 uv.2.1}.ncard =
        #((Finset.univ : Finset (S × (Sᶜ : Finset V))).filter
          fun uv => G.Adj uv.1.1 uv.2.1) := by
    rw [Set.ncard_eq_toFinset_card]
    congr 1
    ext uv
    simp
  rw [hright, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [← S.sum_attach (fun v => ∑ w ∈ Sᶜ, if G.Adj v w then 1 else 0)]
  simp_rw [← (Sᶜ).sum_attach (fun w => if G.Adj _ w then 1 else 0)]
  simp only [Finset.attach_eq_univ]
  exact (Fintype.sum_prod_type
    (fun uv : S × (Sᶜ : Finset V) => if G.Adj uv.1.1 uv.2.1 then 1 else 0)).symm

@[simp]
theorem cutSize_graphOfEdges_eq_sampledCutSize {N : ℕ}
    (E : Set (RandomEdge N)) (S : Finset (Fin N))
    [DecidableRel (graphOfEdges E).Adj] :
    cutSize (graphOfEdges E) S = sampledCutSize E S := by
  rw [cutSize_eq_pair_ncard, sampledCutSize_eq_pair_ncard]
  congr 1
  ext uv
  exact (cutEdgeEmbedding_mem_iff_adj E S uv).symm

/-- The graph-theoretic cut count with the irrelevant decidability choice
hidden.  This makes it a genuine function on the finite graph space. -/
def canonicalCutSize {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) : ℕ := by
  classical
  exact cutSize G S

/-- The actual graph-theoretic cut count of a selected edge set. -/
def randomGraphCutSize {N : ℕ} (E : Set (RandomEdge N)) (S : Finset (Fin N)) : ℕ :=
  canonicalCutSize (graphOfEdges E) S

@[simp]
theorem randomGraphCutSize_eq_sampledCutSize {N : ℕ}
    (E : Set (RandomEdge N)) (S : Finset (Fin N)) :
    randomGraphCutSize E S = sampledCutSize E S := by
  classical
  unfold randomGraphCutSize canonicalCutSize
  exact cutSize_graphOfEdges_eq_sampledCutSize E S

private theorem map_ncard_setBernoulli_univ (ι : Type*) [Finite ι] (p : unitInterval) :
    setBer((Set.univ : Set ι), p).map Set.ncard = Bin(Nat.card ι, p) := by
  apply Measure.ext_of_singleton
  intro k
  rw [map_ncard_setBernoulli_singleton (Set.toFinite _), binomial_singleton]
  simp

private theorem map_ncard_restrictSet_setBernoulli_univ
    {ι : Type*} [Finite ι] (A : Set ι) (p : unitInterval) :
    setBer((Set.univ : Set ι), p).map (fun E => (restrictSet A E).ncard) =
      Bin(Nat.card A, p) := by
  have hres : Measurable (restrictSet A) := by
    change Measurable (A.restrict (π := fun _ ↦ Prop))
    exact Set.measurable_restrict A
  change setBer((Set.univ : Set ι), p).map
      ((Set.ncard : Set A → ℕ) ∘ restrictSet A) = Bin(Nat.card A, p)
  rw [← Measure.map_map (by fun_prop : Measurable (Set.ncard : Set A → ℕ)) hres,
    map_restrictSet_setBernoulli_univ, map_ncard_setBernoulli_univ]

/-- The total number of selected edges has the binomial distribution with
`N.choose 2` trials. -/
theorem map_selectedEdgeCount_randomEdgeMeasure (N : ℕ) (p : unitInterval) :
    (randomEdgeMeasure N p).map (fun E => selectedEdgeCount E) =
      Bin(N.choose 2, p) := by
  have hfun : (fun E : Set (RandomEdge N) => selectedEdgeCount E) = Set.ncard := by
    funext E
    exact selectedEdgeCount_eq_ncard E
  rw [hfun, randomEdgeMeasure, map_ncard_setBernoulli_univ]
  rw [Nat.card_eq_fintype_card, card_randomEdge]

/-- `selectedEdgeCount` as a random variable has binomial law. -/
theorem hasLaw_selectedEdgeCount (N : ℕ) (p : unitInterval) :
    HasLaw (fun E : Set (RandomEdge N) => selectedEdgeCount E)
      Bin(N.choose 2, p) (randomEdgeMeasure N p) where
  aemeasurable := by
    rw [show (fun E : Set (RandomEdge N) => selectedEdgeCount E) = Set.ncard by
      funext E; exact selectedEdgeCount_eq_ncard E]
    fun_prop
  map_eq := map_selectedEdgeCount_randomEdgeMeasure N p

/-- A fixed cut has the binomial distribution with
`|S| (N - |S|)` trials. -/
theorem map_sampledCutSize_randomEdgeMeasure
    (N : ℕ) (p : unitInterval) (S : Finset (Fin N)) :
    (randomEdgeMeasure N p).map (fun E => sampledCutSize E S) =
      Bin(#S * (N - #S), p) := by
  rw [randomEdgeMeasure]
  change setBer((Set.univ : Set (RandomEdge N)), p).map
      (fun E => (restrictSet (cutEdgeSet S) E).ncard) = _
  rw [map_ncard_restrictSet_setBernoulli_univ, card_cutEdgeSet]

/-- `sampledCutSize` as a random variable has the exact binomial law used by
Chernoff bounds later in the construction. -/
theorem hasLaw_sampledCutSize (N : ℕ) (p : unitInterval) (S : Finset (Fin N)) :
    HasLaw (fun E : Set (RandomEdge N) => sampledCutSize E S)
      Bin(#S * (N - #S), p) (randomEdgeMeasure N p) where
  aemeasurable := by
    change AEMeasurable
      (fun E : Set (RandomEdge N) => (restrictSet (cutEdgeSet S) E).ncard) _
    apply Measurable.aemeasurable
    exact (by fun_prop : Measurable (Set.ncard : Set (cutEdgeSet S) → ℕ)).comp
      (by
        change Measurable ((cutEdgeSet S).restrict (π := fun _ ↦ Prop))
        exact Set.measurable_restrict _)
  map_eq := map_sampledCutSize_randomEdgeMeasure N p S

/-- The graph-theoretic cut size itself has the same exact binomial law. -/
theorem hasLaw_randomGraphCutSize
    (N : ℕ) (p : unitInterval) (S : Finset (Fin N)) :
    HasLaw (fun E : Set (RandomEdge N) => randomGraphCutSize E S)
      Bin(#S * (N - #S), p) (randomEdgeMeasure N p) := by
  apply (hasLaw_sampledCutSize N p S).congr
  filter_upwards [] with E
  exact randomGraphCutSize_eq_sampledCutSize E S

/-- Under the induced measure on graphs, the graph edge count is still
exactly binomial. -/
theorem map_edgeCount_randomGraphMeasure (N : ℕ) (p : unitInterval) :
    (randomGraphMeasure N p).map (fun G => Nat.card G.edgeSet) =
      Bin(N.choose 2, p) := by
  rw [randomGraphMeasure,
    Measure.map_map (measurable_of_finite _) (measurable_graphOfEdges N)]
  change (randomEdgeMeasure N p).map (fun E => selectedEdgeCount E) = _
  exact map_selectedEdgeCount_randomEdgeMeasure N p

theorem hasLaw_edgeCount_randomGraphMeasure (N : ℕ) (p : unitInterval) :
    HasLaw (fun G : SimpleGraph (Fin N) => Nat.card G.edgeSet)
      Bin(N.choose 2, p) (randomGraphMeasure N p) where
  aemeasurable := (measurable_of_finite _).aemeasurable
  map_eq := map_edgeCount_randomGraphMeasure N p

/-- Under the induced measure on graphs, the graph-theoretic size of a fixed
cut has the same binomial law. -/
theorem map_cutSize_randomGraphMeasure
    (N : ℕ) (p : unitInterval) (S : Finset (Fin N)) :
    (randomGraphMeasure N p).map (fun G => canonicalCutSize G S) =
      Bin(#S * (N - #S), p) := by
  rw [randomGraphMeasure,
    Measure.map_map (measurable_of_finite _) (measurable_graphOfEdges N)]
  change (randomEdgeMeasure N p).map (fun E => randomGraphCutSize E S) = _
  exact (hasLaw_randomGraphCutSize N p S).map_eq

theorem hasLaw_cutSize_randomGraphMeasure
    (N : ℕ) (p : unitInterval) (S : Finset (Fin N)) :
    HasLaw (fun G : SimpleGraph (Fin N) => canonicalCutSize G S)
      Bin(#S * (N - #S), p) (randomGraphMeasure N p) where
  aemeasurable := (measurable_of_finite _).aemeasurable
  map_eq := map_cutSize_randomGraphMeasure N p S

/-! The following identities put the two tails used by the alteration
argument directly in the form expected by binomial Chernoff bounds. -/

theorem measureReal_selectedEdgeCount_ge_eq_binomial
    (N : ℕ) (p : unitInterval) (a : ℝ) :
    (randomEdgeMeasure N p).real
        {E | a ≤ (selectedEdgeCount E : ℝ)} =
      Bin(N.choose 2, p).real {k : ℕ | a ≤ (k : ℝ)} := by
  exact (hasLaw_selectedEdgeCount N p).measureReal_eq
    (p := fun k : ℕ => a ≤ (k : ℝ)) (by measurability)

theorem measureReal_randomGraphCutSize_le_eq_binomial
    (N : ℕ) (p : unitInterval) (S : Finset (Fin N)) (a : ℝ) :
    (randomEdgeMeasure N p).real
        {E | (randomGraphCutSize E S : ℝ) ≤ a} =
      Bin(#S * (N - #S), p).real {k : ℕ | (k : ℝ) ≤ a} := by
  exact (hasLaw_randomGraphCutSize N p S).measureReal_eq
    (p := fun k : ℕ => (k : ℝ) ≤ a) (by measurability)

theorem measureReal_graphEdgeCount_ge_eq_binomial
    (N : ℕ) (p : unitInterval) (a : ℝ) :
    (randomGraphMeasure N p).real
        {G | a ≤ (Nat.card G.edgeSet : ℝ)} =
      Bin(N.choose 2, p).real {k : ℕ | a ≤ (k : ℝ)} := by
  exact (hasLaw_edgeCount_randomGraphMeasure N p).measureReal_eq
    (p := fun k : ℕ => a ≤ (k : ℝ)) (by measurability)

theorem measureReal_graphCutSize_le_eq_binomial
    (N : ℕ) (p : unitInterval) (S : Finset (Fin N)) (a : ℝ) :
    (randomGraphMeasure N p).real
        {G | (canonicalCutSize G S : ℝ) ≤ a} =
      Bin(#S * (N - #S), p).real {k : ℕ | (k : ℝ) ≤ a} := by
  exact (hasLaw_cutSize_randomGraphMeasure N p S).measureReal_eq
    (p := fun k : ℕ => (k : ℝ) ≤ a) (by measurability)

end

end LeanCo.HypercubeTuran
