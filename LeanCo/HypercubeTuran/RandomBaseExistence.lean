import LeanCo.HypercubeTuran.RandomGraph
import LeanCo.HypercubeTuran.RandomAux

/-!
# Simultaneous pseudorandom properties of a finite binomial graph

This file packages the four bad-event families needed for the base graph:
too many total edges, a sparse cut, a large independent set, and a small
vertex set spanning too many edges.  The first main result is deliberately
parameterized by the numerical probability estimates, so choices of
`N`, `p`, and `d` can be improved without changing the combinatorial layer.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal Finset ProbabilityTheory SimpleGraph unitInterval

namespace LeanCo.HypercubeTuran

noncomputable section

namespace RB

/-- Non-diagonal unordered pairs of vertices of `U`. -/
abbrev InternalEdgeIndex {N : ℕ} (U : Finset (Fin N)) :=
  (Sym2.diagSetᶜ : Set (Sym2 U))

/-- Include an unordered pair from `U` into the ambient edge coordinates. -/
def internalEdgeEmbedding {N : ℕ} (U : Finset (Fin N)) :
    InternalEdgeIndex U ↪ RandomEdge N where
  toFun e := ⟨(Function.Embedding.subtype _).sym2Map e.1, by
    simpa only [Set.mem_compl_iff, Sym2.mem_diagSet,
      Function.Embedding.sym2Map_apply, Sym2.isDiag_map
        (Function.Embedding.subtype _).injective] using e.2⟩
  inj' := by
    intro e f h
    apply Subtype.ext
    exact (Function.Embedding.subtype _).sym2Map.injective
      (congrArg Subtype.val h)

/-- All possible ambient edges whose endpoints lie in `U`. -/
def internalEdgeFinset {N : ℕ} (U : Finset (Fin N)) : Finset (RandomEdge N) :=
  Finset.univ.map (internalEdgeEmbedding U)

@[simp]
theorem card_internalEdgeIndex {N : ℕ} (U : Finset (Fin N)) :
    Fintype.card (InternalEdgeIndex U) = (#U).choose 2 := by
  rw [Sym2.card_diagSet_compl, Fintype.card_coe]

@[simp]
theorem card_internalEdgeFinset {N : ℕ} (U : Finset (Fin N)) :
    #(internalEdgeFinset U) = (#U).choose 2 := by
  rw [internalEdgeFinset, Finset.card_map, Finset.card_univ,
    card_internalEdgeIndex]

/-- Number of selected edge coordinates internal to `U`. -/
def internalEdgeCount {N : ℕ} (E : Set (RandomEdge N))
    (U : Finset (Fin N)) : ℕ :=
  #(selectedFinset (internalEdgeFinset U) E)

/-- The internal coordinate determined by two distinct vertices of `U`. -/
def internalEdgeOfNe {N : ℕ} (U : Finset (Fin N))
    (u v : U) (huv : u ≠ v) : InternalEdgeIndex U :=
  ⟨s(u, v), Sym2.mk_isDiag_iff.not.2 huv⟩

@[simp]
theorem internalEdgeOfNe_mem_iff_adj {N : ℕ}
    (E : Set (RandomEdge N)) (U : Finset (Fin N))
    (u v : U) (huv : u ≠ v) :
    internalEdgeEmbedding U (internalEdgeOfNe U u v huv) ∈ E ↔
      (graphOfEdges E).Adj u.1 v.1 := by
  rw [← SimpleGraph.mem_edgeSet, edgeSet_graphOfEdges]
  have hval :
      (internalEdgeEmbedding U (internalEdgeOfNe U u v huv) : RandomEdge N).1 =
        s(u.1, v.1) := by
    simp [internalEdgeEmbedding, internalEdgeOfNe,
      Function.Embedding.sym2Map_apply]
  constructor
  · intro h
    exact ⟨internalEdgeEmbedding U (internalEdgeOfNe U u v huv), h, hval⟩
  · rintro ⟨e, he, h⟩
    have heq : e = internalEdgeEmbedding U (internalEdgeOfNe U u v huv) :=
      Subtype.ext (h.trans hval.symm)
    simpa [heq] using he

/-- An independent vertex set contains no selected internal coordinate. -/
theorem internalEdgeCount_eq_zero_of_isIndepSet {N : ℕ}
    (E : Set (RandomEdge N)) (U : Finset (Fin N))
    (hU : (graphOfEdges E).IsIndepSet (U : Set (Fin N))) :
    internalEdgeCount E U = 0 := by
  classical
  by_contra hne
  have hpos : 0 < internalEdgeCount E U := Nat.pos_of_ne_zero hne
  rw [internalEdgeCount, Finset.card_pos] at hpos
  obtain ⟨x, hx⟩ := hpos
  rw [mem_selectedFinset] at hx
  obtain ⟨hxA, hxE⟩ := hx
  rcases Finset.mem_map.mp hxA with ⟨e, _, rfl⟩
  obtain ⟨z, hz⟩ := e
  revert hz hxE
  refine Sym2.ind ?_ z
  intro u v hdiag _ _ hE
  have huv : u ≠ v := Sym2.mk_isDiag_iff.not.mp hdiag
  have hval : u.1 ≠ v.1 := fun h => huv (Subtype.ext h)
  have hadj : (graphOfEdges E).Adj u.1 v.1 :=
    (internalEdgeOfNe_mem_iff_adj E U u v huv).mp (by
      simpa [internalEdgeOfNe] using hE)
  exact hU u.2 v.2 hval hadj

/-- Bridge from the canonical cut random variable to `cutSize` computed with
any decidability instance chosen by a downstream construction. -/
theorem randomGraphCutSize_eq_cutSize {N : ℕ}
    (E : Set (RandomEdge N)) (S : Finset (Fin N))
    [DecidableRel (graphOfEdges E).Adj] :
    randomGraphCutSize E S = cutSize (graphOfEdges E) S := by
  rw [randomGraphCutSize_eq_sampledCutSize,
    cutSize_graphOfEdges_eq_sampledCutSize]

/-- Vanishing internal-edge count is exactly disjointness from the finite set
of candidate internal edges. -/
theorem internalEdgeCount_eq_zero_iff_disjoint {N : ℕ}
    (E : Set (RandomEdge N)) (U : Finset (Fin N)) :
    internalEdgeCount E U = 0 ↔
      Disjoint (internalEdgeFinset U : Set (RandomEdge N)) E := by
  classical
  simp [internalEdgeCount, Finset.card_eq_zero,
    Finset.eq_empty_iff_forall_notMem,
    mem_selectedFinset, Set.disjoint_left]

/-! ## Fixed absent-coordinate probability -/

/-- Every coordinate of a fixed finite set is absent with probability
`(1-p)^|A|`. -/
theorem setBernoulli_disjoint_finset_apply {ι : Type*} [Countable ι]
    (u : Set ι) (p : unitInterval) (A : Finset ι)
    (hA : (A : Set ι) ⊆ u) :
    setBer(u, p) {s : Set ι | Disjoint (A : Set ι) s} =
      (unitInterval.toNNReal (σ p) : ℝ≥0∞) ^ #A := by
  rw [setBernoulli_apply']
  let T : Set ((i : A) → Prop) := {q | ∀ i, ¬ q i}
  have hevent :
      (fun q : ι → Prop => {i | q i}) ⁻¹'
          {s : Set ι | Disjoint (A : Set ι) s} =
        cylinder A T := by
    ext q
    simp only [Set.mem_preimage, Set.mem_setOf_eq, mem_cylinder, T]
    constructor
    · intro h i hi
      exact (Set.disjoint_left.1 h i.property) hi
    · intro h
      rw [Set.disjoint_left]
      intro i hiA hiq
      exact (h ⟨i, hiA⟩) hiq
  rw [hevent, Measure.infinitePi_cylinder _ (by measurability : MeasurableSet T)]
  have hT : T = {fun _ => False} := by
    ext q
    simp only [T, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro h
      funext i
      exact propext ⟨fun hi => (h i hi).elim, False.elim⟩
    · rintro rfl i
      exact id
  rw [hT, Measure.pi_singleton]
  have hfactor (i : A) :
      (unitInterval.toNNReal p • Measure.dirac ((i : ι) ∈ u) +
        unitInterval.toNNReal (σ p) • Measure.dirac False) {False} =
          (unitInterval.toNNReal (σ p) : ℝ≥0∞) := by
    simp [hA i.property]
  simp_rw [hfactor]
  simp

theorem setBernoulli_disjoint_finset_apply_real {ι : Type*} [Countable ι]
    (u : Set ι) (p : unitInterval) (A : Finset ι)
    (hA : (A : Set ι) ⊆ u) :
    setBer(u, p).real {s : Set ι | Disjoint (A : Set ι) s} =
      (1 - (p : ℝ)) ^ #A := by
  rw [measureReal_def, setBernoulli_disjoint_finset_apply u p A hA]
  simp [unitInterval.coe_toNNReal]

/-- Exact probability that a fixed vertex set spans no sampled edge. -/
theorem measureReal_internalEdgeCount_eq_zero
    (N : ℕ) (p : unitInterval) (U : Finset (Fin N)) :
    (randomEdgeMeasure N p).real
        {E | internalEdgeCount E U = 0} =
      (1 - (p : ℝ)) ^ ((#U).choose 2) := by
  have hevent :
      {E : Set (RandomEdge N) | internalEdgeCount E U = 0} =
        {E | Disjoint (internalEdgeFinset U : Set (RandomEdge N)) E} := by
    ext E
    exact internalEdgeCount_eq_zero_iff_disjoint E U
  rw [hevent, randomEdgeMeasure,
    setBernoulli_disjoint_finset_apply_real]
  · rw [card_internalEdgeFinset]
  · simp

/-- Union-bound upper tail for the edges spanned by one fixed vertex set. -/
theorem measureReal_internalEdgeCount_ge_le
    (N : ℕ) (p : unitInterval) (U : Finset (Fin N)) (m : ℕ) :
    (randomEdgeMeasure N p).real
        {E | m ≤ internalEdgeCount E U} ≤
      ((((#U).choose 2).choose m : ℕ) : ℝ) * (p : ℝ) ^ m := by
  simpa only [randomEdgeMeasure, internalEdgeCount,
    card_internalEdgeFinset] using
      (setBernoulli_fixedSet_tail_real
        (Set.univ : Set (RandomEdge N)) p (internalEdgeFinset U)
        (by simp) m)

/-! ## The four good properties and their bad events -/

/-- The strengthened finite source properties preserved by deleting one
edge from every short cycle. -/
structure IsGoodSource {N : ℕ} (E : Set (RandomEdge N)) (d g : ℕ) : Prop where
  edge_control : 4 * selectedEdgeCount E ≤ 5 * d * N
  cut_expansion : ∀ S : Finset (Fin N),
    8 * d * #S * (N - #S) ≤ 5 * N * randomGraphCutSize E S
  small_independent : ∀ A : Finset (Fin N),
    (graphOfEdges E).IsIndepSet (A : Set (Fin N)) → 300 * #A < N
  locally_sparse : ∀ U : Finset (Fin N), #U ≤ 2 * g →
    internalEdgeCount E U ≤ #U

def badEdgeEvent (N d : ℕ) : Set (Set (RandomEdge N)) :=
  {E | 5 * d * N < 4 * selectedEdgeCount E}

def badCutEvent (N d : ℕ) : Set (Set (RandomEdge N)) :=
  {E | ∃ S : Finset (Fin N),
    5 * N * randomGraphCutSize E S < 8 * d * #S * (N - #S)}

def badIndependentEvent (N : ℕ) : Set (Set (RandomEdge N)) :=
  {E | ∃ A : Finset (Fin N),
    N ≤ 300 * #A ∧ internalEdgeCount E A = 0}

def badLocalSparsityEvent (N g : ℕ) : Set (Set (RandomEdge N)) :=
  {E | ∃ U : Finset (Fin N),
    #U ≤ 2 * g ∧ #U + 1 ≤ internalEdgeCount E U}

def badSourceEvent (N d g : ℕ) : Set (Set (RandomEdge N)) :=
  badEdgeEvent N d ∪ badCutEvent N d ∪
    badIndependentEvent N ∪ badLocalSparsityEvent N g

/-- The vertex sets that are large enough to violate the desired
independence-number bound. -/
def largeVertexSets (N : ℕ) : Finset (Finset (Fin N)) :=
  Finset.univ.filter fun A => N ≤ 300 * #A

@[simp]
theorem mem_largeVertexSets {N : ℕ} {A : Finset (Fin N)} :
    A ∈ largeVertexSets N ↔ N ≤ 300 * #A := by
  simp [largeVertexSets]

/-- The vertex sets on which local sparsity is required. -/
def smallVertexSets (N g : ℕ) : Finset (Finset (Fin N)) :=
  Finset.univ.filter fun U => #U ≤ 2 * g

@[simp]
theorem mem_smallVertexSets {N g : ℕ} {U : Finset (Fin N)} :
    U ∈ smallVertexSets N g ↔ #U ≤ 2 * g := by
  simp [smallVertexSets]

/-- All `u`-element vertex sets. -/
def vertexSetsOfCard (N u : ℕ) : Finset (Finset (Fin N)) :=
  (Finset.univ : Finset (Fin N)).powersetCard u

@[simp]
theorem mem_vertexSetsOfCard {N u : ℕ} {U : Finset (Fin N)} :
    U ∈ vertexSetsOfCard N u ↔ #U = u := by
  simp [vertexSetsOfCard]

@[simp]
theorem card_vertexSetsOfCard (N u : ℕ) :
    #(vertexSetsOfCard N u) = N.choose u := by
  rw [vertexSetsOfCard, Finset.card_powersetCard, Finset.card_univ,
    Fintype.card_fin]

/-! ## Exact and finite-sum estimates for the four bad-event families -/

theorem measureReal_badEdgeEvent_eq_binomial
    (N d : ℕ) (p : unitInterval) :
    (randomEdgeMeasure N p).real (badEdgeEvent N d) =
      Bin(N.choose 2, p).real {k : ℕ | 5 * d * N < 4 * k} := by
  simpa only [badEdgeEvent, Set.mem_setOf_eq] using
    (hasLaw_selectedEdgeCount N p).measureReal_eq
      (p := fun k : ℕ => 5 * d * N < 4 * k) (by measurability)

/-- Exponential-transform upper bound for the total-edge failure event. -/
theorem measureReal_badEdgeEvent_le_chernoff
    (N d : ℕ) (p : unitInterval) {t : ℝ} (ht : 0 < t) :
    (randomEdgeMeasure N p).real (badEdgeEvent N d) ≤
      Real.exp (-t * (((5 * d * N : ℕ) : ℝ) / 4)) *
        (1 - (p : ℝ) + (p : ℝ) * Real.exp t) ^ (N.choose 2) := by
  let a : ℝ := ((5 * d * N : ℕ) : ℝ) / 4
  calc
    (randomEdgeMeasure N p).real (badEdgeEvent N d) ≤
        (randomEdgeMeasure N p).real
          {E | a ≤ (selectedEdgeCount E : ℝ)} := by
      apply measureReal_mono
      · intro E hE
        change 5 * d * N < 4 * selectedEdgeCount E at hE
        have hcast : ((5 * d * N : ℕ) : ℝ) <
            4 * (selectedEdgeCount E : ℝ) := by
          exact_mod_cast hE
        dsimp only [a]
        exact ((div_lt_iff₀ (by norm_num : (0 : ℝ) < 4)).2
          (by simpa [mul_comm] using hcast)).le
      · finiteness
    _ = Bin(N.choose 2, p).real {k : ℕ | a ≤ (k : ℝ)} :=
      measureReal_selectedEdgeCount_ge_eq_binomial N p a
    _ ≤ Real.exp (-t * a) *
        (1 - (p : ℝ) + (p : ℝ) * Real.exp t) ^ (N.choose 2) :=
      binomial_chernoff_upper (N.choose 2) p ht a
    _ = _ := rfl

/-- Direct union bound over all cuts, retaining each exact binomial tail. -/
theorem measureReal_badCutEvent_le_binomial_sum
    (N d : ℕ) (p : unitInterval) :
    (randomEdgeMeasure N p).real (badCutEvent N d) ≤
      ∑ S : Finset (Fin N),
        Bin(#S * (N - #S), p).real
          {k : ℕ | 5 * N * k < 8 * d * #S * (N - #S)} := by
  let event : Finset (Fin N) → Set (Set (RandomEdge N)) := fun S =>
    {E | 5 * N * randomGraphCutSize E S <
      8 * d * #S * (N - #S)}
  calc
    (randomEdgeMeasure N p).real (badCutEvent N d) =
        (randomEdgeMeasure N p).real
          {E | ∃ S ∈ (Finset.univ : Finset (Finset (Fin N))), E ∈ event S} := by
      congr 1
      ext E
      simp [badCutEvent, event]
    _ ≤ ∑ S ∈ (Finset.univ : Finset (Finset (Fin N))),
          (randomEdgeMeasure N p).real (event S) :=
      measureReal_exists_mem_finset_le _ _ _
    _ = ∑ S : Finset (Fin N),
        Bin(#S * (N - #S), p).real
          {k : ℕ | 5 * N * k < 8 * d * #S * (N - #S)} := by
      apply Finset.sum_congr rfl
      intro S _
      simpa only [event, Set.mem_setOf_eq] using
        (hasLaw_randomGraphCutSize N p S).measureReal_eq
          (p := fun k : ℕ =>
            5 * N * k < 8 * d * #S * (N - #S)) (by measurability)

/-- Exponential-transform lower-tail bound for one specified bad cut. -/
theorem measureReal_badCutAt_le_chernoff
    {N : ℕ} (hN : 0 < N) (d : ℕ) (p : unitInterval)
    (S : Finset (Fin N)) {t : ℝ} (ht : t < 0) :
    (randomEdgeMeasure N p).real
        {E | 5 * N * randomGraphCutSize E S <
          8 * d * #S * (N - #S)} ≤
      Real.exp (-t *
          (((8 * d * #S * (N - #S) : ℕ) : ℝ) /
            ((5 * N : ℕ) : ℝ))) *
        (1 - (p : ℝ) + (p : ℝ) * Real.exp t) ^
          (#S * (N - #S)) := by
  let a : ℝ := ((8 * d * #S * (N - #S) : ℕ) : ℝ) /
    ((5 * N : ℕ) : ℝ)
  have hden : (0 : ℝ) < ((5 * N : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mul_pos (by norm_num : 0 < 5) hN)
  calc
    (randomEdgeMeasure N p).real
        {E | 5 * N * randomGraphCutSize E S <
          8 * d * #S * (N - #S)} ≤
        (randomEdgeMeasure N p).real
          {E | (randomGraphCutSize E S : ℝ) ≤ a} := by
      apply measureReal_mono
      · intro E hE
        change 5 * N * randomGraphCutSize E S <
          8 * d * #S * (N - #S) at hE
        change (randomGraphCutSize E S : ℝ) ≤ a
        dsimp only [a]
        rw [le_div_iff₀ hden]
        have hcast : ((5 * N * randomGraphCutSize E S : ℕ) : ℝ) <
            ((8 * d * #S * (N - #S) : ℕ) : ℝ) := by
          exact_mod_cast hE
        norm_num only [Nat.cast_mul] at hcast ⊢
        nlinarith
      · finiteness
    _ = Bin(#S * (N - #S), p).real
        {k : ℕ | (k : ℝ) ≤ a} :=
      measureReal_randomGraphCutSize_le_eq_binomial N p S a
    _ ≤ Real.exp (-t * a) *
        (1 - (p : ℝ) + (p : ℝ) * Real.exp t) ^
          (#S * (N - #S)) :=
      binomial_chernoff_lower
        (#S * (N - #S)) p ht a
    _ = _ := rfl

/-- Union of the preceding fixed-cut Chernoff estimates. -/
theorem measureReal_badCutEvent_le_chernoff_sum
    {N : ℕ} (hN : 0 < N) (d : ℕ) (p : unitInterval)
    {t : ℝ} (ht : t < 0) :
    (randomEdgeMeasure N p).real (badCutEvent N d) ≤
      ∑ S : Finset (Fin N),
        Real.exp (-t *
            (((8 * d * #S * (N - #S) : ℕ) : ℝ) /
              ((5 * N : ℕ) : ℝ))) *
          (1 - (p : ℝ) + (p : ℝ) * Real.exp t) ^
            (#S * (N - #S)) := by
  let event : Finset (Fin N) → Set (Set (RandomEdge N)) := fun S =>
    {E | 5 * N * randomGraphCutSize E S <
      8 * d * #S * (N - #S)}
  calc
    (randomEdgeMeasure N p).real (badCutEvent N d) =
        (randomEdgeMeasure N p).real
          {E | ∃ S ∈ (Finset.univ : Finset (Finset (Fin N))), E ∈ event S} := by
      congr 1
      ext E
      simp [badCutEvent, event]
    _ ≤ ∑ S ∈ (Finset.univ : Finset (Finset (Fin N))),
          (randomEdgeMeasure N p).real (event S) :=
      measureReal_exists_mem_finset_le _ _ _
    _ ≤ ∑ S : Finset (Fin N),
        Real.exp (-t *
            (((8 * d * #S * (N - #S) : ℕ) : ℝ) /
              ((5 * N : ℕ) : ℝ))) *
          (1 - (p : ℝ) + (p : ℝ) * Real.exp t) ^
            (#S * (N - #S)) := by
      apply Finset.sum_le_sum
      intro S _
      exact measureReal_badCutAt_le_chernoff hN d p S ht

/-- Bad cuts having a prescribed side cardinality. -/
def badCutEventAtSize (N d u : ℕ) : Set (Set (RandomEdge N)) :=
  {E | ∃ S ∈ vertexSetsOfCard N u,
    5 * N * randomGraphCutSize E S < 8 * d * u * (N - u)}

theorem badCutEvent_eq_iUnion_size (N d : ℕ) :
    badCutEvent N d =
      {E | ∃ u ∈ Finset.range (N + 1), E ∈ badCutEventAtSize N d u} := by
  ext E
  constructor
  · rintro ⟨S, hbad⟩
    have hcard : #S ≤ N := by
      simpa using Finset.card_le_univ S
    refine ⟨#S, Finset.mem_range.2 (Nat.lt_succ_of_le hcard), S, ?_, ?_⟩
    · exact mem_vertexSetsOfCard.2 rfl
    · exact hbad
  · rintro ⟨u, _, S, hS, hbad⟩
    have hcard : #S = u := mem_vertexSetsOfCard.mp hS
    refine ⟨S, ?_⟩
    simpa only [hcard] using hbad

/-- Fixed-cardinality cut bound; the binomial tail is now multiplied by
exactly `choose(N,u)`. -/
theorem measureReal_badCutEventAtSize_le_chernoff
    {N : ℕ} (hN : 0 < N) (d u : ℕ) (p : unitInterval)
    {t : ℝ} (ht : t < 0) :
    (randomEdgeMeasure N p).real (badCutEventAtSize N d u) ≤
      (N.choose u : ℝ) *
        (Real.exp (-t *
            (((8 * d * u * (N - u) : ℕ) : ℝ) /
              ((5 * N : ℕ) : ℝ))) *
          (1 - (p : ℝ) + (p : ℝ) * Real.exp t) ^
            (u * (N - u))) := by
  let event : Finset (Fin N) → Set (Set (RandomEdge N)) := fun S =>
    {E | 5 * N * randomGraphCutSize E S < 8 * d * u * (N - u)}
  calc
    (randomEdgeMeasure N p).real (badCutEventAtSize N d u) ≤
        ∑ S ∈ vertexSetsOfCard N u,
          (randomEdgeMeasure N p).real (event S) := by
      exact measureReal_exists_mem_finset_le _ _ _
    _ ≤ ∑ _S ∈ vertexSetsOfCard N u,
        (Real.exp (-t *
            (((8 * d * u * (N - u) : ℕ) : ℝ) /
              ((5 * N : ℕ) : ℝ))) *
          (1 - (p : ℝ) + (p : ℝ) * Real.exp t) ^
            (u * (N - u))) := by
      apply Finset.sum_le_sum
      intro S hS
      have hcard : #S = u := mem_vertexSetsOfCard.mp hS
      simpa only [event, hcard, Set.mem_setOf_eq] using
        (measureReal_badCutAt_le_chernoff hN d p S ht)
    _ = (N.choose u : ℝ) *
        (Real.exp (-t *
            (((8 * d * u * (N - u) : ℕ) : ℝ) /
              ((5 * N : ℕ) : ℝ))) *
          (1 - (p : ℝ) + (p : ℝ) * Real.exp t) ^
            (u * (N - u))) := by
      rw [Finset.sum_const, nsmul_eq_mul, card_vertexSetsOfCard]

/-- Cardinality-compressed union bound for all cuts. -/
theorem measureReal_badCutEvent_le_chernoff_size_sum
    {N : ℕ} (hN : 0 < N) (d : ℕ) (p : unitInterval)
    {t : ℝ} (ht : t < 0) :
    (randomEdgeMeasure N p).real (badCutEvent N d) ≤
      ∑ u ∈ Finset.range (N + 1),
        (N.choose u : ℝ) *
          (Real.exp (-t *
              (((8 * d * u * (N - u) : ℕ) : ℝ) /
                ((5 * N : ℕ) : ℝ))) *
            (1 - (p : ℝ) + (p : ℝ) * Real.exp t) ^
              (u * (N - u))) := by
  rw [badCutEvent_eq_iUnion_size]
  calc
    (randomEdgeMeasure N p).real
        {E | ∃ u ∈ Finset.range (N + 1), E ∈ badCutEventAtSize N d u} ≤
        ∑ u ∈ Finset.range (N + 1),
          (randomEdgeMeasure N p).real (badCutEventAtSize N d u) :=
      measureReal_exists_mem_finset_le _ _ _
    _ ≤ ∑ u ∈ Finset.range (N + 1),
        (N.choose u : ℝ) *
          (Real.exp (-t *
              (((8 * d * u * (N - u) : ℕ) : ℝ) /
                ((5 * N : ℕ) : ℝ))) *
            (1 - (p : ℝ) + (p : ℝ) * Real.exp t) ^
              (u * (N - u))) := by
      apply Finset.sum_le_sum
      intro u _
      exact measureReal_badCutEventAtSize_le_chernoff hN d u p ht

/-- Union bound over all vertex sets large enough to violate the
independence-number target. -/
theorem measureReal_badIndependentEvent_le_sum
    (N : ℕ) (p : unitInterval) :
    (randomEdgeMeasure N p).real (badIndependentEvent N) ≤
      ∑ A ∈ largeVertexSets N,
        (1 - (p : ℝ)) ^ ((#A).choose 2) := by
  let event : Finset (Fin N) → Set (Set (RandomEdge N)) := fun A =>
    {E | internalEdgeCount E A = 0}
  calc
    (randomEdgeMeasure N p).real (badIndependentEvent N) =
        (randomEdgeMeasure N p).real
          {E | ∃ A ∈ largeVertexSets N, E ∈ event A} := by
      congr 1
      ext E
      simp [badIndependentEvent, event]
    _ ≤ ∑ A ∈ largeVertexSets N,
          (randomEdgeMeasure N p).real (event A) :=
      measureReal_exists_mem_finset_le _ _ _
    _ = ∑ A ∈ largeVertexSets N,
        (1 - (p : ℝ)) ^ ((#A).choose 2) := by
      apply Finset.sum_congr rfl
      intro A _
      exact measureReal_internalEdgeCount_eq_zero N p A

/-- Cardinalities large enough to violate `300 * α < N`. -/
def largeVertexSizes (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter fun u => N ≤ 300 * u

@[simp]
theorem mem_largeVertexSizes {N u : ℕ} :
    u ∈ largeVertexSizes N ↔ u ≤ N ∧ N ≤ 300 * u := by
  simp [largeVertexSizes, Nat.lt_succ_iff]

/-- Absence of all internal edges on some `u`-vertex set. -/
def badIndependentEventAtSize (N u : ℕ) : Set (Set (RandomEdge N)) :=
  {E | ∃ A ∈ vertexSetsOfCard N u, internalEdgeCount E A = 0}

theorem measureReal_badIndependentEventAtSize_le
    (N u : ℕ) (p : unitInterval) :
    (randomEdgeMeasure N p).real (badIndependentEventAtSize N u) ≤
      (N.choose u : ℝ) * (1 - (p : ℝ)) ^ (u.choose 2) := by
  let event : Finset (Fin N) → Set (Set (RandomEdge N)) := fun A =>
    {E | internalEdgeCount E A = 0}
  calc
    (randomEdgeMeasure N p).real (badIndependentEventAtSize N u) ≤
        ∑ A ∈ vertexSetsOfCard N u,
          (randomEdgeMeasure N p).real (event A) := by
      exact measureReal_exists_mem_finset_le _ _ _
    _ = ∑ _A ∈ vertexSetsOfCard N u,
        (1 - (p : ℝ)) ^ (u.choose 2) := by
      apply Finset.sum_congr rfl
      intro A hA
      have hcard : #A = u := mem_vertexSetsOfCard.mp hA
      simpa only [event, hcard, Set.mem_setOf_eq] using
        (measureReal_internalEdgeCount_eq_zero N p A)
    _ = (N.choose u : ℝ) * (1 - (p : ℝ)) ^ (u.choose 2) := by
      rw [Finset.sum_const, nsmul_eq_mul, card_vertexSetsOfCard]

theorem badIndependentEvent_eq_iUnion_size (N : ℕ) :
    badIndependentEvent N =
      {E | ∃ u ∈ largeVertexSizes N, E ∈ badIndependentEventAtSize N u} := by
  ext E
  constructor
  · rintro ⟨A, hlarge, hzero⟩
    have hcard : #A ≤ N := by
      simpa using Finset.card_le_univ A
    refine ⟨#A, mem_largeVertexSizes.2 ⟨hcard, hlarge⟩, A, ?_, hzero⟩
    exact mem_vertexSetsOfCard.2 rfl
  · rintro ⟨u, hu, A, hA, hzero⟩
    have hcard : #A = u := mem_vertexSetsOfCard.mp hA
    refine ⟨A, ?_, hzero⟩
    simpa only [hcard] using (mem_largeVertexSizes.mp hu).2

/-- Cardinality-compressed independent-set union bound. -/
theorem measureReal_badIndependentEvent_le_size_sum
    (N : ℕ) (p : unitInterval) :
    (randomEdgeMeasure N p).real (badIndependentEvent N) ≤
      ∑ u ∈ largeVertexSizes N,
        (N.choose u : ℝ) * (1 - (p : ℝ)) ^ (u.choose 2) := by
  rw [badIndependentEvent_eq_iUnion_size]
  calc
    (randomEdgeMeasure N p).real
        {E | ∃ u ∈ largeVertexSizes N,
          E ∈ badIndependentEventAtSize N u} ≤
        ∑ u ∈ largeVertexSizes N,
          (randomEdgeMeasure N p).real (badIndependentEventAtSize N u) :=
      measureReal_exists_mem_finset_le _ _ _
    _ ≤ ∑ u ∈ largeVertexSizes N,
        (N.choose u : ℝ) * (1 - (p : ℝ)) ^ (u.choose 2) := by
      apply Finset.sum_le_sum
      intro u _
      exact measureReal_badIndependentEventAtSize_le N u p

/-- Elementary exponential envelope for the probability that `n` specified
coordinates are all absent. -/
theorem one_sub_unit_pow_le_exp_neg_mul (p : unitInterval) (n : ℕ) :
    (1 - (p : ℝ)) ^ n ≤ Real.exp (-(p : ℝ) * n) := by
  have hbase0 : (0 : ℝ) ≤ 1 - (p : ℝ) := sub_nonneg.mpr p.property.2
  have hbase : 1 - (p : ℝ) ≤ Real.exp (-(p : ℝ)) := by
    linarith [Real.add_one_le_exp (-(p : ℝ))]
  calc
    (1 - (p : ℝ)) ^ n ≤ Real.exp (-(p : ℝ)) ^ n :=
      pow_le_pow_left₀ hbase0 hbase n
    _ = Real.exp ((n : ℝ) * (-(p : ℝ))) :=
      (Real.exp_nat_mul (-(p : ℝ)) n).symm
    _ = Real.exp (-(p : ℝ) * n) := by
      congr 1
      ring

/-- Cardinality-compressed independent-set bound with the elementary
exponential envelope `(1-p)^r ≤ exp(-pr)`. -/
theorem measureReal_badIndependentEvent_le_exp_size_sum
    (N : ℕ) (p : unitInterval) :
    (randomEdgeMeasure N p).real (badIndependentEvent N) ≤
      ∑ u ∈ largeVertexSizes N,
        (N.choose u : ℝ) * Real.exp (-(p : ℝ) * (u.choose 2)) := by
  calc
    (randomEdgeMeasure N p).real (badIndependentEvent N) ≤
        ∑ u ∈ largeVertexSizes N,
          (N.choose u : ℝ) * (1 - (p : ℝ)) ^ (u.choose 2) :=
      measureReal_badIndependentEvent_le_size_sum N p
    _ ≤ ∑ u ∈ largeVertexSizes N,
        (N.choose u : ℝ) * Real.exp (-(p : ℝ) * (u.choose 2)) := by
      apply Finset.sum_le_sum
      intro u _
      exact mul_le_mul_of_nonneg_left
        (one_sub_unit_pow_le_exp_neg_mul p (u.choose 2))
        (Nat.cast_nonneg _)

theorem measureReal_badIndependentEvent_le_exp_sum
    (N : ℕ) (p : unitInterval) :
    (randomEdgeMeasure N p).real (badIndependentEvent N) ≤
      ∑ A ∈ largeVertexSets N,
        Real.exp (-(p : ℝ) * ((#A).choose 2)) := by
  calc
    (randomEdgeMeasure N p).real (badIndependentEvent N) ≤
        ∑ A ∈ largeVertexSets N,
          (1 - (p : ℝ)) ^ ((#A).choose 2) :=
      measureReal_badIndependentEvent_le_sum N p
    _ ≤ ∑ A ∈ largeVertexSets N,
        Real.exp (-(p : ℝ) * ((#A).choose 2)) := by
      apply Finset.sum_le_sum
      intro A _
      exact one_sub_unit_pow_le_exp_neg_mul p ((#A).choose 2)

/-- Union bound over all small vertex sets, followed by the fixed-coordinate
tail estimate at the first forbidden edge count `|U|+1`. -/
theorem measureReal_badLocalSparsityEvent_le_sum
    (N g : ℕ) (p : unitInterval) :
    (randomEdgeMeasure N p).real (badLocalSparsityEvent N g) ≤
      ∑ U ∈ smallVertexSets N g,
        ((((#U).choose 2).choose (#U + 1) : ℕ) : ℝ) *
          (p : ℝ) ^ (#U + 1) := by
  let event : Finset (Fin N) → Set (Set (RandomEdge N)) := fun U =>
    {E | #U + 1 ≤ internalEdgeCount E U}
  calc
    (randomEdgeMeasure N p).real (badLocalSparsityEvent N g) =
        (randomEdgeMeasure N p).real
          {E | ∃ U ∈ smallVertexSets N g, E ∈ event U} := by
      congr 1
      ext E
      simp [badLocalSparsityEvent, event]
    _ ≤ ∑ U ∈ smallVertexSets N g,
          (randomEdgeMeasure N p).real (event U) :=
      measureReal_exists_mem_finset_le _ _ _
    _ ≤ ∑ U ∈ smallVertexSets N g,
        ((((#U).choose 2).choose (#U + 1) : ℕ) : ℝ) *
          (p : ℝ) ^ (#U + 1) := by
      apply Finset.sum_le_sum
      intro U _
      exact measureReal_internalEdgeCount_ge_le N p U (#U + 1)

/-- Local-sparsity failure restricted to a fixed vertex-set cardinality. -/
def badLocalSparsityEventAtSize (N u : ℕ) :
    Set (Set (RandomEdge N)) :=
  {E | ∃ U ∈ vertexSetsOfCard N u,
    u + 1 ≤ internalEdgeCount E U}

theorem measureReal_badLocalSparsityEventAtSize_le
    (N u : ℕ) (p : unitInterval) :
    (randomEdgeMeasure N p).real (badLocalSparsityEventAtSize N u) ≤
      (N.choose u : ℝ) *
        ((((u.choose 2).choose (u + 1) : ℕ) : ℝ) *
          (p : ℝ) ^ (u + 1)) := by
  let event : Finset (Fin N) → Set (Set (RandomEdge N)) := fun U =>
    {E | u + 1 ≤ internalEdgeCount E U}
  calc
    (randomEdgeMeasure N p).real (badLocalSparsityEventAtSize N u) ≤
        ∑ U ∈ vertexSetsOfCard N u,
          (randomEdgeMeasure N p).real (event U) := by
      exact measureReal_exists_mem_finset_le _ _ _
    _ ≤ ∑ _U ∈ vertexSetsOfCard N u,
        ((((u.choose 2).choose (u + 1) : ℕ) : ℝ) *
          (p : ℝ) ^ (u + 1)) := by
      apply Finset.sum_le_sum
      intro U hU
      have hcard : #U = u := mem_vertexSetsOfCard.mp hU
      simpa only [event, hcard, Set.mem_setOf_eq] using
        (measureReal_internalEdgeCount_ge_le N p U (u + 1))
    _ = (N.choose u : ℝ) *
        ((((u.choose 2).choose (u + 1) : ℕ) : ℝ) *
          (p : ℝ) ^ (u + 1)) := by
      rw [Finset.sum_const, nsmul_eq_mul, card_vertexSetsOfCard]

theorem badLocalSparsityEvent_eq_iUnion_size (N g : ℕ) :
    badLocalSparsityEvent N g =
      {E | ∃ u ∈ Finset.range (2 * g + 1),
        E ∈ badLocalSparsityEventAtSize N u} := by
  ext E
  constructor
  · rintro ⟨U, hsmall, hmany⟩
    refine ⟨#U, by simpa using (Nat.lt_succ_iff.2 hsmall), U, ?_, ?_⟩
    · exact mem_vertexSetsOfCard.2 rfl
    · exact hmany
  · rintro ⟨u, hu, U, hU, hmany⟩
    have hcard : #U = u := mem_vertexSetsOfCard.mp hU
    refine ⟨U, ?_, ?_⟩
    · rw [hcard]
      exact Nat.le_of_lt_succ (by simpa using hu)
    · simpa only [hcard] using hmany

/-- Cardinality-compressed local-sparsity union bound. -/
theorem measureReal_badLocalSparsityEvent_le_size_sum
    (N g : ℕ) (p : unitInterval) :
    (randomEdgeMeasure N p).real (badLocalSparsityEvent N g) ≤
      ∑ u ∈ Finset.range (2 * g + 1),
        (N.choose u : ℝ) *
          ((((u.choose 2).choose (u + 1) : ℕ) : ℝ) *
            (p : ℝ) ^ (u + 1)) := by
  rw [badLocalSparsityEvent_eq_iUnion_size]
  calc
    (randomEdgeMeasure N p).real
        {E | ∃ u ∈ Finset.range (2 * g + 1),
          E ∈ badLocalSparsityEventAtSize N u} ≤
        ∑ u ∈ Finset.range (2 * g + 1),
          (randomEdgeMeasure N p).real
            (badLocalSparsityEventAtSize N u) :=
      measureReal_exists_mem_finset_le _ _ _
    _ ≤ ∑ u ∈ Finset.range (2 * g + 1),
        (N.choose u : ℝ) *
          ((((u.choose 2).choose (u + 1) : ℕ) : ℝ) *
            (p : ℝ) ^ (u + 1)) := by
      apply Finset.sum_le_sum
      intro u _
      exact measureReal_badLocalSparsityEventAtSize_le N u p

theorem isGoodSource_of_not_mem_badSourceEvent {N d g : ℕ}
    {E : Set (RandomEdge N)} (hE : E ∉ badSourceEvent N d g) :
    IsGoodSource E d g := by
  have hedge : E ∉ badEdgeEvent N d := by
    intro h
    exact hE (Or.inl (Or.inl (Or.inl h)))
  have hcut : E ∉ badCutEvent N d := by
    intro h
    exact hE (Or.inl (Or.inl (Or.inr h)))
  have hind : E ∉ badIndependentEvent N := by
    intro h
    exact hE (Or.inl (Or.inr h))
  have hlocal : E ∉ badLocalSparsityEvent N g := by
    intro h
    exact hE (Or.inr h)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Nat.le_of_not_gt (fun h => hedge h)
  · intro S
    exact Nat.le_of_not_gt (fun h => hcut ⟨S, h⟩)
  · intro A hA
    apply Nat.lt_of_not_ge
    intro hlarge
    apply hind
    exact ⟨A, hlarge, internalEdgeCount_eq_zero_of_isIndepSet E A hA⟩
  · intro U hU
    apply Nat.le_of_lt_succ
    apply Nat.lt_of_not_ge
    intro hsparse
    exact hlocal ⟨U, hU, hsparse⟩

theorem measureReal_badSourceEvent_le (N d g : ℕ) (p : unitInterval) :
    (randomEdgeMeasure N p).real (badSourceEvent N d g) ≤
      (randomEdgeMeasure N p).real (badEdgeEvent N d) +
      (randomEdgeMeasure N p).real (badCutEvent N d) +
      (randomEdgeMeasure N p).real (badIndependentEvent N) +
      (randomEdgeMeasure N p).real (badLocalSparsityEvent N g) := by
  rw [badSourceEvent]
  calc
    _ ≤ (randomEdgeMeasure N p).real
          (badEdgeEvent N d ∪ badCutEvent N d ∪ badIndependentEvent N) +
        (randomEdgeMeasure N p).real (badLocalSparsityEvent N g) :=
      measureReal_union_le _ _
    _ ≤ ((randomEdgeMeasure N p).real
          (badEdgeEvent N d ∪ badCutEvent N d) +
        (randomEdgeMeasure N p).real (badIndependentEvent N)) +
        (randomEdgeMeasure N p).real (badLocalSparsityEvent N g) := by
      gcongr
      exact measureReal_union_le _ _
    _ ≤ (((randomEdgeMeasure N p).real (badEdgeEvent N d) +
          (randomEdgeMeasure N p).real (badCutEvent N d)) +
        (randomEdgeMeasure N p).real (badIndependentEvent N)) +
        (randomEdgeMeasure N p).real (badLocalSparsityEvent N g) := by
      gcongr
      exact measureReal_union_le _ _
    _ = _ := by ring

theorem exists_isGoodSource_of_component_sum_lt_one
    {N d g : ℕ} {p : unitInterval}
    (hprob :
      (randomEdgeMeasure N p).real (badEdgeEvent N d) +
      (randomEdgeMeasure N p).real (badCutEvent N d) +
      (randomEdgeMeasure N p).real (badIndependentEvent N) +
      (randomEdgeMeasure N p).real (badLocalSparsityEvent N g) < 1) :
    ∃ E : Set (RandomEdge N), IsGoodSource E d g := by
  have hbad :
      (randomEdgeMeasure N p).real (badSourceEvent N d g) < 1 :=
    (measureReal_badSourceEvent_le N d g p).trans_lt hprob
  have hne : badSourceEvent N d g ≠ Set.univ := by
    intro h
    rw [h] at hbad
    simpa using hbad
  obtain ⟨E, hE⟩ := (Set.ne_univ_iff_exists_notMem (badSourceEvent N d g)).mp hne
  exact ⟨E, isGoodSource_of_not_mem_badSourceEvent hE⟩

/-- A completely explicit finite expression bounding the probability of any
source failure.  The two global count terms retain exact binomial tails;
the independent-set and local-sparsity terms are elementary powers. -/
def sourceFailureBound (N d g : ℕ) (p : unitInterval) : ℝ :=
  Bin(N.choose 2, p).real {k : ℕ | 5 * d * N < 4 * k} +
  (∑ S : Finset (Fin N),
    Bin(#S * (N - #S), p).real
      {k : ℕ | 5 * N * k < 8 * d * #S * (N - #S)}) +
  (∑ A ∈ largeVertexSets N,
    (1 - (p : ℝ)) ^ ((#A).choose 2)) +
  ∑ U ∈ smallVertexSets N g,
    ((((#U).choose 2).choose (#U + 1) : ℕ) : ℝ) *
      (p : ℝ) ^ (#U + 1)

theorem component_sum_le_sourceFailureBound
    (N d g : ℕ) (p : unitInterval) :
    (randomEdgeMeasure N p).real (badEdgeEvent N d) +
      (randomEdgeMeasure N p).real (badCutEvent N d) +
      (randomEdgeMeasure N p).real (badIndependentEvent N) +
      (randomEdgeMeasure N p).real (badLocalSparsityEvent N g) ≤
        sourceFailureBound N d g p := by
  unfold sourceFailureBound
  rw [measureReal_badEdgeEvent_eq_binomial]
  gcongr
  · exact measureReal_badCutEvent_le_binomial_sum N d p
  · exact measureReal_badIndependentEvent_le_sum N p
  · exact measureReal_badLocalSparsityEvent_le_sum N g p

/-- Finite probabilistic-method criterion: any parameters for which the
displayed finite bound is below one yield a deterministic source graph with
all four strengthened properties simultaneously. -/
theorem exists_isGoodSource_of_sourceFailureBound_lt_one
    {N d g : ℕ} {p : unitInterval}
    (h : sourceFailureBound N d g p < 1) :
    ∃ E : Set (RandomEdge N), IsGoodSource E d g := by
  apply exists_isGoodSource_of_component_sum_lt_one
  exact (component_sum_le_sourceFailureBound N d g p).trans_lt h

end RB

end

end LeanCo.HypercubeTuran
