import LeanCo.SizeRamsey.ApproxRegularMass

/-!
# Degree-band peeling for the path size--Ramsey lower bound

This file implements the edge decomposition used on pages 10--11 of
Beke--Li--Sahasrabudhe v1.  At step `j + 1`, all edges of the current
residual incident to a vertex of residual degree at least `τ (j + 1)` are
placed in a layer, and the next residual is their graph difference.

The indexing is the paper's one-based indexing for bands and layers:
`peelingResidual G τ 0 = G`, while `peelingBand G τ (j + 1)` and
`peelingLayer G τ (j + 1)` are formed from `peelingResidual G τ j`.
The zero-th band and layer are harmless empty values.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open Finset SimpleGraph

noncomputable section

universe u

variable {V : Type u}

/-! ## One peeling step -/

/-- Vertices whose degree in `R` is at least `t`. -/
def degreeBand [Fintype V] (R : SimpleGraph V) (t : ℕ) : Finset V :=
  Finset.univ.filter fun v ↦ t ≤ Nat.card (R.neighborSet v)

@[simp]
theorem mem_degreeBand [Fintype V] (R : SimpleGraph V)
    [DecidableRel R.Adj] (t : ℕ) (v : V) :
    v ∈ degreeBand R t ↔ t ≤ R.degree v := by
  rw [degreeBand, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  rw [Nat.card_eq_fintype_card, R.card_neighborSet_eq_degree]

/-- The subgraph of `R` consisting of all edges incident to `S`. -/
def degreeBandIncidentSubgraph (R : SimpleGraph V) (S : Finset V) :
    SimpleGraph V where
  Adj x y := R.Adj x y ∧ (x ∈ S ∨ y ∈ S)
  symm.symm x y hxy := ⟨hxy.1.symm, hxy.2.elim Or.inr Or.inl⟩

@[simp]
theorem degreeBandIncidentSubgraph_adj (R : SimpleGraph V) (S : Finset V)
    {x y : V} :
    (degreeBandIncidentSubgraph R S).Adj x y ↔
      R.Adj x y ∧ (x ∈ S ∨ y ∈ S) :=
  Iff.rfl

instance [DecidableEq V] {R : SimpleGraph V} [DecidableRel R.Adj]
    (S : Finset V) : DecidableRel (degreeBandIncidentSubgraph R S).Adj :=
  inferInstanceAs (DecidableRel fun x y ↦ R.Adj x y ∧ (x ∈ S ∨ y ∈ S))

/-- An incident-edge layer is a subgraph of its residual. -/
theorem degreeBandIncidentSubgraph_le (R : SimpleGraph V) (S : Finset V) :
    degreeBandIncidentSubgraph R S ≤ R :=
  fun _ _ hxy ↦ hxy.1

/-- The complement of the incident band is independent in the layer. -/
theorem degreeBandIncidentSubgraph_compl_independent [Fintype V]
    [DecidableEq V] (R : SimpleGraph V) (S : Finset V) :
    ∀ ⦃x⦄, x ∈ Finset.univ \ S →
      ∀ ⦃y⦄, y ∈ Finset.univ \ S →
        ¬(degreeBandIncidentSubgraph R S).Adj x y := by
  intro x hx y hy hxy
  have hxS : x ∉ S := (Finset.mem_sdiff.mp hx).2
  have hyS : y ∉ S := (Finset.mem_sdiff.mp hy).2
  exact hxy.2.elim hxS hyS

/-- At a vertex in the band, passing to the incident-edge layer preserves
the whole residual degree. -/
theorem degree_degreeBandIncidentSubgraph_eq [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (S : Finset V) {v : V} (hv : v ∈ S) :
    (degreeBandIncidentSubgraph R S).degree v = R.degree v := by
  have hneighbors :
      (degreeBandIncidentSubgraph R S).neighborFinset v =
        R.neighborFinset v := by
    ext w
    simp [hv]
  exact congrArg Finset.card hneighbors

/-- Removing the incident layer leaves degree below `t` at every vertex,
provided `t` is positive.  Positivity is logically necessary for a strict
natural-number bound: for `t = 0`, even the empty residual has degree `0`. -/
theorem degree_sdiff_degreeBandIncidentSubgraph_lt [Fintype V]
    [DecidableEq V] (R : SimpleGraph V) [DecidableRel R.Adj]
    (t : ℕ) (ht : 0 < t) (v : V) :
    (R \ degreeBandIncidentSubgraph R (degreeBand R t)).degree v < t := by
  classical
  by_cases hv : v ∈ degreeBand R t
  · have hisolated :
        (R \ degreeBandIncidentSubgraph R (degreeBand R t)).degree v = 0 := by
      rw [degree_eq_zero_iff_notMem_support]
      intro hvSupport
      rw [mem_support] at hvSupport
      obtain ⟨w, hvw⟩ := hvSupport
      have hvw' := (sdiff_adj R
        (degreeBandIncidentSubgraph R (degreeBand R t)) v w).mp hvw
      exact hvw'.2 ⟨hvw'.1, Or.inl hv⟩
    simpa only [hisolated] using ht
  · have hvlt : R.degree v < t := by
      simpa only [mem_degreeBand, not_le] using hv
    exact ((R \ degreeBandIncidentSubgraph R (degreeBand R t)).degree_le_of_le
      sdiff_le).trans_lt hvlt

/-! ## The recursive decomposition -/

/-- Residual graphs of the degree-band peeling process. -/
def peelingResidual [Fintype V] (G : SimpleGraph V) (τ : ℕ → ℕ) :
    ℕ → SimpleGraph V
  | 0 => G
  | j + 1 =>
      let R := peelingResidual G τ j
      R \ degreeBandIncidentSubgraph R (degreeBand R (τ (j + 1)))

/-- The paper's one-based band `V_j`; the zero-th band is empty. -/
def peelingBand [Fintype V] (G : SimpleGraph V) (τ : ℕ → ℕ) :
    ℕ → Finset V
  | 0 => ∅
  | j + 1 => degreeBand (peelingResidual G τ j) (τ (j + 1))

/-- The paper's one-based edge layer `E_j`; the zero-th layer is empty. -/
def peelingLayer [Fintype V] (G : SimpleGraph V) (τ : ℕ → ℕ) :
    ℕ → SimpleGraph V
  | 0 => ⊥
  | j + 1 => degreeBandIncidentSubgraph
      (peelingResidual G τ j) (peelingBand G τ (j + 1))

@[simp]
theorem peelingResidual_zero [Fintype V] (G : SimpleGraph V) (τ : ℕ → ℕ) :
    peelingResidual G τ 0 = G :=
  rfl

@[simp]
theorem peelingBand_zero [Fintype V] (G : SimpleGraph V) (τ : ℕ → ℕ) :
    peelingBand G τ 0 = ∅ :=
  rfl

@[simp]
theorem peelingBand_succ [Fintype V] (G : SimpleGraph V) (τ : ℕ → ℕ)
    (j : ℕ) :
    peelingBand G τ (j + 1) =
      degreeBand (peelingResidual G τ j) (τ (j + 1)) :=
  rfl

@[simp]
theorem peelingLayer_zero [Fintype V] (G : SimpleGraph V) (τ : ℕ → ℕ) :
    peelingLayer G τ 0 = ⊥ :=
  rfl

@[simp]
theorem peelingLayer_succ [Fintype V] (G : SimpleGraph V) (τ : ℕ → ℕ)
    (j : ℕ) :
    peelingLayer G τ (j + 1) = degreeBandIncidentSubgraph
      (peelingResidual G τ j) (peelingBand G τ (j + 1)) :=
  rfl

@[simp]
theorem peelingResidual_succ [Fintype V] (G : SimpleGraph V)
    (τ : ℕ → ℕ) (j : ℕ) :
    peelingResidual G τ (j + 1) =
      peelingResidual G τ j \ peelingLayer G τ (j + 1) :=
  rfl

noncomputable instance instDecidableRelPeelingResidual [Fintype V]
    (G : SimpleGraph V) (τ : ℕ → ℕ) (j : ℕ) :
    DecidableRel (peelingResidual G τ j).Adj :=
  Classical.decRel _

noncomputable instance instDecidableRelPeelingLayer [Fintype V]
    (G : SimpleGraph V) (τ : ℕ → ℕ) (j : ℕ) :
    DecidableRel (peelingLayer G τ j).Adj :=
  Classical.decRel _

/-- The vertices outside the one-based band `V_j`. -/
def peelingOutside [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (τ : ℕ → ℕ)
    (j : ℕ) : Finset V :=
  Finset.univ \ peelingBand G τ j

/-! ## Structural invariants -/

/-- Every layer lies in the residual from which it was removed. -/
theorem peelingLayer_succ_le_residual [Fintype V] (G : SimpleGraph V)
    (τ : ℕ → ℕ) (j : ℕ) :
    peelingLayer G τ (j + 1) ≤ peelingResidual G τ j := by
  rw [peelingLayer_succ]
  exact degreeBandIncidentSubgraph_le _ _

/-- Residuals decrease at every peeling step. -/
theorem peelingResidual_succ_le_residual [Fintype V] (G : SimpleGraph V)
    (τ : ℕ → ℕ) (j : ℕ) :
    peelingResidual G τ (j + 1) ≤ peelingResidual G τ j := by
  rw [peelingResidual_succ]
  exact sdiff_le

/-- Every residual remains a subgraph of the initial graph. -/
theorem peelingResidual_le_initial [Fintype V] (G : SimpleGraph V)
    (τ : ℕ → ℕ) (j : ℕ) :
    peelingResidual G τ j ≤ G := by
  induction j with
  | zero => exact le_rfl
  | succ j ih =>
      exact (peelingResidual_succ_le_residual G τ j).trans ih

/-- Every peeled layer is a subgraph of the initial graph. -/
theorem peelingLayer_succ_le_initial [Fintype V] (G : SimpleGraph V)
    (τ : ℕ → ℕ) (j : ℕ) :
    peelingLayer G τ (j + 1) ≤ G :=
  (peelingLayer_succ_le_residual G τ j).trans
    (peelingResidual_le_initial G τ j)

/-- A residual is exactly the disjoint union of the next layer and next
residual. -/
theorem peelingResidual_eq_layer_sup_succ [Fintype V] (G : SimpleGraph V)
    (τ : ℕ → ℕ) (j : ℕ) :
    peelingResidual G τ j =
      peelingLayer G τ (j + 1) ⊔ peelingResidual G τ (j + 1) := by
  rw [peelingResidual_succ]
  exact (sup_sdiff_cancel_right
    (peelingLayer_succ_le_residual G τ j)).symm

/-- The next layer and next residual have disjoint edge sets. -/
theorem peelingLayer_disjoint_residual_succ [Fintype V]
    (G : SimpleGraph V) (τ : ℕ → ℕ) (j : ℕ) :
    Disjoint (peelingLayer G τ (j + 1))
      (peelingResidual G τ (j + 1)) := by
  rw [peelingResidual_succ]
  exact disjoint_sdiff_self_right

/-- The band and its outside part are disjoint. -/
theorem peelingBand_disjoint_outside [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (τ : ℕ → ℕ) (j : ℕ) :
    Disjoint (peelingBand G τ j) (peelingOutside G τ j) := by
  exact Finset.disjoint_sdiff (s := peelingBand G τ j) (t := Finset.univ)

/-- The band and its outside part cover every vertex. -/
theorem peelingBand_union_outside [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (τ : ℕ → ℕ) (j : ℕ) :
    peelingBand G τ j ∪ peelingOutside G τ j = Finset.univ := by
  exact Finset.union_sdiff_of_subset
    (s := peelingBand G τ j) (t := Finset.univ) (Finset.subset_univ _)

/-- The outside part is independent in its peeled layer. -/
theorem peelingOutside_independent_in_layer_succ [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) (τ : ℕ → ℕ) (j : ℕ) :
    ∀ ⦃x⦄, x ∈ peelingOutside G τ (j + 1) →
      ∀ ⦃y⦄, y ∈ peelingOutside G τ (j + 1) →
        ¬(peelingLayer G τ (j + 1)).Adj x y := by
  rw [peelingLayer_succ]
  simpa only [peelingOutside] using
    (degreeBandIncidentSubgraph_compl_independent
      (peelingResidual G τ j) (peelingBand G τ (j + 1)))

/-- Band vertices retain their entire residual degree in the layer. -/
theorem peelingLayer_degree_eq_residual_of_mem_band [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) (τ : ℕ → ℕ) (j : ℕ)
    {v : V} (hv : v ∈ peelingBand G τ (j + 1)) :
    (peelingLayer G τ (j + 1)).degree v =
      (peelingResidual G τ j).degree v := by
  have hneighbors :
      (peelingLayer G τ (j + 1)).neighborSet v =
        (peelingResidual G τ j).neighborSet v := by
    ext w
    change
      (degreeBandIncidentSubgraph (peelingResidual G τ j)
          (peelingBand G τ (j + 1))).Adj v w ↔
        (peelingResidual G τ j).Adj v w
    rw [degreeBandIncidentSubgraph_adj]
    exact and_iff_left (Or.inl hv)
  have hcard := congrArg (fun s : Set V ↦ Nat.card s) hneighbors
  simpa only [Nat.card_eq_fintype_card,
    SimpleGraph.card_neighborSet_eq_degree] using hcard

/-- Consequently every band vertex has layer degree at least its threshold. -/
theorem peelingThreshold_le_layer_degree [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (τ : ℕ → ℕ) (j : ℕ)
    {v : V} (hv : v ∈ peelingBand G τ (j + 1)) :
    τ (j + 1) ≤ (peelingLayer G τ (j + 1)).degree v := by
  rw [peelingLayer_degree_eq_residual_of_mem_band G τ j hv]
  exact (mem_degreeBand (peelingResidual G τ j) (τ (j + 1)) v).mp
    (by simpa only [peelingBand_succ] using hv)

/-- At every vertex, layer degree is bounded by degree in the current
residual.  This is the global upper-degree input needed by the repaired
subgraph-finding interface. -/
theorem peelingLayer_degree_le_residual [Fintype V] (G : SimpleGraph V)
    (τ : ℕ → ℕ) (j : ℕ) (v : V) :
    (peelingLayer G τ (j + 1)).degree v ≤
      (peelingResidual G τ j).degree v :=
  (peelingLayer G τ (j + 1)).degree_le_of_le
    (peelingLayer_succ_le_residual G τ j)

/-- A global residual degree bound transfers directly to the next layer. -/
theorem peelingLayer_degree_le_of_residual_degree_le [Fintype V]
    (G : SimpleGraph V) (τ : ℕ → ℕ) (j Δ : ℕ)
    (hdegree : ∀ v, (peelingResidual G τ j).degree v ≤ Δ) :
    ∀ v, (peelingLayer G τ (j + 1)).degree v ≤ Δ := by
  intro v
  exact (peelingLayer_degree_le_residual G τ j v).trans (hdegree v)

/-- After removing a positive-threshold band, the next residual has global
degree strictly below that threshold. -/
theorem peelingResidual_succ_degree_lt [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (τ : ℕ → ℕ) (j : ℕ)
    (hτ : 0 < τ (j + 1)) (v : V) :
    (peelingResidual G τ (j + 1)).degree v < τ (j + 1) := by
  let R := peelingResidual G τ j
  let E := degreeBandIncidentSubgraph R (degreeBand R (τ (j + 1)))
  have hraw : (R \ E).degree v < τ (j + 1) :=
    degree_sdiff_degreeBandIncidentSubgraph_lt
    (peelingResidual G τ j) (τ (j + 1)) hτ v
  have hneighbors :
      (peelingResidual G τ (j + 1)).neighborSet v =
        (R \ E).neighborSet v := by
    ext w
    simp [R, E, peelingResidual_succ, peelingLayer_succ,
      peelingBand_succ]
  have hcard := congrArg (fun s : Set V ↦ Nat.card s) hneighbors
  have hdegree :
      (peelingResidual G τ (j + 1)).degree v = (R \ E).degree v := by
    simpa only [Nat.card_eq_fintype_card,
      SimpleGraph.card_neighborSet_eq_degree] using hcard
  exact hdegree.trans_lt hraw

/-- Exact treatment of the zero-threshold edge case. -/
theorem threshold_eq_zero_or_peelingResidual_succ_degree_lt [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) (τ : ℕ → ℕ) (j : ℕ) :
    τ (j + 1) = 0 ∨
      ∀ v, (peelingResidual G τ (j + 1)).degree v < τ (j + 1) := by
  rcases Nat.eq_zero_or_pos (τ (j + 1)) with hzero | hpos
  · exact Or.inl hzero
  · exact Or.inr (peelingResidual_succ_degree_lt G τ j hpos)

/-- From the second layer onward, the preceding positive threshold is a
global strict upper bound on the layer degree. -/
theorem peelingLayer_succ_degree_lt_previousThreshold [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) (τ : ℕ → ℕ) (j : ℕ)
    (hτ : 0 < τ (j + 1)) (v : V) :
    (peelingLayer G τ (j + 2)).degree v < τ (j + 1) :=
  (peelingLayer_degree_le_residual G τ (j + 1) v).trans_lt
    (peelingResidual_succ_degree_lt G τ j hτ v)

/-! ## Exact edge-mass identities -/

/-- A finite graph is the edge-disjoint union of a subgraph and its graph
difference, hence their edge counts add exactly. -/
theorem edgeCount_eq_add_edgeCount_sdiff [Fintype V] [DecidableEq V]
    (R E : SimpleGraph V) (hER : E ≤ R) :
    edgeCount R = edgeCount E + edgeCount (R \ E) := by
  simp only [edgeCount, Nat.card_coe_set_eq, SimpleGraph.edgeSet_sdiff]
  simpa only [add_comm] using
    (Set.ncard_sdiff_add_ncard_of_subset
      (SimpleGraph.edgeSet_mono hER)).symm

/-- One peeling step gives the exact natural-number edge-count recurrence. -/
theorem peelingResidual_edgeCount_succ [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (τ : ℕ → ℕ) (j : ℕ) :
    edgeCount (peelingResidual G τ j) =
      edgeCount (peelingLayer G τ (j + 1)) +
        edgeCount (peelingResidual G τ (j + 1)) := by
  rw [peelingResidual_succ]
  exact edgeCount_eq_add_edgeCount_sdiff
    (peelingResidual G τ j) (peelingLayer G τ (j + 1))
      (peelingLayer_succ_le_residual G τ j)

/-- After `T` steps, the initial edge mass is exactly the final residual
mass plus the masses of the one-based layers `E₁, …, E_T`. -/
theorem peeling_edgeCount_mass_identity [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (τ : ℕ → ℕ) (T : ℕ) :
    edgeCount G = edgeCount (peelingResidual G τ T) +
      ∑ j ∈ Finset.Icc 1 T, edgeCount (peelingLayer G τ j) := by
  induction T with
  | zero => simp
  | succ T ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hstep := peelingResidual_edgeCount_succ G τ T
      omega

/-- The exact peeling identity feeds the previously formalized
approximately-regular mass dichotomy without an additional hypothesis. -/
theorem approxRegularPeeling_mass_dichotomy [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (τ : ℕ → ℕ) (T : ℕ) :
    (edgeCount G : ℝ) / 3 ≤
        (edgeCount (peelingResidual G τ T) : ℝ) ∨
      ∃ j : ℕ, 1 ≤ j ∧ j ≤ T ∧
        Real.exp (-1) ^ j * (edgeCount G : ℝ) ≤
          (edgeCount (peelingLayer G τ j) : ℝ) := by
  exact approxRegularEdgeCount_mass_dichotomy G
    (peelingResidual G τ T) (peelingLayer G τ) T
      (peeling_edgeCount_mass_identity G τ T)

/-! ## Reusable packaged interfaces -/

/-- All deterministic facts produced by the `(j + 1)`-st peeling step. -/
structure DegreeBandPeelingStep [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (τ : ℕ → ℕ) (j : ℕ) : Prop where
  layer_le_residual :
    peelingLayer G τ (j + 1) ≤ peelingResidual G τ j
  residual_le_initial : peelingResidual G τ j ≤ G
  next_le_residual :
    peelingResidual G τ (j + 1) ≤ peelingResidual G τ j
  split : peelingResidual G τ j =
    peelingLayer G τ (j + 1) ⊔ peelingResidual G τ (j + 1)
  edge_disjoint : Disjoint (peelingLayer G τ (j + 1))
    (peelingResidual G τ (j + 1))
  edgeCount_split : edgeCount (peelingResidual G τ j) =
    edgeCount (peelingLayer G τ (j + 1)) +
      edgeCount (peelingResidual G τ (j + 1))
  vertex_disjoint : Disjoint (peelingBand G τ (j + 1))
    (peelingOutside G τ (j + 1))
  vertex_cover : peelingBand G τ (j + 1) ∪
    peelingOutside G τ (j + 1) = Finset.univ
  outside_independent :
    ∀ ⦃x⦄, x ∈ peelingOutside G τ (j + 1) →
      ∀ ⦃y⦄, y ∈ peelingOutside G τ (j + 1) →
        ¬(peelingLayer G τ (j + 1)).Adj x y
  band_degree_eq : ∀ ⦃v⦄, v ∈ peelingBand G τ (j + 1) →
    (peelingLayer G τ (j + 1)).degree v =
      (peelingResidual G τ j).degree v
  band_degree_lower : ∀ ⦃v⦄, v ∈ peelingBand G τ (j + 1) →
    τ (j + 1) ≤ (peelingLayer G τ (j + 1)).degree v
  layer_degree_upper : ∀ v,
    (peelingLayer G τ (j + 1)).degree v ≤
      (peelingResidual G τ j).degree v
  next_degree_lt : 0 < τ (j + 1) → ∀ v,
    (peelingResidual G τ (j + 1)).degree v < τ (j + 1)

/-- The canonical recursive process supplies a complete step package. -/
theorem degreeBandPeelingStep [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (τ : ℕ → ℕ) (j : ℕ) :
    DegreeBandPeelingStep G τ j where
  layer_le_residual := peelingLayer_succ_le_residual G τ j
  residual_le_initial := peelingResidual_le_initial G τ j
  next_le_residual := peelingResidual_succ_le_residual G τ j
  split := peelingResidual_eq_layer_sup_succ G τ j
  edge_disjoint := peelingLayer_disjoint_residual_succ G τ j
  edgeCount_split := peelingResidual_edgeCount_succ G τ j
  vertex_disjoint := peelingBand_disjoint_outside G τ (j + 1)
  vertex_cover := peelingBand_union_outside G τ (j + 1)
  outside_independent := peelingOutside_independent_in_layer_succ G τ j
  band_degree_eq := by
    intro v hv
    exact peelingLayer_degree_eq_residual_of_mem_band G τ j hv
  band_degree_lower := by
    intro v hv
    exact peelingThreshold_le_layer_degree G τ j hv
  layer_degree_upper := peelingLayer_degree_le_residual G τ j
  next_degree_lt := peelingResidual_succ_degree_lt G τ j

/-- The fields from a peeling layer that match the graph-theoretic inputs of
the repaired subgraph-finding lemma.  The caller supplies only a global
upper bound on the current residual; the peeling construction transfers it
to the layer. -/
structure PeelingSubgraphFindingInput [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (τ : ℕ → ℕ) (j Δ : ℕ) : Prop where
  layer_le_initial : peelingLayer G τ (j + 1) ≤ G
  partition_disjoint : Disjoint (peelingBand G τ (j + 1))
    (peelingOutside G τ (j + 1))
  partition_cover : peelingBand G τ (j + 1) ∪
    peelingOutside G τ (j + 1) = Finset.univ
  outside_independent :
    ∀ ⦃x⦄, x ∈ peelingOutside G τ (j + 1) →
      ∀ ⦃y⦄, y ∈ peelingOutside G τ (j + 1) →
        ¬(peelingLayer G τ (j + 1)).Adj x y
  global_degree_upper : ∀ v,
    (peelingLayer G τ (j + 1)).degree v ≤ Δ
  band_degree_lower : ∀ ⦃v⦄, v ∈ peelingBand G τ (j + 1) →
    τ (j + 1) ≤ (peelingLayer G τ (j + 1)).degree v

/-- Package a layer for the repaired subgraph-finding interface. -/
theorem peelingSubgraphFindingInput [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (τ : ℕ → ℕ) (j Δ : ℕ)
    (hdegree : ∀ v, (peelingResidual G τ j).degree v ≤ Δ) :
    PeelingSubgraphFindingInput G τ j Δ where
  layer_le_initial := peelingLayer_succ_le_initial G τ j
  partition_disjoint := peelingBand_disjoint_outside G τ (j + 1)
  partition_cover := peelingBand_union_outside G τ (j + 1)
  outside_independent := peelingOutside_independent_in_layer_succ G τ j
  global_degree_upper :=
    peelingLayer_degree_le_of_residual_degree_le G τ j Δ hdegree
  band_degree_lower := by
    intro v hv
    exact peelingThreshold_le_layer_degree G τ j hv

/-- Horizon-wide package: the exact mass identity used by
`ApproxRegularMass` together with the complete deterministic certificate at
every step before `T`. -/
structure ApproxRegularPeelingPackage [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (τ : ℕ → ℕ) (T : ℕ) : Prop where
  mass_identity : edgeCount G = edgeCount (peelingResidual G τ T) +
    ∑ j ∈ Finset.Icc 1 T, edgeCount (peelingLayer G τ j)
  step : ∀ j, j < T → DegreeBandPeelingStep G τ j

/-- Construct the horizon-wide peeling package. -/
theorem approxRegularPeelingPackage [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (τ : ℕ → ℕ) (T : ℕ) :
    ApproxRegularPeelingPackage G τ T where
  mass_identity := peeling_edgeCount_mass_identity G τ T
  step := fun j _ ↦ degreeBandPeelingStep G τ j

/-- Combined end product: either the final residual carries one third of
the initial mass, or an explicitly indexed layer carries the geometric mass
guarantee and comes with its full peeling-step certificate. -/
theorem approxRegularPeeling_layer_or_residual [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (τ : ℕ → ℕ) (T : ℕ) :
    (edgeCount G : ℝ) / 3 ≤
        (edgeCount (peelingResidual G τ T) : ℝ) ∨
      ∃ i : ℕ, i < T ∧
        Real.exp (-1) ^ (i + 1) * (edgeCount G : ℝ) ≤
          (edgeCount (peelingLayer G τ (i + 1)) : ℝ) ∧
        DegreeBandPeelingStep G τ i := by
  rcases approxRegularPeeling_mass_dichotomy G τ T with hresidual |
    ⟨j, hjOne, hjT, hjmass⟩
  · exact Or.inl hresidual
  · right
    cases j with
    | zero => omega
    | succ i =>
        exact ⟨i, by omega, by simpa only [Nat.succ_eq_add_one] using hjmass,
          degreeBandPeelingStep G τ i⟩

end

end LeanCo.SizeRamsey
