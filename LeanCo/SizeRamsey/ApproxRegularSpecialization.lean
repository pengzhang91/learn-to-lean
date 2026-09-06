import LeanCo.SizeRamsey.ApproxRegularPeeling

/-!
# The `exp (-2)` specialization of degree-band peeling

This file specializes `ApproxRegularPeeling` to the geometric thresholds on
pages 10--11 of Beke--Li--Sahasrabudhe v1.  We keep the real scale

`D * exp (-2) ^ j`

separate from its natural-number ceiling.  This matters at the upper end of
a degree band: the elementary equivalence `d < ⌈x⌉₊ ↔ (d : ℝ) < x`
gives an exact strict real bound, whereas replacing the ceiling by an
unjustified equality would lose the endpoint information.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open Finset SimpleGraph

noncomputable section

universe u

variable {V : Type u}

/-! ## Geometric scale and its exact integer rounding -/

/-- The paper's constant `c₁ = exp (-2)`. -/
def approxRegularRatio : ℝ := Real.exp (-2)

/-- The unrounded degree scale at level `j`. -/
def approxRegularScale (D j : ℕ) : ℝ :=
  (D : ℝ) * approxRegularRatio ^ j

/-- The natural threshold actually used by the finite-graph peeling. -/
def approxRegularThreshold (D j : ℕ) : ℕ :=
  ⌈approxRegularScale D j⌉₊

theorem approxRegularRatio_pos : 0 < approxRegularRatio := by
  exact Real.exp_pos (-2)

theorem approxRegularRatio_lt_one : approxRegularRatio < 1 := by
  exact Real.exp_lt_one_iff.mpr (by norm_num)

theorem approxRegularRatio_nonneg : 0 ≤ approxRegularRatio :=
  approxRegularRatio_pos.le

theorem approxRegularRatio_le_one : approxRegularRatio ≤ 1 :=
  approxRegularRatio_lt_one.le

theorem approxRegularScale_pos (D j : ℕ) (hD : 0 < D) :
    0 < approxRegularScale D j := by
  exact mul_pos (by exact_mod_cast hD) (pow_pos approxRegularRatio_pos j)

theorem approxRegularScale_nonneg (D j : ℕ) :
    0 ≤ approxRegularScale D j := by
  exact mul_nonneg (Nat.cast_nonneg D) (pow_nonneg approxRegularRatio_nonneg j)

@[simp]
theorem approxRegularScale_zero (D : ℕ) :
    approxRegularScale D 0 = D := by
  simp [approxRegularScale]

theorem approxRegularScale_succ (D j : ℕ) :
    approxRegularScale D (j + 1) =
      approxRegularRatio * approxRegularScale D j := by
  simp only [approxRegularScale, pow_succ]
  ring

theorem approxRegularScale_antitone (D : ℕ) :
    Antitone (approxRegularScale D) := by
  intro i j hij
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one approxRegularRatio_nonneg
      approxRegularRatio_le_one hij)
    (Nat.cast_nonneg D)

theorem approxRegularThreshold_pos (D j : ℕ) (hD : 0 < D) :
    0 < approxRegularThreshold D j := by
  rw [approxRegularThreshold, Nat.ceil_pos]
  exact approxRegularScale_pos D j hD

theorem approxRegularScale_le_threshold_cast (D j : ℕ) :
    approxRegularScale D j ≤ (approxRegularThreshold D j : ℝ) := by
  exact Nat.le_ceil (approxRegularScale D j)

/-- The ceiling error is strictly less than one. -/
theorem approxRegularThreshold_cast_lt_scale_add_one (D j : ℕ) :
    (approxRegularThreshold D j : ℝ) < approxRegularScale D j + 1 := by
  exact Nat.ceil_lt_add_one (approxRegularScale_nonneg D j)

/-- For a natural degree, strict comparison with the rounded threshold is
exactly strict comparison with the real scale; there is no `+1` loss. -/
theorem nat_lt_approxRegularThreshold_iff (D j d : ℕ) :
    d < approxRegularThreshold D j ↔ (d : ℝ) < approxRegularScale D j := by
  exact Nat.lt_ceil

/-! ## The minimal stopping horizon -/

/-- Eventually the geometric scale is at most any positive natural target. -/
theorem exists_approxRegularScale_le (D r : ℕ) (hD : 0 < D)
    (hr : 0 < r) :
    ∃ T : ℕ, approxRegularScale D T ≤ (r : ℝ) := by
  have hDreal : 0 < (D : ℝ) := by exact_mod_cast hD
  have hrreal : 0 < (r : ℝ) := by exact_mod_cast hr
  obtain ⟨T, hT⟩ := exists_pow_lt_of_lt_one
    (div_pos hrreal hDreal) approxRegularRatio_lt_one
  refine ⟨T, ?_⟩
  have hmul :
      (D : ℝ) * approxRegularRatio ^ T <
        (D : ℝ) * ((r : ℝ) / (D : ℝ)) :=
    mul_lt_mul_of_pos_left hT hDreal
  have hcancel : (D : ℝ) * ((r : ℝ) / (D : ℝ)) = (r : ℝ) := by
    field_simp
  rw [approxRegularScale]
  exact hmul.le.trans_eq hcancel

/-- The least `T` with `D * c₁^T ≤ r`.  The conditional makes the
definition total; all mathematical interfaces below assume `D,r > 0`, when
the successful branch is forced. -/
noncomputable def approxRegularStop (D r : ℕ) : ℕ :=
  by
    classical
    exact if h : ∃ T : ℕ, approxRegularScale D T ≤ (r : ℝ) then
      Nat.find h
    else 0

theorem approxRegularStop_spec (D r : ℕ) (hD : 0 < D) (hr : 0 < r) :
    approxRegularScale D (approxRegularStop D r) ≤ (r : ℝ) := by
  let hExists := exists_approxRegularScale_le D r hD hr
  rw [approxRegularStop, dif_pos hExists]
  exact Nat.find_spec hExists

theorem approxRegularStop_minimal (D r j : ℕ) (hD : 0 < D)
    (hr : 0 < r) (hj : j < approxRegularStop D r) :
    (r : ℝ) < approxRegularScale D j := by
  let hExists := exists_approxRegularScale_le D r hD hr
  have hstop : approxRegularStop D r = Nat.find hExists := by
    rw [approxRegularStop, dif_pos hExists]
  have hnot : ¬ approxRegularScale D j ≤ (r : ℝ) := by
    apply Nat.find_min hExists
    simpa only [hstop] using hj
  exact lt_of_not_ge hnot

theorem approxRegularStop_le_of_scale_le (D r j : ℕ)
    (hD : 0 < D) (hr : 0 < r)
    (hj : approxRegularScale D j ≤ (r : ℝ)) :
    approxRegularStop D r ≤ j := by
  let hExists := exists_approxRegularScale_le D r hD hr
  have hstop : approxRegularStop D r = Nat.find hExists := by
    rw [approxRegularStop, dif_pos hExists]
  rw [hstop]
  exact Nat.find_min' hExists hj

/-- Every actual layer at or before the stopping horizon retains the useful
lower scale `c₁ r`.  This is the correct endpoint statement: at `j = T` one
only knows `scale T ≤ r`, not `r < scale T`. -/
theorem approxRegularRatio_mul_lt_scale_of_layer_index (D r j : ℕ)
    (hD : 0 < D) (hr : 0 < r)
    (hjOne : 1 ≤ j) (hjStop : j ≤ approxRegularStop D r) :
    approxRegularRatio * (r : ℝ) < approxRegularScale D j := by
  have hjpred : j - 1 < approxRegularStop D r := by omega
  have hpred := approxRegularStop_minimal D r (j - 1) hD hr hjpred
  have hmul := mul_lt_mul_of_pos_left hpred approxRegularRatio_pos
  have hj : j - 1 + 1 = j := Nat.sub_add_cancel hjOne
  rw [← approxRegularScale_succ D (j - 1), hj] at hmul
  exact hmul

/-! ## Exact degree bounds for the specialized peeling -/

/-- A band vertex in the `(j+1)`-st layer has real degree at least the
unrounded scale at that same index. -/
theorem approxRegularPeeling_band_degree_lower_real [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) (D j : ℕ) {v : V}
    (hv : v ∈ peelingBand G (approxRegularThreshold D) (j + 1)) :
    approxRegularScale D (j + 1) ≤
      ((peelingLayer G (approxRegularThreshold D) (j + 1)).degree v : ℝ) := by
  have hthreshold := peelingThreshold_le_layer_degree
    G (approxRegularThreshold D) j hv
  exact (approxRegularScale_le_threshold_cast D (j + 1)).trans
    (by exact_mod_cast hthreshold)

/-- After the `(j+1)`-st peel, every residual degree is strictly below the
*unrounded* `(j+1)`-st scale.  This is where `Nat.lt_ceil` removes the
rounding error exactly. -/
theorem approxRegularPeeling_residual_degree_lt_scale [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) (D j : ℕ) (hD : 0 < D)
    (v : V) :
    ((peelingResidual G (approxRegularThreshold D) (j + 1)).degree v : ℝ) <
      approxRegularScale D (j + 1) := by
  rw [← nat_lt_approxRegularThreshold_iff]
  exact peelingResidual_succ_degree_lt G (approxRegularThreshold D) j
    (approxRegularThreshold_pos D (j + 1) hD) v

/-- From the second layer onward, every vertex of the layer has real degree
strictly below the preceding unrounded scale. -/
theorem approxRegularPeeling_layer_degree_lt_previous_scale [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) (D j : ℕ) (hD : 0 < D)
    (v : V) :
    ((peelingLayer G (approxRegularThreshold D) (j + 2)).degree v : ℝ) <
      approxRegularScale D (j + 1) := by
  rw [← nat_lt_approxRegularThreshold_iff]
  exact peelingLayer_succ_degree_lt_previousThreshold
    G (approxRegularThreshold D) j
      (approxRegularThreshold_pos D (j + 1) hD) v

/-- If `D` bounds the initial graph globally, it bounds every peeled layer.
This is the global (not merely band-side) hypothesis required by the repaired
subgraph-finding lemma. -/
theorem approxRegularPeeling_layer_degree_le_initial_bound [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D j : ℕ)
    (hdegree : ∀ v, G.degree v ≤ D) (v : V) :
    (peelingLayer G (approxRegularThreshold D) (j + 1)).degree v ≤ D := by
  exact ((peelingLayer G (approxRegularThreshold D) (j + 1)).degree_le_of_le
    (peelingLayer_succ_le_initial G (approxRegularThreshold D) j)).trans
      (hdegree v)

/-- The first layer has upper degree at most `D = scale D 0`. -/
theorem approxRegularPeeling_first_layer_degree_upper_real [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : ℕ) (hdegree : ∀ v, G.degree v ≤ D)
    (v : V) :
    ((peelingLayer G (approxRegularThreshold D) 1).degree v : ℝ) ≤
      approxRegularScale D 0 := by
  rw [approxRegularScale_zero]
  exact_mod_cast
    approxRegularPeeling_layer_degree_le_initial_bound G D 0 hdegree v

/-- Uniform paper indexing: layer `j ≥ 1` has real degree at most the
preceding scale.  The bound is non-strict only for the first layer; for all
later layers `approxRegularPeeling_layer_degree_lt_previous_scale` is the
sharper statement. -/
theorem approxRegularPeeling_layer_degree_upper_previous_scale [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (D j : ℕ) (hD : 0 < D)
    (hdegree : ∀ v, G.degree v ≤ D) (hj : 1 ≤ j) (v : V) :
    ((peelingLayer G (approxRegularThreshold D) j).degree v : ℝ) ≤
      approxRegularScale D (j - 1) := by
  cases j with
  | zero => omega
  | succ i =>
      cases i with
      | zero =>
          simpa only [Nat.zero_add, Nat.add_zero, Nat.succ_eq_add_one,
            Nat.add_sub_cancel] using
            approxRegularPeeling_first_layer_degree_upper_real G D hdegree v
      | succ i =>
          have hlt :=
            approxRegularPeeling_layer_degree_lt_previous_scale G D i hD v
          have hindex : i + 2 - 1 = i + 1 := by omega
          simpa only [Nat.succ_eq_add_one, hindex] using hlt.le

/-- The repaired SubgraphFinding input for every layer, using the global
initial maximum-degree bound `D`. -/
theorem approxRegularPeeling_subgraphFindingInput [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (D j : ℕ)
    (hdegree : ∀ v, G.degree v ≤ D) :
    PeelingSubgraphFindingInput G (approxRegularThreshold D) j D := by
  apply peelingSubgraphFindingInput
  intro v
  exact ((peelingResidual G (approxRegularThreshold D) j).degree_le_of_le
    (peelingResidual_le_initial G (approxRegularThreshold D) j)).trans
      (hdegree v)

/-- From the second layer onward one can instead feed the repaired interface
the sharper natural upper bound `⌈scale(j+1)⌉₊ - 1`. -/
theorem approxRegularPeeling_subgraphFindingInput_sharp [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) (D j : ℕ) (hD : 0 < D) :
    PeelingSubgraphFindingInput G (approxRegularThreshold D) (j + 1)
      (approxRegularThreshold D (j + 1) - 1) := by
  apply peelingSubgraphFindingInput
  intro v
  exact Nat.le_sub_one_of_lt
    (peelingResidual_succ_degree_lt G (approxRegularThreshold D) j
      (approxRegularThreshold_pos D (j + 1) hD) v)

/-- The sharp natural upper parameter itself lies strictly below the
corresponding real scale. -/
theorem approxRegularThreshold_sub_one_cast_lt_scale (D j : ℕ)
    (hD : 0 < D) :
    ((approxRegularThreshold D j - 1 : ℕ) : ℝ) <
      approxRegularScale D j := by
  rw [← nat_lt_approxRegularThreshold_iff]
  exact Nat.sub_one_lt (Nat.ne_of_gt (approxRegularThreshold_pos D j hD))

/-! ## Stopping-horizon and paper-facing packages -/

/-- At the minimal stopping horizon, the remaining graph has global natural
degree at most `r`.  If the horizon is zero this follows from the initial
bound and `D ≤ r`; otherwise it follows from the exact strict real residual
bound. -/
theorem approxRegularPeeling_final_residual_degree_le_target [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (D r : ℕ) (hD : 0 < D) (hr : 0 < r)
    (hdegree : ∀ v, G.degree v ≤ D) (v : V) :
    (peelingResidual G (approxRegularThreshold D)
      (approxRegularStop D r)).degree v ≤ r := by
  have hstop := approxRegularStop_spec D r hD hr
  cases hT : approxRegularStop D r with
  | zero =>
      have hDr : D ≤ r := by
        rw [hT, approxRegularScale_zero] at hstop
        exact_mod_cast hstop
      exact (((peelingResidual G (approxRegularThreshold D) 0).degree_le_of_le
        (peelingResidual_le_initial G (approxRegularThreshold D) 0)).trans
          (hdegree v)).trans hDr
  | succ j =>
      have hreal :=
        approxRegularPeeling_residual_degree_lt_scale G D j hD v
      have hle :
          ((peelingResidual G (approxRegularThreshold D) (j + 1)).degree v : ℝ) ≤
            (r : ℝ) := hreal.le.trans (by simpa only [hT] using hstop)
      have hnat :
          (peelingResidual G (approxRegularThreshold D) (j + 1)).degree v ≤ r := by
        exact_mod_cast hle
      simpa only [hT, Nat.succ_eq_add_one] using hnat

/-- When at least one peel occurs, the final residual has the sharper strict
natural degree bound `< r`. -/
theorem approxRegularPeeling_final_residual_degree_lt_target_of_pos [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) (D r : ℕ)
    (hD : 0 < D) (hr : 0 < r) (hT : 0 < approxRegularStop D r)
    (v : V) :
    (peelingResidual G (approxRegularThreshold D)
      (approxRegularStop D r)).degree v < r := by
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hT)
  have hreal := approxRegularPeeling_residual_degree_lt_scale G D j hD v
  have hstop := approxRegularStop_spec D r hD hr
  have hlt :
      ((peelingResidual G (approxRegularThreshold D) (j + 1)).degree v : ℝ) <
        (r : ℝ) := hreal.trans_le (by simpa only [hj] using hstop)
  have hnat :
      (peelingResidual G (approxRegularThreshold D) (j + 1)).degree v < r := by
    exact_mod_cast hlt
  rw [hj]
  simpa only [Nat.succ_eq_add_one] using hnat

/-- The complete certificate attached to the zero-based layer `i`, i.e. to
the paper's one-based layer `E_(i+1)`.  It includes both the peeling step and
the repaired global-degree SubgraphFinding input. -/
structure ApproxRegularPaperLayer [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (D r i : ℕ) : Prop where
  before_stop : i < approxRegularStop D r
  step : DegreeBandPeelingStep G (approxRegularThreshold D) i
  repaired_input :
    PeelingSubgraphFindingInput G (approxRegularThreshold D) i D
  scale_above_target :
    approxRegularRatio * (r : ℝ) < approxRegularScale D (i + 1)
  band_degree_lower_real : ∀ {v},
    v ∈ peelingBand G (approxRegularThreshold D) (i + 1) →
      approxRegularScale D (i + 1) ≤
        ((peelingLayer G (approxRegularThreshold D) (i + 1)).degree v : ℝ)
  degree_upper_previous_scale : ∀ v,
    ((peelingLayer G (approxRegularThreshold D) (i + 1)).degree v : ℝ) ≤
      approxRegularScale D i
  later_strict_upper : i = 0 ∨ ∀ v,
    ((peelingLayer G (approxRegularThreshold D) (i + 1)).degree v : ℝ) <
      approxRegularScale D i
  later_sharp_repaired_input : i = 0 ∨
    PeelingSubgraphFindingInput G (approxRegularThreshold D) i
      (approxRegularThreshold D i - 1)

/-- Construct the paper-facing certificate for any layer before the stopping
horizon. -/
theorem approxRegularPaperLayer [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D r i : ℕ) (hD : 0 < D) (hr : 0 < r)
    (hdegree : ∀ v, G.degree v ≤ D)
    (hi : i < approxRegularStop D r) :
    ApproxRegularPaperLayer G D r i where
  before_stop := hi
  step := degreeBandPeelingStep G (approxRegularThreshold D) i
  repaired_input := approxRegularPeeling_subgraphFindingInput G D i hdegree
  scale_above_target :=
    approxRegularRatio_mul_lt_scale_of_layer_index D r (i + 1) hD hr
      (by omega) (by omega)
  band_degree_lower_real := by
    intro v hv
    exact approxRegularPeeling_band_degree_lower_real G D i hv
  degree_upper_previous_scale := by
    intro v
    have h := approxRegularPeeling_layer_degree_upper_previous_scale
      G D (i + 1) hD hdegree (by omega) v
    simpa only [Nat.add_sub_cancel] using h
  later_strict_upper := by
    cases i with
    | zero => exact Or.inl rfl
    | succ i =>
        right
        intro v
        simpa only [Nat.succ_eq_add_one] using
          approxRegularPeeling_layer_degree_lt_previous_scale G D i hD v
  later_sharp_repaired_input := by
    cases i with
    | zero => exact Or.inl rfl
    | succ i =>
        right
        simpa only [Nat.succ_eq_add_one] using
          approxRegularPeeling_subgraphFindingInput_sharp G D i hD

/-- Horizon-wide specialization: the exact mass identity, minimal stopping
facts, final residual degree bound, and a reusable certificate for every
candidate layer. -/
structure ApproxRegularSpecializationPackage [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (D r : ℕ) : Prop where
  threshold_positive : ∀ j, 0 < approxRegularThreshold D j
  stop_scale_upper :
    approxRegularScale D (approxRegularStop D r) ≤ (r : ℝ)
  before_stop_scale_lower : ∀ j, j < approxRegularStop D r →
    (r : ℝ) < approxRegularScale D j
  peeling : ApproxRegularPeelingPackage G (approxRegularThreshold D)
    (approxRegularStop D r)
  final_residual_degree : ∀ v,
    (peelingResidual G (approxRegularThreshold D)
      (approxRegularStop D r)).degree v ≤ r
  layer : ∀ i, i < approxRegularStop D r →
    ApproxRegularPaperLayer G D r i

/-- Construct the complete specialized package. -/
theorem approxRegularSpecializationPackage [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D r : ℕ) (hD : 0 < D) (hr : 0 < r)
    (hdegree : ∀ v, G.degree v ≤ D) :
    ApproxRegularSpecializationPackage G D r where
  threshold_positive := fun j ↦ approxRegularThreshold_pos D j hD
  stop_scale_upper := approxRegularStop_spec D r hD hr
  before_stop_scale_lower := fun j hj ↦
    approxRegularStop_minimal D r j hD hr hj
  peeling := approxRegularPeelingPackage G (approxRegularThreshold D)
    (approxRegularStop D r)
  final_residual_degree :=
    approxRegularPeeling_final_residual_degree_le_target G D r hD hr hdegree
  layer := fun i hi ↦ approxRegularPaperLayer G D r i hD hr hdegree hi

/-- Direct mass-dichotomy interface.  In the residual branch the remaining
graph has global degree at most `r`; in the layer branch the mass witness is
paired with all deterministic and repaired-SubgraphFinding certificates. -/
theorem approxRegularSpecialized_layer_or_residual [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (D r : ℕ) (hD : 0 < D) (hr : 0 < r)
    (hdegree : ∀ v, G.degree v ≤ D) :
    ((edgeCount G : ℝ) / 3 ≤
          (edgeCount (peelingResidual G (approxRegularThreshold D)
            (approxRegularStop D r)) : ℝ) ∧
        ∀ v, (peelingResidual G (approxRegularThreshold D)
          (approxRegularStop D r)).degree v ≤ r) ∨
      ∃ i : ℕ, i < approxRegularStop D r ∧
        Real.exp (-1) ^ (i + 1) * (edgeCount G : ℝ) ≤
          (edgeCount (peelingLayer G (approxRegularThreshold D) (i + 1)) : ℝ) ∧
        ApproxRegularPaperLayer G D r i := by
  rcases approxRegularPeeling_layer_or_residual G (approxRegularThreshold D)
    (approxRegularStop D r) with hresidual | ⟨i, hi, hmass, _hstep⟩
  · left
    exact ⟨hresidual,
      approxRegularPeeling_final_residual_degree_le_target
        G D r hD hr hdegree⟩
  · right
    exact ⟨i, hi, hmass, approxRegularPaperLayer G D r i hD hr hdegree hi⟩

end

end LeanCo.SizeRamsey
