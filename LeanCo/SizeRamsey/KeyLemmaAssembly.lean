import LeanCo.SizeRamsey.ApproxRegularSpecialization
import LeanCo.SizeRamsey.PeelingDegreeCount
import LeanCo.SizeRamsey.PeelingSubgraphFinding
import LeanCo.SizeRamsey.KeyLemmaNumerics

/-!
# Generic assembly of the two Key-Lemma branches

This module joins the exact peeling mass dichotomy to the repaired
SubgraphFinding theorem.  The genuinely probabilistic/asymptotic lower
bounds for `ballsBinsWeight` are deliberately exposed as named hypotheses;
the theorem below does not pretend that those estimates have already been
proved.

For a zero-based layer index `i`, the layer is `E_(i+1)`.  Its natural global
degree cap is `D` for the first layer and `⌈D c₁^i⌉₊ - 1` thereafter.
This is the exact integer consequence of the strict residual bound and does
not discard the ceiling error.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open Finset SimpleGraph

noncomputable section

universe u

variable {V : Type u}

/-! ## Exact degree caps and paper-facing real factors -/

/-- Global natural degree cap used when applying SubgraphFinding to the
zero-based layer `i`. -/
def keyLemmaLayerDegreeCap (D i : ℕ) : ℕ :=
  if i = 0 then D else approxRegularThreshold D i - 1

@[simp]
theorem keyLemmaLayerDegreeCap_zero (D : ℕ) :
    keyLemmaLayerDegreeCap D 0 = D := by
  simp [keyLemmaLayerDegreeCap]

@[simp]
theorem keyLemmaLayerDegreeCap_succ (D i : ℕ) :
    keyLemmaLayerDegreeCap D (i + 1) =
      approxRegularThreshold D (i + 1) - 1 := by
  simp [keyLemmaLayerDegreeCap]

@[simp]
theorem approxRegularThreshold_zero_eq (D : ℕ) :
    approxRegularThreshold D 0 = D := by
  simp [approxRegularThreshold, approxRegularScale]

/-- The exact residual bound which feeds the repaired global-degree
SubgraphFinding interface for layer `i+1`. -/
theorem peelingResidual_degree_le_keyLemmaLayerDegreeCap [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (D i : ℕ) (hD : 0 < D) (hdegree : ∀ v, G.degree v ≤ D) :
    ∀ v, (peelingResidual G (approxRegularThreshold D) i).degree v ≤
      keyLemmaLayerDegreeCap D i := by
  cases i with
  | zero =>
      intro v
      rw [keyLemmaLayerDegreeCap_zero]
      exact ((peelingResidual G (approxRegularThreshold D) 0).degree_le_of_le
        (peelingResidual_le_initial G (approxRegularThreshold D) 0)).trans
          (hdegree v)
  | succ i =>
      intro v
      rw [keyLemmaLayerDegreeCap_succ]
      exact Nat.le_sub_one_of_lt
        (peelingResidual_succ_degree_lt G (approxRegularThreshold D) i
          (approxRegularThreshold_pos D (i + 1) hD) v)

/-- Every layer cap is no larger than the initial cap `D`. -/
theorem keyLemmaLayerDegreeCap_le (D i : ℕ) :
    keyLemmaLayerDegreeCap D i ≤ D := by
  cases i with
  | zero => simp
  | succ i =>
      rw [keyLemmaLayerDegreeCap_succ]
      have hscale : approxRegularScale D (i + 1) ≤
          approxRegularScale D 0 :=
        approxRegularScale_antitone D (Nat.zero_le (i + 1))
      have hthreshold : approxRegularThreshold D (i + 1) ≤
          approxRegularThreshold D 0 := by
        exact Nat.ceil_mono hscale
      rw [approxRegularThreshold_zero_eq] at hthreshold
      exact (Nat.sub_le _ _).trans hthreshold

/-- The target occurring in the literal BLS Key Lemma. -/
def keyLemmaAssemblyTarget (G : SimpleGraph V) (r : ℕ) (β : ℝ) : ℝ :=
  60 * (edgeCount G : ℝ) /
    (Real.rpow β (9 / 10 : ℝ) * r)

/-- Numerator of the final dense-layer gain factor. -/
def keyLemmaDenseNumerator (β : ℝ) (j : ℕ) : ℝ :=
  Real.exp (j : ℝ) * (1 / β) ^ (1 / 10 : ℝ)

/-- Denominator of the final dense-layer gain factor. -/
def keyLemmaDenseDenominator (β : ℝ) (j : ℕ) : ℝ :=
  keyLemmaDenseConstant *
    (4 * (j : ℝ) + Real.log (5 / β ^ 2))

theorem keyLemmaAssemblyTarget_nonneg (G : SimpleGraph V) (r : ℕ)
    {β : ℝ} (hβ : 0 < β) (hr : 0 < r) :
    0 ≤ keyLemmaAssemblyTarget G r β := by
  unfold keyLemmaAssemblyTarget
  have hpow : 0 < Real.rpow β (9 / 10 : ℝ) :=
    Real.rpow_pos_of_pos hβ _
  have hrReal : 0 < (r : ℝ) := by exact_mod_cast hr
  exact div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
    (mul_pos hpow hrReal).le

theorem keyLemmaDenseDenominator_pos {β : ℝ} (hβ : 0 < β)
    (hβOne : β ≤ 1) {j : ℕ} (hj : 1 ≤ j) :
    0 < keyLemmaDenseDenominator β j := by
  have hβSq : β ^ 2 ≤ 1 := by nlinarith [sq_nonneg β]
  have hβSqPos : 0 < β ^ 2 := pow_pos hβ _
  have hlog : 0 ≤ Real.log (5 / β ^ 2) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hβSqPos]
    nlinarith
  have hjReal : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hbracket : 0 < 4 * (j : ℝ) + Real.log (5 / β ^ 2) := by
    nlinarith
  unfold keyLemmaDenseDenominator keyLemmaDenseConstant
  exact mul_pos (by positivity) hbracket

/-! ## The two still-open weight interfaces -/

/-- Normalized weight lower bound needed for every dense layer.  This is
already in the exact form consumed by the mass comparison. -/
def KeyLemmaLayerWeightBound [Fintype V] (G : SimpleGraph V)
    (D r n : ℕ) (target : ℝ) : Prop :=
  ∀ i, i < approxRegularStop D r →
    Real.exp (-1) ^ (i + 1) * (edgeCount G : ℝ) ≤
        (edgeCount
          (peelingLayer G (approxRegularThreshold D) (i + 1)) : ℝ) →
    target ≤
      Real.exp (-1) ^ (i + 1) * (edgeCount G : ℝ) / 3 *
        ballsBinsWeight
          (subgraphFindingBinCount n
            (peelingBand G (approxRegularThreshold D) (i + 1)).card)
          (keyLemmaLayerDegreeCap D i)

/-- Raw dense-layer balls-and-bins estimate.  The two exact natural
degree-count inequalities are passed to the hypothesis rather than being
assumed: `KeyLemmaAssembly` supplies them from `PeelingDegreeCount`.

The remaining inequality is the precise unformalized analytic interface.
Together with `KeyLemmaNumerics`, it implies `KeyLemmaLayerWeightBound`. -/
def KeyLemmaDenseRawWeightBound [Fintype V] (G : SimpleGraph V)
    (D r n : ℕ) (β target : ℝ) : Prop :=
  ∀ i, i < approxRegularStop D r →
    Real.exp (-1) ^ (i + 1) * (edgeCount G : ℝ) ≤
        (edgeCount
          (peelingLayer G (approxRegularThreshold D) (i + 1)) : ℝ) →
    approxRegularThreshold D (i + 1) *
        (peelingBand G (approxRegularThreshold D) (i + 1)).card ≤
        2 * edgeCount
          (peelingLayer G (approxRegularThreshold D) (i + 1)) →
    edgeCount (peelingLayer G (approxRegularThreshold D) (i + 1)) ≤
        (peelingBand G (approxRegularThreshold D) (i + 1)).card *
          keyLemmaLayerDegreeCap D i →
    target * keyLemmaDenseNumerator β (i + 1) ≤
      (Real.exp (-1) ^ (i + 1) * (edgeCount G : ℝ) / 3 *
          ballsBinsWeight
            (subgraphFindingBinCount n
              (peelingBand G (approxRegularThreshold D) (i + 1)).card)
            (keyLemmaLayerDegreeCap D i)) *
        keyLemmaDenseDenominator β (i + 1)

/-- Normalized weight lower bound needed in the final-residual branch.
This is the second explicitly open balls-and-bins/asymptotic interface. -/
def KeyLemmaResidualWeightBound [Fintype V] (G : SimpleGraph V)
    (r n : ℕ) (target : ℝ) : Prop :=
  target ≤ (edgeCount G : ℝ) / 9 *
    ballsBinsWeight
      (subgraphFindingBinCount n (Fintype.card V)) r

/-! ## Closing the dense real arithmetic from `KeyLemmaNumerics` -/

/-- The raw dense weight estimate plus the numerical dominance proved in
`KeyLemmaNumerics` yields the normalized layer-weight interface.  The exact
degree-count premises of the raw estimate are discharged here. -/
theorem keyLemmaLayerWeightBound_of_denseRaw [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {D r n : ℕ} {β target : ℝ}
    (hD : 0 < D) (hdegree : ∀ v, G.degree v ≤ D)
    (hβ : 0 < β) (hβOne : β ≤ 1) (htarget : 0 ≤ target)
    (hnumeric : ∀ j : ℕ, 1 ≤ j →
      keyLemmaDenseDenominator β j ≤ keyLemmaDenseNumerator β j)
    (hraw : KeyLemmaDenseRawWeightBound G D r n β target) :
    KeyLemmaLayerWeightBound G D r n target := by
  intro i hi hlayerMass
  have hresidualDegree : ∀ v,
      (peelingResidual G (approxRegularThreshold D) i).degree v ≤
        keyLemmaLayerDegreeCap D i :=
    peelingResidual_degree_le_keyLemmaLayerDegreeCap G D i hD hdegree
  have hcountLower :=
    peelingThreshold_mul_bandCard_le_twice_layerEdgeCount
      G (approxRegularThreshold D) i
  have hcountUpper :=
    peelingLayerEdgeCount_le_bandCard_mul_of_residual_degree_upper
      G (approxRegularThreshold D) i (keyLemmaLayerDegreeCap D i)
        hresidualDegree
  have hrawi := hraw i hi hlayerMass hcountLower hcountUpper
  have hj : 1 ≤ i + 1 := by omega
  have hdenom : 0 < keyLemmaDenseDenominator β (i + 1) :=
    keyLemmaDenseDenominator_pos hβ hβOne hj
  have htargetNumerator :
      target * keyLemmaDenseDenominator β (i + 1) ≤
        target * keyLemmaDenseNumerator β (i + 1) :=
    mul_le_mul_of_nonneg_left (hnumeric (i + 1) hj) htarget
  have hmul :
      target * keyLemmaDenseDenominator β (i + 1) ≤
        (Real.exp (-1) ^ (i + 1) * (edgeCount G : ℝ) / 3 *
            ballsBinsWeight
              (subgraphFindingBinCount n
                (peelingBand G (approxRegularThreshold D) (i + 1)).card)
              (keyLemmaLayerDegreeCap D i)) *
          keyLemmaDenseDenominator β (i + 1) :=
    htargetNumerator.trans hrawi
  exact le_of_mul_le_mul_right hmul hdenom

/-! ## Numerical hypotheses shared by both extraction branches -/

/-- The paper's stronger quarter-size vertex hypothesis implies the looser
vertex-side hypothesis required by repaired SubgraphFinding. -/
theorem keyLemma_vertexCard_le_subgraphFinding_bound [Fintype V]
    {r n : ℕ} (hr : 21 ≤ r)
    (hcard : (Fintype.card V : ℝ) ≤
      ((r : ℝ) * Real.log (r : ℝ) * n) / 4) :
    (Fintype.card V : ℝ) ≤
      2 * ((r : ℝ) * Real.log (r : ℝ)) * n := by
  have hrOne : (1 : ℝ) ≤ r := by
    exact_mod_cast (show 1 ≤ r by omega)
  have hlog : 0 ≤ Real.log (r : ℝ) := Real.log_nonneg hrOne
  have hbase : 0 ≤ (r : ℝ) * Real.log (r : ℝ) * n := by positivity
  exact hcard.trans (by nlinarith)

/-- At `r ≥ 21`, the residual cap `r` lies below the natural floor of
`r log r`, as required by repaired SubgraphFinding. -/
theorem keyLemma_targetDegree_le_floor (r : ℕ) (hr : 21 ≤ r) :
    r ≤ ⌊(r : ℝ) * Real.log (r : ℝ)⌋₊ := by
  apply Nat.le_floor
  have hrReal : 0 < (r : ℝ) := by positivity
  have hlogOne : (1 : ℝ) < Real.log (r : ℝ) := by
    apply (Real.lt_log_iff_exp_lt hrReal).mpr
    exact Real.exp_one_lt_three.trans_le
      (by exact_mod_cast (show 3 ≤ r by omega))
  calc
    (r : ℝ) = (r : ℝ) * 1 := by ring
    _ ≤ (r : ℝ) * Real.log (r : ℝ) :=
      mul_le_mul_of_nonneg_left hlogOne.le hrReal.le

/-! ## Generic two-branch assembly -/

/-- Generic Key-Lemma assembly theorem.

The conclusion is fully proved from the two explicitly named weight
interfaces.  In the residual branch, the factor `1/9` is the product of the
peeling `1/3` mass guarantee and the SubgraphFinding `1/3` guarantee.  In a
layer branch, the geometric mass factor supplied by the peeling is combined
with the same SubgraphFinding guarantee. -/
theorem keyLemmaAssembly_of_weight_bounds [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {D r n : ℕ} {target : ℝ}
    (hr : 21 ≤ r)
    (hn : 100 * Real.log (r : ℝ) ≤ (n : ℝ))
    (hD : 0 < D) (hdegree : ∀ v, G.degree v ≤ D)
    (hcard : (Fintype.card V : ℝ) ≤
      ((r : ℝ) * Real.log (r : ℝ) * n) / 4)
    (hDfloor : D ≤ ⌊(r : ℝ) * Real.log (r : ℝ)⌋₊)
    (hLayerWeight : KeyLemmaLayerWeightBound G D r n target)
    (hResidualWeight : KeyLemmaResidualWeightBound G r n target) :
    ∃ H : SimpleGraph V,
      H ≤ G ∧ (pathGraph n).Free H ∧ target ≤ (edgeCount H : ℝ) := by
  have hrPos : 0 < r := by omega
  have hvertex :=
    keyLemma_vertexCard_le_subgraphFinding_bound (V := V) hr hcard
  have hrFloor := keyLemma_targetDegree_le_floor r hr
  rcases approxRegularSpecialized_layer_or_residual G D r hD hrPos hdegree with
    ⟨hresidualMass, hresidualDegree⟩ |
      ⟨i, hi, hlayerMass, _hlayerPackage⟩
  · obtain ⟨H, hHle, hHfree, hHweight⟩ :=
      exists_pathFree_subgraph_of_peelingResidual
        G (approxRegularThreshold D) (r := r) (n := n) (Δ := r)
          (T := approxRegularStop D r) hr hn hvertex hresidualDegree hrFloor
    let W : ℝ := ballsBinsWeight
      (subgraphFindingBinCount n (Fintype.card V)) r
    have hW : 0 ≤ W := ballsBinsWeight_nonneg _ _
    have hmassScaled :
        (edgeCount G : ℝ) / 9 * W ≤
          (edgeCount (peelingResidual G (approxRegularThreshold D)
            (approxRegularStop D r)) : ℝ) / 3 * W := by
      calc
        (edgeCount G : ℝ) / 9 * W =
            ((edgeCount G : ℝ) / 3) * (W / 3) := by ring
        _ ≤ (edgeCount (peelingResidual G (approxRegularThreshold D)
              (approxRegularStop D r)) : ℝ) * (W / 3) :=
          mul_le_mul_of_nonneg_right hresidualMass (div_nonneg hW (by norm_num))
        _ = (edgeCount (peelingResidual G (approxRegularThreshold D)
              (approxRegularStop D r)) : ℝ) / 3 * W := by ring
    refine ⟨H, hHle.trans (peelingResidual_le_initial
      G (approxRegularThreshold D) (approxRegularStop D r)), hHfree, ?_⟩
    exact hResidualWeight.trans (hmassScaled.trans (by simpa only [W] using hHweight))
  · have hcapDegree : ∀ v,
        (peelingResidual G (approxRegularThreshold D) i).degree v ≤
          keyLemmaLayerDegreeCap D i :=
      peelingResidual_degree_le_keyLemmaLayerDegreeCap G D i hD hdegree
    have hcapFloor : keyLemmaLayerDegreeCap D i ≤
        ⌊(r : ℝ) * Real.log (r : ℝ)⌋₊ :=
      (keyLemmaLayerDegreeCap_le D i).trans hDfloor
    have hbandNat :
        (peelingBand G (approxRegularThreshold D) (i + 1)).card ≤
          Fintype.card V := by
      simpa only [Finset.card_univ] using
        Finset.card_le_univ
          (peelingBand G (approxRegularThreshold D) (i + 1))
    have hbandReal :
        ((peelingBand G (approxRegularThreshold D) (i + 1)).card : ℝ) ≤
          (Fintype.card V : ℝ) := by
      exact_mod_cast hbandNat
    have hband := hbandReal.trans hvertex
    obtain ⟨H, hHle, hHfree, hHweight⟩ :=
      exists_pathFree_subgraph_of_peelingLayer
        G (approxRegularThreshold D) (r := r) (n := n)
          (Δ := keyLemmaLayerDegreeCap D i) i hr hn hband hcapDegree hcapFloor
    let W : ℝ := ballsBinsWeight
      (subgraphFindingBinCount n
        (peelingBand G (approxRegularThreshold D) (i + 1)).card)
      (keyLemmaLayerDegreeCap D i)
    have hW : 0 ≤ W := ballsBinsWeight_nonneg _ _
    have hmassScaled :
        Real.exp (-1) ^ (i + 1) * (edgeCount G : ℝ) / 3 * W ≤
          (edgeCount (peelingLayer G (approxRegularThreshold D) (i + 1)) : ℝ) /
            3 * W := by
      calc
        Real.exp (-1) ^ (i + 1) * (edgeCount G : ℝ) / 3 * W =
            (Real.exp (-1) ^ (i + 1) * (edgeCount G : ℝ)) * (W / 3) := by
          ring
        _ ≤ (edgeCount (peelingLayer G (approxRegularThreshold D) (i + 1)) : ℝ) *
              (W / 3) :=
          mul_le_mul_of_nonneg_right hlayerMass (div_nonneg hW (by norm_num))
        _ = (edgeCount (peelingLayer G (approxRegularThreshold D) (i + 1)) : ℝ) /
              3 * W := by ring
    refine ⟨H, hHle.trans
      (peelingLayer_succ_le_initial G (approxRegularThreshold D) i),
        hHfree, ?_⟩
    exact (hLayerWeight i hi hlayerMass).trans
      (hmassScaled.trans (by simpa only [W] using hHweight))

/-! ## Raw-weight and literal Key-Lemma wrappers -/

/-- Version of the generic assembly theorem which accepts the raw dense
balls-and-bins inequality and an explicit numerical dominance theorem. -/
theorem keyLemmaAssembly_of_denseRaw [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {D r n : ℕ} {β target : ℝ}
    (hr : 21 ≤ r)
    (hn : 100 * Real.log (r : ℝ) ≤ (n : ℝ))
    (hD : 0 < D) (hdegree : ∀ v, G.degree v ≤ D)
    (hcard : (Fintype.card V : ℝ) ≤
      ((r : ℝ) * Real.log (r : ℝ) * n) / 4)
    (hDfloor : D ≤ ⌊(r : ℝ) * Real.log (r : ℝ)⌋₊)
    (hβ : 0 < β) (hβOne : β ≤ 1) (htarget : 0 ≤ target)
    (hnumeric : ∀ j : ℕ, 1 ≤ j →
      keyLemmaDenseDenominator β j ≤ keyLemmaDenseNumerator β j)
    (hDenseWeight : KeyLemmaDenseRawWeightBound G D r n β target)
    (hResidualWeight : KeyLemmaResidualWeightBound G r n target) :
    ∃ H : SimpleGraph V,
      H ≤ G ∧ (pathGraph n).Free H ∧ target ≤ (edgeCount H : ℝ) := by
  apply keyLemmaAssembly_of_weight_bounds G hr hn hD hdegree hcard hDfloor
  · exact keyLemmaLayerWeightBound_of_denseRaw G hD hdegree hβ hβOne
      htarget hnumeric hDenseWeight
  · exact hResidualWeight

/-- `KeyLemmaNumerics` supplies a single `β₀` for all dense layers.  For
that `β₀`, the only remaining premises are the two honestly named raw
balls-and-bins weight interfaces.  The conclusion has the literal
`60 e(G) / (β^0.9 r)` target of BLS Lemma 2.1. -/
theorem exists_keyLemmaAssembly_beta0 [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {D r n : ℕ}
    (hr : 21 ≤ r)
    (hn : 100 * Real.log (r : ℝ) ≤ (n : ℝ))
    (hD : 0 < D) (hdegree : ∀ v, G.degree v ≤ D)
    (hcard : (Fintype.card V : ℝ) ≤
      ((r : ℝ) * Real.log (r : ℝ) * n) / 4)
    (hDfloor : D ≤ ⌊(r : ℝ) * Real.log (r : ℝ)⌋₊) :
    ∃ β₀ : ℝ, β₀ ∈ Set.Ioc (0 : ℝ) 1 ∧
      ∀ β : ℝ, 0 < β → β ≤ β₀ →
        KeyLemmaDenseRawWeightBound G D r n β
          (keyLemmaAssemblyTarget G r β) →
        KeyLemmaResidualWeightBound G r n
          (keyLemmaAssemblyTarget G r β) →
        ∃ H : SimpleGraph V,
          H ≤ G ∧ (pathGraph n).Free H ∧
            keyLemmaAssemblyTarget G r β ≤ (edgeCount H : ℝ) := by
  obtain ⟨β₀, hβ₀, hdenseNumeric⟩ := exists_keyLemmaDense_beta0
  refine ⟨β₀, hβ₀, ?_⟩
  intro β hβ hββ₀ hDenseWeight hResidualWeight
  have hβOne : β ≤ 1 := hββ₀.trans hβ₀.2
  have htarget : 0 ≤ keyLemmaAssemblyTarget G r β :=
    keyLemmaAssemblyTarget_nonneg G r hβ (by omega)
  have hnumeric : ∀ j : ℕ, 1 ≤ j →
      keyLemmaDenseDenominator β j ≤ keyLemmaDenseNumerator β j := by
    intro j hj
    simpa only [keyLemmaDenseDenominator, keyLemmaDenseNumerator,
      keyLemmaDenseConstant] using hdenseNumeric β hβ hββ₀ j hj
  exact keyLemmaAssembly_of_denseRaw G hr hn hD hdegree hcard hDfloor
    hβ hβOne htarget hnumeric hDenseWeight hResidualWeight

end

end LeanCo.SizeRamsey
