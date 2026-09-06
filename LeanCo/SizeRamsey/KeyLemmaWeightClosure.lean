import LeanCo.SizeRamsey.BallsBinsLowerBound
import LeanCo.SizeRamsey.KeyLemmaBridge

/-!
# Closing the Key-Lemma weight interfaces

This module feeds the literal finite balls-and-bins lower bound into the two
remaining analytic interfaces of `KeyLemmaBridge`.  Natural ceilings are
kept explicit so that every application of Appendix A.10 has genuine
natural reference parameters.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open Finset SimpleGraph Filter Set Topology

noncomputable section

universe u

variable {V : Type u}

/-- Natural reference bin count for the final-residual branch. -/
def keyLemmaResidualBinReference (r : ℕ) : ℕ :=
  ⌈7 * (r : ℝ) * Real.log (r : ℝ)⌉₊

/-- Natural reference bin count for dense layer `i+1`. -/
def keyLemmaDenseBinReference (r i : ℕ) (β : ℝ) : ℕ :=
  ⌈8 * (r : ℝ) /
      (approxRegularRatio ^ (i + 1) * β)⌉₊

/-- The natural upper degree reference for dense layer `i+1`. -/
def keyLemmaDenseDegreeReference (D i : ℕ) : ℕ :=
  approxRegularThreshold D i

theorem keyLemmaLayerDegreeCap_le_denseDegreeReference (D i : ℕ) :
    keyLemmaLayerDegreeCap D i ≤ keyLemmaDenseDegreeReference D i := by
  cases i with
  | zero => simp [keyLemmaDenseDegreeReference]
  | succ i =>
      simp only [keyLemmaDenseDegreeReference, keyLemmaLayerDegreeCap_succ]
      exact Nat.sub_le _ _

/-! ## A strengthened finite A.10 consequence

The literal paper-facing theorem uses the constant `120`.  Its finite
negative-association proof has enough slack to give `60`; this genuine
strengthening absorbs the exact natural ceiling in the dense branch. -/

theorem ballsBinsExplicitThreshold_lt_three_div_twenty_balls_of_three_lt
    {q d : ℕ} (hq : 2 ≤ q) (hd : 0 < d)
    (hy : 3 < ballsBinsExplicitThreshold q d) :
    ballsBinsExplicitThreshold q d < 3 * (d : ℝ) / 20 := by
  let L : ℝ := Real.log (q : ℝ)
  let c : ℝ := (q : ℝ) * L / (2 * d)
  let ell : ℝ := Real.log (1 + c)
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hLpos : 0 < L := by
    dsimp only [L]
    exact Real.log_pos (by exact_mod_cast hq)
  have hcpos : 0 < c := by
    dsimp only [c]
    positivity
  have hellpos : 0 < ell := by
    dsimp only [ell]
    exact Real.log_pos (by linarith)
  have hy' : 3 < L / (20 * ell) := by
    simpa only [ballsBinsExplicitThreshold, L, c, ell] using hy
  have hLsmall : L < 2 * d := by
    by_contra hnot
    have hLlarge : 2 * (d : ℝ) ≤ L := le_of_not_gt hnot
    have hcq : (q : ℝ) ≤ c := by
      dsimp only [c]
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (d : ℝ))).2
      nlinarith
    have hlog : L ≤ ell := by
      dsimp only [L, ell]
      exact Real.log_le_log hqpos (by linarith : (q : ℝ) ≤ 1 + c)
    have hySmall : L / (20 * ell) ≤ (1 : ℝ) / 20 := by
      calc
        L / (20 * ell) ≤ L / (20 * L) :=
          div_le_div_of_nonneg_left hLpos.le (by positivity)
            (mul_le_mul_of_nonneg_left hlog (by norm_num))
        _ = (1 : ℝ) / 20 := by field_simp [ne_of_gt hLpos]
    linarith
  have hellLower : c / (1 + c) ≤ ell := by
    simpa only [ell] using div_one_add_le_log_one_add hcpos.le
  have hrough : L / (20 * ell) ≤ L / (20 * (c / (1 + c))) :=
    div_le_div_of_nonneg_left hLpos.le (by positivity)
      (mul_le_mul_of_nonneg_left hellLower (by norm_num))
  have hsimplify :
      L / (20 * (c / (1 + c))) =
        (d : ℝ) / (10 * q) + L / 20 := by
    dsimp only [c]
    field_simp [ne_of_gt hqpos, ne_of_gt hdpos, ne_of_gt hLpos]
    ring
  rw [hsimplify] at hrough
  have hqtwo : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hfirst : (d : ℝ) / (10 * q) ≤ d / 20 := by
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).2
    nlinarith
  have hsecond : L / 20 < (d : ℝ) / 10 := by linarith
  have : L / (20 * ell) < 3 * (d : ℝ) / 20 := by linarith
  simpa only [ballsBinsExplicitThreshold, L, c, ell] using this

/-- Strengthened same-parameter A.10 bound with constant `60`. -/
theorem ballsBinsWeight_lower_bound_same_parameters_sixty
    {q d : ℕ} (hq : 2 ≤ q) (hd : 0 < d) :
    Real.log (q : ℝ) /
        (60 * d * Real.log (1 + (q : ℝ) * Real.log q / (2 * d))) ≤
      ballsBinsWeight q d := by
  have hrewrite :
      Real.log (q : ℝ) /
          (60 * d * Real.log (1 + (q : ℝ) * Real.log q / (2 * d))) =
        ballsBinsExplicitThreshold q d / (3 * d) := by
    unfold ballsBinsExplicitThreshold
    ring
  rw [hrewrite]
  let y : ℝ := ballsBinsExplicitThreshold q d
  have hyNonneg : 0 ≤ y := ballsBinsExplicitThreshold_nonneg hq hd
  by_cases hySmall : y ≤ 3
  · calc
      y / (3 * d) ≤ (3 : ℝ) / (3 * d) :=
        div_le_div_of_nonneg_right hySmall (by positivity)
      _ = (1 : ℝ) / d := by field_simp
      _ ≤ ballsBinsWeight q d :=
        one_div_balls_le_ballsBinsWeight (by omega) hd
  · have hyLarge : 3 < y := lt_of_not_ge hySmall
    let t : ℕ := ⌊y⌋₊
    have htLe : (t : ℝ) ≤ y := by
      dsimp only [t]
      exact Nat.floor_le hyNonneg
    have htThree : 3 ≤ t := by
      dsimp only [t]
      exact Nat.le_floor hyLarge.le
    have htpos : 0 < t := by omega
    have hyThreeHalves : 2 * y ≤ 3 * (t : ℝ) := by
      have hfloor := Nat.lt_floor_add_one y
      have htTwo : (2 : ℝ) ≤ t := by exact_mod_cast (show 2 ≤ t by omega)
      nlinarith
    have hyBall :=
      ballsBinsExplicitThreshold_lt_three_div_twenty_balls_of_three_lt
        hq hd hyLarge
    have htHalfNat : 2 * t ≤ d := by
      have htReal : 2 * (t : ℝ) < d := by
        calc
          2 * (t : ℝ) ≤ 2 * y := by linarith
          _ < 2 * (3 * (d : ℝ) / 20) := by linarith
          _ < d := by
            have hdR : (0 : ℝ) < d := by exact_mod_cast hd
            nlinarith
      exact_mod_cast htReal.le
    have htarget : y / (3 * d) ≤ (t : ℝ) / (2 * d) := by
      apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 3 * d)
        (by positivity : (0 : ℝ) < 2 * d)).2
      nlinarith
    let k : Fin q := ⟨0, by omega⟩
    have hthreshold : (t : ℝ) / (2 * d) ≤ ballsBinsWeight q d := by
      by_cases hdense : q * t ≤ d
      · apply threshold_div_two_balls_le_ballsBinsWeight_of_mass hq hd k
        exact allocation_card_le_mul_tail_card_of_mul_threshold_le
          (by omega) k hdense
      · have hsparse : d < q * t := by omega
        have hcert := log_certificate_of_le_explicitThreshold hq hd
          (show (t : ℝ) ≤ ballsBinsExplicitThreshold q d by exact htLe)
          hsparse
        apply threshold_div_two_balls_le_ballsBinsWeight_of_pointMass hq hd k
        exact pointMass_of_log_certificate hq htpos htHalfNat hcert
    exact htarget.trans hthreshold

/-- Monotone natural-reference form of the strengthened bound. -/
theorem ballsBinsWeight_lower_bound_nat_sixty
    {q d Q D : ℕ} (hq : 2 ≤ q) (hd : 0 < d)
    (hQ : q ≤ Q) (hD : d ≤ D) :
    Real.log (Q : ℝ) /
        (60 * D * Real.log (1 + (Q : ℝ) * Real.log Q / (2 * D))) ≤
      ballsBinsWeight q d := by
  have hQtwo : 2 ≤ Q := hq.trans hQ
  have hDpos : 0 < D := hd.trans_le hD
  have hsame := ballsBinsWeight_lower_bound_same_parameters_sixty hQtwo hDpos
  have hballs : ballsBinsWeight Q D ≤ ballsBinsWeight Q d :=
    ballsBinsWeight_antitone_balls (by omega) hd hD
  have hbins : ballsBinsWeight Q d ≤ ballsBinsWeight q d :=
    ballsBinsWeight_antitone_bins_of_le (by omega) hQ
  exact hsame.trans (hballs.trans hbins)

/-! ## Dense-layer natural parameter bounds -/

/-- The exact layer cap never exceeds its unrounded preceding scale. -/
theorem keyLemmaLayerDegreeCap_cast_le_scale
    {D i : ℕ} (hD : 0 < D) :
    (keyLemmaLayerDegreeCap D i : ℝ) ≤ approxRegularScale D i := by
  cases i with
  | zero => simp
  | succ i =>
      rw [keyLemmaLayerDegreeCap_succ]
      exact (approxRegularThreshold_sub_one_cast_lt_scale D (i + 1) hD).le

/-- Before the stopping time, the natural dense degree reference loses at
most the explicit factor `22/21` to the ceiling. -/
theorem denseDegreeReference_cast_le_scale_mul
    {D r i : ℕ} (hr : 21 ≤ r) (hD : 0 < D)
    (hi : i < approxRegularStop D r) :
    (keyLemmaDenseDegreeReference D i : ℝ) ≤
      (22 / 21 : ℝ) * approxRegularScale D i := by
  have hrpos : 0 < r := by omega
  have hscaleR : (r : ℝ) < approxRegularScale D i :=
    approxRegularStop_minimal D r i hD hrpos hi
  have hrCast : (21 : ℝ) ≤ r := by exact_mod_cast hr
  have hone : (1 : ℝ) ≤ approxRegularScale D i / 21 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 21)).2
    simpa using hrCast.trans hscaleR.le
  have hceil := approxRegularThreshold_cast_lt_scale_add_one D i
  unfold keyLemmaDenseDegreeReference
  calc
    (approxRegularThreshold D i : ℝ) ≤
        approxRegularScale D i + 1 := hceil.le
    _ ≤ (22 / 21 : ℝ) * approxRegularScale D i := by
      nlinarith

/-- The two edge-count premises of a selected dense layer bound its actual
bin count by the paper's natural reference ceiling. -/
theorem subgraphFindingBinCount_le_denseReference
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {D r n i : ℕ} {β : ℝ}
    (hr : 21 ≤ r) (hn : 0 < n) (hβ : 0 < β) (hβOne : β ≤ 1)
    (hmax : (D : ℝ) = β * r * Real.log (r : ℝ))
    (hedgeUpper : (edgeCount G : ℝ) ≤
      (r : ℝ) ^ 2 * Real.log (r : ℝ) * n)
    (hcount : approxRegularThreshold D (i + 1) *
        (peelingBand G (approxRegularThreshold D) (i + 1)).card ≤
      2 * edgeCount
        (peelingLayer G (approxRegularThreshold D) (i + 1))) :
    subgraphFindingBinCount n
        (peelingBand G (approxRegularThreshold D) (i + 1)).card ≤
      keyLemmaDenseBinReference r i β := by
  let v := (peelingBand G (approxRegularThreshold D) (i + 1)).card
  let q := subgraphFindingBinCount n v
  let a := (v + 1) / 2
  let c : ℝ := approxRegularRatio ^ (i + 1)
  have hrpos : (0 : ℝ) < r := by positivity
  have hlogpos : 0 < Real.log (r : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < r by omega))
  have hcpos : 0 < c := by
    dsimp only [c]
    exact pow_pos approxRegularRatio_pos _
  have hApos : 0 < β * c := mul_pos hβ hcpos
  have hAle : β * c ≤ 1 := by
    have hcOne : c ≤ 1 := by
      dsimp only [c]
      exact pow_le_one₀ approxRegularRatio_nonneg approxRegularRatio_le_one
    nlinarith [mul_nonneg hβ.le hcpos.le]
  have hlayerLe : edgeCount
      (peelingLayer G (approxRegularThreshold D) (i + 1)) ≤ edgeCount G :=
    edgeCount_mono (peelingLayer_succ_le_initial
      G (approxRegularThreshold D) i)
  have hcountR :
      (approxRegularThreshold D (i + 1) : ℝ) * v ≤
        2 * (edgeCount
          (peelingLayer G (approxRegularThreshold D) (i + 1)) : ℝ) := by
    exact_mod_cast hcount
  have hscale : approxRegularScale D (i + 1) =
      (β * c) * ((r : ℝ) * Real.log (r : ℝ)) := by
    dsimp only [approxRegularScale, c]
    rw [hmax]
    ring
  have hvScaled : (β * c) * (v : ℝ) ≤ 2 * r * n := by
    have hchain : approxRegularScale D (i + 1) * v ≤
        2 * ((r : ℝ) ^ 2 * Real.log (r : ℝ) * n) := by
      calc
        approxRegularScale D (i + 1) * v ≤
            (approxRegularThreshold D (i + 1) : ℝ) * v :=
          mul_le_mul_of_nonneg_right
            (approxRegularScale_le_threshold_cast D (i + 1)) (by positivity)
        _ ≤ 2 * (edgeCount
            (peelingLayer G (approxRegularThreshold D) (i + 1)) : ℝ) :=
          hcountR
        _ ≤ 2 * (edgeCount G : ℝ) := by
          exact_mod_cast Nat.mul_le_mul_left 2 hlayerLe
        _ ≤ 2 * ((r : ℝ) ^ 2 * Real.log (r : ℝ) * n) :=
          mul_le_mul_of_nonneg_left hedgeUpper (by norm_num)
    rw [hscale] at hchain
    have hcancel : 0 < (r : ℝ) * Real.log (r : ℝ) :=
      mul_pos hrpos hlogpos
    apply (mul_le_mul_iff_of_pos_right hcancel).1
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hchain
  have hqNat : n * q ≤ 6 * a := by
    dsimp only [q, a]
    exact mul_subgraphFindingBinCount_le n v
  have haNat : 2 * a ≤ v + 1 := by
    dsimp only [a]
    exact Nat.mul_div_le _ _
  have hqR : (n : ℝ) * q ≤ 3 * (v + 1) := by
    have hqCast : (n : ℝ) * q ≤ 6 * a := by exact_mod_cast hqNat
    have haCast : (2 : ℝ) * a ≤ v + 1 := by exact_mod_cast haNat
    nlinarith
  have hsmall : 3 * (β * c) ≤ 2 * (r : ℝ) * n := by
    have hrn : (2 : ℝ) ≤ (r : ℝ) * n := by
      have hrTwo : (2 : ℝ) ≤ r := by exact_mod_cast (show 2 ≤ r by omega)
      have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith [mul_le_mul hrTwo hnOne (by norm_num) (by positivity)]
    nlinarith
  have hqUpper : (q : ℝ) ≤ 8 * (r : ℝ) / (β * c) := by
    apply (le_div_iff₀ hApos).2
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    apply (mul_le_mul_iff_of_pos_right hnR).1
    calc
      ((q : ℝ) * (β * c)) * n = (β * c) * ((n : ℝ) * q) := by ring
      _ ≤ (β * c) * (3 * (v + 1)) :=
        mul_le_mul_of_nonneg_left hqR hApos.le
      _ = 3 * ((β * c) * v) + 3 * (β * c) := by ring
      _ ≤ 3 * (2 * (r : ℝ) * n) + 2 * (r : ℝ) * n := by
        gcongr
      _ = (8 * (r : ℝ)) * n := by ring
  unfold keyLemmaDenseBinReference
  have hceil := Nat.le_ceil (8 * (r : ℝ) /
    (approxRegularRatio ^ (i + 1) * β))
  have hqUpper' : (q : ℝ) ≤
      8 * (r : ℝ) /
        (approxRegularRatio ^ (i + 1) * β) := by
    dsimp only [c] at hqUpper
    convert hqUpper using 1 <;> ring
  have hcast : (q : ℝ) ≤
      (⌈8 * (r : ℝ) /
        (approxRegularRatio ^ (i + 1) * β)⌉₊ : ℝ) :=
    hqUpper'.trans hceil
  exact_mod_cast hcast

/-- A selected mass-dense layer has enough band vertices to make its bin
count at least two. -/
theorem two_le_subgraphFindingBinCount_denseLayer
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {D r n i : ℕ} {β : ℝ}
    (hr : 21 ≤ r) (hn : 0 < n) (hβ : 0 < β) (hβOne : β ≤ 1)
    (hmax : (D : ℝ) = β * r * Real.log (r : ℝ))
    (hedgeLower : Real.rpow (r : ℝ) (7 / 4 : ℝ) * n ≤
      (edgeCount G : ℝ))
    (hgrowth : 3 * ((r : ℝ) * Real.log (r : ℝ)) ≤
      Real.rpow (r : ℝ) (7 / 4 : ℝ))
    (hmass : Real.exp (-1) ^ (i + 1) * (edgeCount G : ℝ) ≤
      (edgeCount
        (peelingLayer G (approxRegularThreshold D) (i + 1)) : ℝ))
    (hcountUpper :
      edgeCount (peelingLayer G (approxRegularThreshold D) (i + 1)) ≤
        (peelingBand G (approxRegularThreshold D) (i + 1)).card *
          keyLemmaLayerDegreeCap D i) :
    2 ≤ subgraphFindingBinCount n
      (peelingBand G (approxRegularThreshold D) (i + 1)).card := by
  let v := (peelingBand G (approxRegularThreshold D) (i + 1)).card
  have hrpos : (0 : ℝ) < r := by positivity
  have hlogpos : 0 < Real.log (r : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < r by omega))
  have hDrealpos : (0 : ℝ) < D := by
    rw [hmax]
    positivity
  have hD : 0 < D := by exact_mod_cast hDrealpos
  have hbase : (r : ℝ) * Real.log (r : ℝ) ≤
      Real.exp (-1) * Real.rpow (r : ℝ) (7 / 4 : ℝ) := by
    have he : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
    have hmul : Real.exp 1 * ((r : ℝ) * Real.log (r : ℝ)) ≤
        Real.rpow (r : ℝ) (7 / 4 : ℝ) := by
      calc
        Real.exp 1 * ((r : ℝ) * Real.log (r : ℝ)) ≤
            3 * ((r : ℝ) * Real.log (r : ℝ)) :=
          mul_le_mul_of_nonneg_right he (by positivity)
        _ ≤ Real.rpow (r : ℝ) (7 / 4 : ℝ) := hgrowth
    rw [Real.exp_neg]
    change (r : ℝ) * Real.log (r : ℝ) ≤
      (Real.exp 1)⁻¹ * Real.rpow (r : ℝ) (7 / 4 : ℝ)
    rw [inv_mul_eq_div]
    apply (le_div_iff₀ (Real.exp_pos 1)).2
    simpa [mul_comm] using hmul
  have hratioLe : approxRegularRatio ≤ Real.exp (-1) := by
    unfold approxRegularRatio
    exact Real.exp_le_exp.mpr (by norm_num)
  have hratioPow : approxRegularRatio ^ i ≤ Real.exp (-1) ^ i :=
    pow_le_pow_left₀ approxRegularRatio_nonneg hratioLe i
  have hβbase : β * ((r : ℝ) * Real.log (r : ℝ)) ≤
      (r : ℝ) * Real.log (r : ℝ) := by
    calc
      β * ((r : ℝ) * Real.log (r : ℝ)) ≤
          1 * ((r : ℝ) * Real.log (r : ℝ)) :=
        mul_le_mul_of_nonneg_right hβOne
          (mul_nonneg hrpos.le hlogpos.le)
      _ = (r : ℝ) * Real.log (r : ℝ) := by ring
  have hscaleUpper : approxRegularScale D i ≤
      Real.exp (-1) ^ (i + 1) *
        Real.rpow (r : ℝ) (7 / 4 : ℝ) := by
    rw [approxRegularScale, hmax]
    calc
      (β * (r : ℝ) * Real.log (r : ℝ)) * approxRegularRatio ^ i =
          (β * ((r : ℝ) * Real.log (r : ℝ))) *
            approxRegularRatio ^ i := by ring
      _ ≤ ((r : ℝ) * Real.log (r : ℝ)) * approxRegularRatio ^ i :=
        mul_le_mul_of_nonneg_right hβbase
          (pow_nonneg approxRegularRatio_nonneg i)
      _ ≤ ((r : ℝ) * Real.log (r : ℝ)) * Real.exp (-1) ^ i :=
        mul_le_mul_of_nonneg_left hratioPow (by positivity)
      _ ≤ (Real.exp (-1) * Real.rpow (r : ℝ) (7 / 4 : ℝ)) *
          Real.exp (-1) ^ i :=
        mul_le_mul_of_nonneg_right hbase (by positivity)
      _ = Real.exp (-1) ^ (i + 1) *
          Real.rpow (r : ℝ) (7 / 4 : ℝ) := by
        rw [pow_succ]
        ring
  have hscalePos : 0 < approxRegularScale D i :=
    approxRegularScale_pos D i hD
  have hcountUpperR :
      (edgeCount
        (peelingLayer G (approxRegularThreshold D) (i + 1)) : ℝ) ≤
      (v : ℝ) * keyLemmaLayerDegreeCap D i := by
    exact_mod_cast hcountUpper
  have hnvScaled : approxRegularScale D i * n ≤
      (v : ℝ) * approxRegularScale D i := by
    calc
      approxRegularScale D i * n ≤
          (Real.exp (-1) ^ (i + 1) *
            Real.rpow (r : ℝ) (7 / 4 : ℝ)) * n :=
        mul_le_mul_of_nonneg_right hscaleUpper (by positivity)
      _ ≤ Real.exp (-1) ^ (i + 1) * (edgeCount G : ℝ) := by
        have := mul_le_mul_of_nonneg_left hedgeLower
          (show 0 ≤ Real.exp (-1) ^ (i + 1) by positivity)
        simpa [mul_comm, mul_left_comm, mul_assoc] using this
      _ ≤ (edgeCount
          (peelingLayer G (approxRegularThreshold D) (i + 1)) : ℝ) := hmass
      _ ≤ (v : ℝ) * keyLemmaLayerDegreeCap D i := hcountUpperR
      _ ≤ (v : ℝ) * approxRegularScale D i :=
        mul_le_mul_of_nonneg_left
          (keyLemmaLayerDegreeCap_cast_le_scale hD) (by positivity)
  have hnvR : (n : ℝ) ≤ v := by
    apply (mul_le_mul_iff_of_pos_right hscalePos).1
    simpa [mul_comm] using hnvScaled
  have hnv : n ≤ v := by exact_mod_cast hnvR
  rw [subgraphFindingBinCount, Nat.le_div_iff_mul_le hn]
  have hvhalf : v ≤ 2 * ((v + 1) / 2) := by omega
  simpa only [v] using (show 2 * n ≤ 6 * ((v + 1) / 2) by omega)

/-- Two bins are already guaranteed once the vertex count dominates the
path length. -/
theorem two_le_subgraphFindingBinCount_of_le {n v : ℕ}
    (hn : 0 < n) (hnv : n ≤ v) :
    2 ≤ subgraphFindingBinCount n v := by
  rw [subgraphFindingBinCount, Nat.le_div_iff_mul_le hn]
  have hvhalf : v ≤ 2 * ((v + 1) / 2) := by omega
  omega

/-- Maximum degree plus the Key-Lemma edge lower bound force enough
vertices to make the residual bin count nondegenerate. -/
theorem keyLemma_vertexCard_ge_pathLength
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {r n : ℕ} {β : ℝ}
    (hr : 2 ≤ r) (hn : 0 < n) (hβ : 0 < β) (hβOne : β ≤ 1)
    (hmax : (G.maxDegree : ℝ) =
      β * r * Real.log (r : ℝ))
    (hedge : Real.rpow (r : ℝ) (7 / 4 : ℝ) * n ≤
      (edgeCount G : ℝ))
    (hgrowth : (r : ℝ) * Real.log (r : ℝ) ≤
      Real.rpow (r : ℝ) (7 / 4 : ℝ)) :
    n ≤ Fintype.card V := by
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hlogpos : 0 < Real.log (r : ℝ) :=
    Real.log_pos (by exact_mod_cast hr)
  have hrlogpos : 0 < (r : ℝ) * Real.log (r : ℝ) :=
    mul_pos hrpos hlogpos
  have hedgeNat : edgeCount G ≤ Fintype.card V * G.maxDegree := by
    apply edgeCount_le_card_mul_of_edgeMeetingSet_degree_upper G Finset.univ
    · intro x y _hxy
      simp
    · intro v _hv
      exact G.degree_le_maxDegree v
  have hedgeReal : (edgeCount G : ℝ) ≤
      (Fintype.card V : ℝ) * G.maxDegree := by
    exact_mod_cast hedgeNat
  have hDle : (G.maxDegree : ℝ) ≤
      (r : ℝ) * Real.log (r : ℝ) := by
    rw [hmax]
    calc
      β * (r : ℝ) * Real.log (r : ℝ) =
          β * ((r : ℝ) * Real.log (r : ℝ)) := by ring
      _ ≤ 1 * ((r : ℝ) * Real.log (r : ℝ)) :=
        mul_le_mul_of_nonneg_right hβOne hrlogpos.le
      _ = (r : ℝ) * Real.log (r : ℝ) := by ring
  have hmain :
      ((r : ℝ) * Real.log (r : ℝ)) * n ≤
        (Fintype.card V : ℝ) *
          ((r : ℝ) * Real.log (r : ℝ)) := by
    calc
      ((r : ℝ) * Real.log (r : ℝ)) * n ≤
          Real.rpow (r : ℝ) (7 / 4 : ℝ) * n :=
        mul_le_mul_of_nonneg_right hgrowth (by positivity)
      _ ≤ (edgeCount G : ℝ) := hedge
      _ ≤ (Fintype.card V : ℝ) * G.maxDegree := hedgeReal
      _ ≤ (Fintype.card V : ℝ) *
          ((r : ℝ) * Real.log (r : ℝ)) :=
        mul_le_mul_of_nonneg_left hDle (by positivity)
  have hcast : (n : ℝ) ≤ Fintype.card V := by
    apply (mul_le_mul_iff_of_pos_right hrlogpos).1
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmain
  exact_mod_cast hcast

/-- The quarter-size vertex hypothesis implies the natural residual bin
reference bound. -/
theorem subgraphFindingBinCount_le_residualReference
    {r n v : ℕ} (hr : 21 ≤ r)
    (hn : 100 * Real.log (r : ℝ) ≤ (n : ℝ))
    (hv : (v : ℝ) ≤
      ((r : ℝ) * Real.log (r : ℝ) * n) / 4) :
    subgraphFindingBinCount n v ≤ keyLemmaResidualBinReference r := by
  have hrpos : (0 : ℝ) < r := by positivity
  have hlogpos : 0 < Real.log (r : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < r by omega))
  have hvLoose : (v : ℝ) ≤
      2 * ((r : ℝ) * Real.log (r : ℝ)) * n := by
    have hbase : 0 ≤ (r : ℝ) * Real.log (r : ℝ) * n := by positivity
    nlinarith
  have hq := subgraphFindingBinCount_le_seven_mul hr hn hvLoose
  unfold keyLemmaResidualBinReference
  have hceil := Nat.le_ceil (7 * (r : ℝ) * Real.log (r : ℝ))
  have hcast : (subgraphFindingBinCount n v : ℝ) ≤
      (⌈7 * (r : ℝ) * Real.log (r : ℝ)⌉₊ : ℝ) := by
    have hq' : (subgraphFindingBinCount n v : ℝ) ≤
        7 * (r : ℝ) * Real.log (r : ℝ) := by
      convert hq using 1 <;> ring
    exact hq'.trans hceil
  exact_mod_cast hcast

/-- Elementary logarithmic bounds for the natural residual reference.  The
ceiling error is absorbed by `7 r log r + 1 ≤ 8 r log r`. -/
theorem keyLemmaResidualReference_log_bounds (r : ℕ) (hr : 21 ≤ r) :
    let Q := keyLemmaResidualBinReference r
    Real.log (r : ℝ) ≤ Real.log (Q : ℝ) ∧
      Real.log (Q : ℝ) ≤ 3 * Real.log (r : ℝ) ∧
      Real.log (1 + (Q : ℝ) * Real.log Q / (2 * r)) ≤
        6 * Real.log (Real.log (r : ℝ)) := by
  let L : ℝ := Real.log (r : ℝ)
  let Q : ℕ := keyLemmaResidualBinReference r
  have hrpos : (0 : ℝ) < r := by positivity
  have hexpTwo : Real.exp 2 < (21 : ℝ) := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    have he := Real.exp_one_lt_three
    have hepos := Real.exp_pos 1
    nlinarith
  have hLtwo : 2 < L := by
    dsimp only [L]
    apply (Real.lt_log_iff_exp_lt hrpos).2
    exact hexpTwo.trans_le (by exact_mod_cast hr)
  have hLpos : 0 < L := by linarith
  have hrLone : 1 ≤ (r : ℝ) * L := by
    have hrOne : (1 : ℝ) ≤ r := by
      exact_mod_cast (show 1 ≤ r by omega)
    calc
      (1 : ℝ) ≤ 1 * 2 := by norm_num
      _ ≤ (r : ℝ) * L :=
        mul_le_mul hrOne hLtwo.le (by norm_num) (by positivity)
  have hQlower : 7 * (r : ℝ) * L ≤ Q := by
    dsimp only [Q, keyLemmaResidualBinReference, L]
    exact Nat.le_ceil _
  have hQupperStrict : (Q : ℝ) < 7 * (r : ℝ) * L + 1 := by
    dsimp only [Q, keyLemmaResidualBinReference, L]
    exact Nat.ceil_lt_add_one (by positivity)
  have hQupper : (Q : ℝ) ≤ 8 * (r : ℝ) * L := by
    linarith
  have hrQ : (r : ℝ) ≤ Q := by
    calc
      (r : ℝ) ≤ 7 * (r : ℝ) * L := by nlinarith [mul_pos hrpos hLpos]
      _ ≤ Q := hQlower
  have hQpos : (0 : ℝ) < Q := hrpos.trans_le hrQ
  have hlogLower : L ≤ Real.log (Q : ℝ) := by
    dsimp only [L]
    exact Real.log_le_log hrpos hrQ
  have hLr : L ≤ (r : ℝ) - 1 := by
    dsimp only [L]
    exact Real.log_le_sub_one_of_pos hrpos
  have hcube : (Q : ℝ) ≤ (r : ℝ) ^ 3 := by
    calc
      (Q : ℝ) ≤ 8 * (r : ℝ) * L := hQupper
      _ ≤ (r : ℝ) ^ 3 := by
        have hrCast : (21 : ℝ) ≤ r := by exact_mod_cast hr
        nlinarith [sq_nonneg ((r : ℝ) - 4)]
  have hlogUpper : Real.log (Q : ℝ) ≤ 3 * L := by
    calc
      Real.log (Q : ℝ) ≤ Real.log ((r : ℝ) ^ 3) :=
        Real.log_le_log hQpos hcube
      _ = 3 * L := by
        rw [Real.log_pow]
        rfl
  have hlogQnonneg : 0 ≤ Real.log (Q : ℝ) :=
    Real.log_nonneg (by linarith)
  have hratio :
      (Q : ℝ) * Real.log Q / (2 * r) ≤ 12 * L ^ 2 := by
    calc
      (Q : ℝ) * Real.log Q / (2 * r) ≤
          (8 * (r : ℝ) * L) * (3 * L) / (2 * r) := by
        gcongr
      _ = 12 * L ^ 2 := by
        field_simp [ne_of_gt hrpos]
        ring
  have hpoly : 1 + 12 * L ^ 2 ≤ L ^ 6 := by
    have hLsq : 4 ≤ L ^ 2 := by nlinarith [sq_nonneg (L - 2)]
    have hLfour : 16 ≤ L ^ 4 := by
      nlinarith [sq_nonneg (L ^ 2 - 4)]
    have hsqpos : 0 ≤ L ^ 2 := sq_nonneg L
    calc
      1 + 12 * L ^ 2 ≤ 13 * L ^ 2 := by nlinarith
      _ ≤ L ^ 4 * L ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) hsqpos
      _ = L ^ 6 := by ring
  have hinsidePos : 0 < 1 + (Q : ℝ) * Real.log Q / (2 * r) := by
    have : 0 ≤ (Q : ℝ) * Real.log Q / (2 * r) := by positivity
    linarith
  have hdenom :
      Real.log (1 + (Q : ℝ) * Real.log Q / (2 * r)) ≤
        6 * Real.log L := by
    calc
      Real.log (1 + (Q : ℝ) * Real.log Q / (2 * r)) ≤
          Real.log (1 + 12 * L ^ 2) :=
        Real.log_le_log hinsidePos (by linarith)
      _ ≤ Real.log (L ^ 6) :=
        Real.log_le_log (by positivity) hpoly
      _ = 6 * Real.log L := by rw [Real.log_pow]; norm_num
  simpa only [Q, L] using ⟨hlogLower, hlogUpper, hdenom⟩

/-- The lower admissible value `β = 1/(7 log r)` still leaves a
`(log r)^0.07` factor after taking the `0.9` power. -/
theorem log_rpow_seven_hundred_div_seven_le_beta_rpow_mul_log
    {L β : ℝ} (hL : 1 ≤ L) (hβ : 0 < β)
    (hβLower : (7 * L)⁻¹ ≤ β) :
    Real.rpow L (7 / 100 : ℝ) / 7 ≤
      Real.rpow β (9 / 10 : ℝ) * L := by
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hbasepos : 0 < 7 * L := by positivity
  have hinvpos : 0 < (7 * L)⁻¹ := inv_pos.mpr hbasepos
  have hβpow : Real.rpow ((7 * L)⁻¹) (9 / 10 : ℝ) ≤
      Real.rpow β (9 / 10 : ℝ) :=
    Real.rpow_le_rpow hinvpos.le hβLower (by norm_num)
  have hLpow : Real.rpow L (7 / 100 : ℝ) ≤
      Real.rpow L (1 / 10 : ℝ) := by
    exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  have hSevenPow : Real.rpow (7 : ℝ) (9 / 10 : ℝ) ≤ 7 := by
    calc
      Real.rpow (7 : ℝ) (9 / 10 : ℝ) ≤ Real.rpow 7 1 :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 7 := Real.rpow_one 7
  have hidentity :
      Real.rpow ((7 * L)⁻¹) (9 / 10 : ℝ) * L =
        Real.rpow L (1 / 10 : ℝ) /
          Real.rpow 7 (9 / 10 : ℝ) := by
    change ((7 * L)⁻¹) ^ (9 / 10 : ℝ) * L =
      L ^ (1 / 10 : ℝ) / (7 : ℝ) ^ (9 / 10 : ℝ)
    rw [Real.inv_rpow hbasepos.le,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 7) hLpos.le]
    have hsub := Real.rpow_sub hLpos (1 : ℝ) (9 / 10 : ℝ)
    norm_num [Real.rpow_one] at hsub
    rw [hsub]
    field_simp [ne_of_gt (Real.rpow_pos_of_pos hLpos (9 / 10 : ℝ)),
      ne_of_gt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 7)
        (9 / 10 : ℝ))]
  calc
    Real.rpow L (7 / 100 : ℝ) / 7 ≤
        Real.rpow L (1 / 10 : ℝ) / 7 :=
      div_le_div_of_nonneg_right hLpow (by norm_num)
    _ ≤ Real.rpow L (1 / 10 : ℝ) /
        Real.rpow 7 (9 / 10 : ℝ) :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg hLpos.le _)
        (Real.rpow_pos_of_pos (by norm_num) _)
        hSevenPow
    _ = Real.rpow ((7 * L)⁻¹) (9 / 10 : ℝ) * L := hidentity.symm
    _ ≤ Real.rpow β (9 / 10 : ℝ) * L :=
      mul_le_mul_of_nonneg_right hβpow hLpos.le

/-- The existing remainder asymptotic, at one explicit constant, implies
the scalar inequality required by the residual A.10 application. -/
theorem keyLemmaResidual_scalar_of_log_ratio
    {r : ℕ} {β : ℝ} (hr : 21 ≤ r) (hβ : 0 < β)
    (hβLower : (7 * Real.log (r : ℝ))⁻¹ ≤ β)
    (hratio : (2721600 : ℝ) ≤
      Real.rpow (Real.log (r : ℝ)) (7 / 100 : ℝ) /
        Real.log (Real.log (r : ℝ))) :
    540 / (Real.rpow β (9 / 10 : ℝ) * r) ≤
      Real.log (keyLemmaResidualBinReference r : ℝ) /
        (120 * r *
          Real.log (1 +
            (keyLemmaResidualBinReference r : ℝ) *
              Real.log (keyLemmaResidualBinReference r) / (2 * r))) := by
  let L : ℝ := Real.log (r : ℝ)
  let Q : ℕ := keyLemmaResidualBinReference r
  have hrpos : (0 : ℝ) < r := by positivity
  have hexpTwo : Real.exp 2 < (21 : ℝ) := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    have he := Real.exp_one_lt_three
    have hepos := Real.exp_pos 1
    nlinarith
  have hLtwo : 2 < L := by
    dsimp only [L]
    apply (Real.lt_log_iff_exp_lt hrpos).2
    exact hexpTwo.trans_le (by exact_mod_cast hr)
  have hLpos : 0 < L := by linarith
  have hlogLpos : 0 < Real.log L := Real.log_pos (by linarith)
  have hratioCross :
      (2721600 : ℝ) * Real.log L ≤
        Real.rpow L (7 / 100 : ℝ) := by
    apply (le_div_iff₀ hlogLpos).1
    simpa only [L] using hratio
  have hratioScaled :
      (388800 : ℝ) * Real.log L ≤
        Real.rpow L (7 / 100 : ℝ) / 7 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 7)).2
    calc
      (388800 : ℝ) * Real.log L * 7 =
          2721600 * Real.log L := by ring
      _ ≤ Real.rpow L (7 / 100 : ℝ) := hratioCross
  have hbetaTerm : Real.rpow L (7 / 100 : ℝ) / 7 ≤
      Real.rpow β (9 / 10 : ℝ) * L := by
    apply log_rpow_seven_hundred_div_seven_le_beta_rpow_mul_log
      (by linarith) hβ
    simpa only [L] using hβLower
  have hcore : (388800 : ℝ) * Real.log L ≤
      Real.rpow β (9 / 10 : ℝ) * L :=
    hratioScaled.trans hbetaTerm
  have hβpowpos : 0 < Real.rpow β (9 / 10 : ℝ) :=
    Real.rpow_pos_of_pos hβ _
  have hcoef :
      540 / (Real.rpow β (9 / 10 : ℝ) * r) ≤
        L / (720 * r * Real.log L) := by
    apply (div_le_div_iff₀ (mul_pos hβpowpos hrpos)
      (by positivity : (0 : ℝ) < 720 * (r : ℝ) * Real.log L)).2
    have hmul := mul_le_mul_of_nonneg_right hcore hrpos.le
    convert hmul using 1 <;> ring
  obtain ⟨hlogLower, _hlogUpper, hdenUpper⟩ :=
    keyLemmaResidualReference_log_bounds r hr
  have hQpos : (0 : ℝ) < Q := by
    have : (0 : ℝ) < Real.log (Q : ℝ) := hLpos.trans_le hlogLower
    exact zero_lt_one.trans ((Real.log_pos_iff (by positivity)).1 this)
  have hlogQpos : 0 < Real.log (Q : ℝ) := hLpos.trans_le hlogLower
  have hinnerTerm : 0 < (Q : ℝ) * Real.log Q / (2 * r) := by positivity
  have hdenPos : 0 < Real.log (1 + (Q : ℝ) * Real.log Q / (2 * r)) :=
    Real.log_pos (by linarith)
  have hdenScaled :
      120 * (r : ℝ) *
          Real.log (1 + (Q : ℝ) * Real.log Q / (2 * r)) ≤
        720 * r * Real.log L := by
    calc
      120 * (r : ℝ) *
          Real.log (1 + (Q : ℝ) * Real.log Q / (2 * r)) ≤
          (120 * r) * (6 * Real.log L) :=
        mul_le_mul_of_nonneg_left
          (by simpa only [Q, L] using hdenUpper)
          (show (0 : ℝ) ≤ 120 * r by positivity)
      _ = 720 * r * Real.log L := by ring
  have hA10 : L / (720 * r * Real.log L) ≤
      Real.log (Q : ℝ) /
        (120 * r * Real.log (1 + (Q : ℝ) * Real.log Q / (2 * r))) := by
    calc
      L / (720 * r * Real.log L) ≤
          L / (120 * r *
            Real.log (1 + (Q : ℝ) * Real.log Q / (2 * r))) :=
        div_le_div_of_nonneg_left hLpos.le (by positivity) hdenScaled
      _ ≤ Real.log (Q : ℝ) /
          (120 * r *
            Real.log (1 + (Q : ℝ) * Real.log Q / (2 * r))) :=
        div_le_div_of_nonneg_right hlogLower (by positivity)
  simpa only [Q, L] using hcoef.trans hA10

/-- Complete residual interface at fixed parameters, with only the two
graph-independent eventual inequalities left explicit. -/
theorem keyLemmaResidualWeightBound_of_keyLemma_hypotheses
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {r n : ℕ} {β : ℝ}
    (hr : 21 ≤ r)
    (hn : 100 * Real.log (r : ℝ) ≤ (n : ℝ))
    (hβ : 0 < β) (hβLower : (7 * Real.log (r : ℝ))⁻¹ ≤ β)
    (hβOne : β ≤ 1)
    (hmax : (G.maxDegree : ℝ) = β * r * Real.log (r : ℝ))
    (hcard : (Fintype.card V : ℝ) ≤
      ((r : ℝ) * Real.log (r : ℝ) * n) / 4)
    (hedge : Real.rpow (r : ℝ) (7 / 4 : ℝ) * n ≤
      (edgeCount G : ℝ))
    (hgrowth : (r : ℝ) * Real.log (r : ℝ) ≤
      Real.rpow (r : ℝ) (7 / 4 : ℝ))
    (hratio : (2721600 : ℝ) ≤
      Real.rpow (Real.log (r : ℝ)) (7 / 100 : ℝ) /
        Real.log (Real.log (r : ℝ))) :
    KeyLemmaResidualWeightBound G r n
      (keyLemmaAssemblyTarget G r β) := by
  have hlogpos : 0 < Real.log (r : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < r by omega))
  have hnposReal : (0 : ℝ) < n :=
    (show (0 : ℝ) < 100 * Real.log (r : ℝ) by positivity).trans_le hn
  have hnpos : 0 < n := by exact_mod_cast hnposReal
  have hvertex : n ≤ Fintype.card V :=
    keyLemma_vertexCard_ge_pathLength G (by omega) hnpos hβ hβOne
      hmax hedge hgrowth
  have hqTwo : 2 ≤ subgraphFindingBinCount n (Fintype.card V) :=
    two_le_subgraphFindingBinCount_of_le hnpos hvertex
  have hqRef : subgraphFindingBinCount n (Fintype.card V) ≤
      keyLemmaResidualBinReference r :=
    subgraphFindingBinCount_le_residualReference hr hn hcard
  have hscalar := keyLemmaResidual_scalar_of_log_ratio hr hβ hβLower hratio
  have hweight := ballsBinsWeight_lower_bound_nat
    hqTwo (show 0 < r by omega) hqRef (show r ≤ r from le_rfl)
  have hcoef :
      540 / (Real.rpow β (9 / 10 : ℝ) * r) ≤
        ballsBinsWeight
          (subgraphFindingBinCount n (Fintype.card V)) r :=
    hscalar.trans hweight
  have hedgeNonneg : 0 ≤ (edgeCount G : ℝ) / 9 := by positivity
  unfold KeyLemmaResidualWeightBound keyLemmaAssemblyTarget
  calc
    60 * (edgeCount G : ℝ) /
          (Real.rpow β (9 / 10 : ℝ) * r) =
        (edgeCount G : ℝ) / 9 *
          (540 / (Real.rpow β (9 / 10 : ℝ) * r)) := by ring
    _ ≤ (edgeCount G : ℝ) / 9 *
          ballsBinsWeight
            (subgraphFindingBinCount n (Fintype.card V)) r :=
      mul_le_mul_of_nonneg_left hcoef hedgeNonneg

/-- Eventually `r log r ≤ r^(7/4)`, the degree-growth comparison used to
force at least two bins in both extraction branches. -/
theorem exists_keyLemma_degree_growth_threshold :
    ∃ r₀ : ℕ, ∀ r : ℕ, r₀ ≤ r →
      (r : ℝ) * Real.log (r : ℝ) ≤
        Real.rpow (r : ℝ) (7 / 4 : ℝ) := by
  have htend :
      Tendsto
        (fun r : ℕ =>
          Real.rpow (r : ℝ) (3 / 4 : ℝ) / Real.log (r : ℝ))
        atTop atTop :=
    (tendsto_rpow_div_log_atTop
      (show (0 : ℝ) < 3 / 4 by norm_num)).comp
        tendsto_natCast_atTop_atTop
  have heventRatio : ∀ᶠ r : ℕ in atTop,
      (1 : ℝ) ≤
        Real.rpow (r : ℝ) (3 / 4 : ℝ) / Real.log (r : ℝ) :=
    htend.eventually (eventually_ge_atTop 1)
  have heventTwo : ∀ᶠ r : ℕ in atTop, 2 ≤ r := eventually_ge_atTop 2
  obtain ⟨r₀, hr₀⟩ := eventually_atTop.1 (heventRatio.and heventTwo)
  refine ⟨r₀, ?_⟩
  intro r hr
  obtain ⟨hratio, hrTwo⟩ := hr₀ r hr
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hlogpos : 0 < Real.log (r : ℝ) :=
    Real.log_pos (by exact_mod_cast hrTwo)
  have hlogpow : Real.log (r : ℝ) ≤
      Real.rpow (r : ℝ) (3 / 4 : ℝ) :=
    by simpa using (le_div_iff₀ hlogpos).1 hratio
  calc
    (r : ℝ) * Real.log (r : ℝ) ≤
        (r : ℝ) * Real.rpow (r : ℝ) (3 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_left hlogpow hrpos.le
    _ = Real.rpow (r : ℝ) (7 / 4 : ℝ) := by
      change (r : ℝ) * (r : ℝ) ^ (3 / 4 : ℝ) =
        (r : ℝ) ^ (7 / 4 : ℝ)
      rw [show (7 / 4 : ℝ) = 1 + 3 / 4 by norm_num,
        Real.rpow_add hrpos, Real.rpow_one]

/-- Graph-uniform eventual closure of the entire residual branch. -/
theorem exists_keyLemmaResidualWeightBound_eventually :
    ∃ r₀ : ℕ, ∀ r : ℕ, r₀ ≤ r →
      ∀ n : ℕ, 100 * Real.log (r : ℝ) ≤ (n : ℝ) →
        ∀ N : ℕ, ∀ G : SimpleGraph (Fin N), ∀ β : ℝ,
          (7 * Real.log (r : ℝ))⁻¹ ≤ β →
          β ≤ keyLemmaGlobalBeta0 →
          ((@SimpleGraph.maxDegree (Fin N) G inferInstance
              (Classical.decRel _)) : ℝ) =
            β * r * Real.log (r : ℝ) →
          (N : ℝ) ≤ ((r : ℝ) * Real.log (r : ℝ) * n) / 4 →
          Real.rpow (r : ℝ) (7 / 4 : ℝ) * n ≤
            (edgeCount G : ℝ) →
          KeyLemmaResidualWeightBound G r n
            (keyLemmaAssemblyTarget G r β) := by
  obtain ⟨rGrowth, hGrowth⟩ := exists_keyLemma_degree_growth_threshold
  obtain ⟨rRatio, hRatio⟩ :=
    exists_keyLemmaRemainder_nat_threshold (2721600 : ℝ)
  refine ⟨max 21 (max rGrowth rRatio), ?_⟩
  intro r hrLarge n hn N G β hβLower hβUpper hmax hcard hedge
  letI : DecidableRel G.Adj := Classical.decRel _
  have hr : 21 ≤ r := (le_max_left 21 (max rGrowth rRatio)).trans hrLarge
  have hrg : rGrowth ≤ r :=
    (le_max_left rGrowth rRatio).trans
      ((le_max_right 21 (max rGrowth rRatio)).trans hrLarge)
  have hrr : rRatio ≤ r :=
    (le_max_right rGrowth rRatio).trans
      ((le_max_right 21 (max rGrowth rRatio)).trans hrLarge)
  have hlogpos : 0 < Real.log (r : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < r by omega))
  have hβpos : 0 < β := by
    exact (inv_pos.mpr (mul_pos (by norm_num) hlogpos)).trans_le hβLower
  have hβOne : β ≤ 1 := hβUpper.trans keyLemmaGlobalBeta0_mem.2
  have hcard' : (Fintype.card (Fin N) : ℝ) ≤
      ((r : ℝ) * Real.log (r : ℝ) * n) / 4 := by
    simpa using hcard
  exact keyLemmaResidualWeightBound_of_keyLemma_hypotheses G hr hn
    hβpos hβLower hβOne hmax hcard' hedge (hGrowth r hrg) (hRatio r hrr)

/-- Once the actual residual bin count and the remaining scalar inequality
are available, Appendix A.10 closes the residual weight interface. -/
theorem keyLemmaResidualWeightBound_of_reference
    [Fintype V] (G : SimpleGraph V)
    {r n : ℕ} {β : ℝ}
    (hr : 2 ≤ r) (hβ : 0 < β)
    (hqTwo : 2 ≤ subgraphFindingBinCount n (Fintype.card V))
    (hqRef : subgraphFindingBinCount n (Fintype.card V) ≤
      keyLemmaResidualBinReference r)
    (hscalar :
      540 / (Real.rpow β (9 / 10 : ℝ) * r) ≤
        Real.log (keyLemmaResidualBinReference r : ℝ) /
          (120 * r *
            Real.log (1 +
              (keyLemmaResidualBinReference r : ℝ) *
                Real.log (keyLemmaResidualBinReference r) / (2 * r)))) :
    KeyLemmaResidualWeightBound G r n
      (keyLemmaAssemblyTarget G r β) := by
  have hrPos : 0 < r := by omega
  have hweight := ballsBinsWeight_lower_bound_nat
    hqTwo hrPos hqRef (show r ≤ r from le_rfl)
  have hcoef :
      540 / (Real.rpow β (9 / 10 : ℝ) * r) ≤
        ballsBinsWeight
          (subgraphFindingBinCount n (Fintype.card V)) r :=
    hscalar.trans hweight
  have hedgeNonneg : 0 ≤ (edgeCount G : ℝ) / 9 := by positivity
  unfold KeyLemmaResidualWeightBound keyLemmaAssemblyTarget
  calc
    60 * (edgeCount G : ℝ) /
          (Real.rpow β (9 / 10 : ℝ) * r) =
        (edgeCount G : ℝ) / 9 *
          (540 / (Real.rpow β (9 / 10 : ℝ) * r)) := by ring
    _ ≤ (edgeCount G : ℝ) / 9 *
          ballsBinsWeight
            (subgraphFindingBinCount n (Fintype.card V)) r :=
      mul_le_mul_of_nonneg_left hcoef hedgeNonneg

/-! ## Dense-layer logarithmic reference bounds -/

/-- The dense reference has at least `r` bins.  This is deliberately stated
at the cast level, which is the form needed by logarithmic monotonicity. -/
theorem le_keyLemmaDenseBinReference_cast
    {r i : ℕ} {β : ℝ} (hr : 0 < r) (hβ : 0 < β) (hβOne : β ≤ 1) :
    (r : ℝ) ≤ (keyLemmaDenseBinReference r i β : ℝ) := by
  have hcpos : 0 < approxRegularRatio ^ (i + 1) :=
    pow_pos approxRegularRatio_pos _
  have hcle : approxRegularRatio ^ (i + 1) ≤ 1 :=
    pow_le_one₀ approxRegularRatio_nonneg approxRegularRatio_le_one
  have hdenpos : 0 < approxRegularRatio ^ (i + 1) * β :=
    mul_pos hcpos hβ
  have hdenle : approxRegularRatio ^ (i + 1) * β ≤ 1 := by
    calc
      approxRegularRatio ^ (i + 1) * β ≤ 1 * β :=
        mul_le_mul_of_nonneg_right hcle hβ.le
      _ ≤ 1 := by simpa using hβOne
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hx : (r : ℝ) ≤
      8 * (r : ℝ) / (approxRegularRatio ^ (i + 1) * β) := by
    apply (le_div_iff₀ hdenpos).2
    nlinarith
  unfold keyLemmaDenseBinReference
  exact hx.trans (Nat.le_ceil _)

/-- Before the stopping time the dense bin reference is bounded by a
graph-independent multiple of `r log r`.  This is the exact place where the
minimality of the peeling stopping time is used. -/
theorem keyLemmaDenseBinReference_cast_lt_sixteen_exp_two
    {D r i : ℕ} {β : ℝ}
    (hr : 21 ≤ r) (hβ : 0 < β) (hβOne : β ≤ 1)
    (hmax : (D : ℝ) = β * r * Real.log (r : ℝ))
    (hi : i < approxRegularStop D r) :
    (keyLemmaDenseBinReference r i β : ℝ) <
      16 * Real.exp 2 * (r : ℝ) * Real.log (r : ℝ) := by
  let c : ℝ := approxRegularRatio ^ i
  let X : ℝ := 8 * (r : ℝ) /
    (approxRegularRatio ^ (i + 1) * β)
  have hrpos : (0 : ℝ) < r := by positivity
  have hlogpos : 0 < Real.log (r : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < r by omega))
  have hcpos : 0 < c := by
    dsimp only [c]
    exact pow_pos approxRegularRatio_pos _
  have hDrealpos : (0 : ℝ) < D := by rw [hmax]; positivity
  have hD : 0 < D := by exact_mod_cast hDrealpos
  have hstop := approxRegularStop_minimal D r i hD (by omega) hi
  have hscale : approxRegularScale D i =
      (β * c) * ((r : ℝ) * Real.log (r : ℝ)) := by
    rw [approxRegularScale, hmax]
    dsimp only [c]
    ring
  rw [hscale] at hstop
  have hcancel : 1 < (β * c) * Real.log (r : ℝ) := by
    apply (mul_lt_mul_iff_of_pos_left hrpos).1
    simpa [mul_comm, mul_left_comm, mul_assoc] using hstop
  have hβcpos : 0 < β * c := mul_pos hβ hcpos
  have hinvlt : (β * c)⁻¹ < Real.log (r : ℝ) := by
    rw [← one_div]
    apply (div_lt_iff₀ hβcpos).2
    simpa [mul_comm] using hcancel
  have hratioInv : approxRegularRatio⁻¹ = Real.exp 2 := by
    unfold approxRegularRatio
    rw [Real.exp_neg]
    simp
  have hXidentity : X =
      8 * (r : ℝ) * Real.exp 2 * (β * c)⁻¹ := by
    dsimp only [X, c]
    rw [pow_succ, div_eq_mul_inv, mul_inv, mul_inv, hratioInv]
    ring
  have hXupper : X <
      8 * Real.exp 2 * (r : ℝ) * Real.log (r : ℝ) := by
    rw [hXidentity]
    have hcoef : 0 < 8 * (r : ℝ) * Real.exp 2 := by positivity
    nlinarith [mul_lt_mul_of_pos_left hinvlt hcoef]
  have hdenpos : 0 < approxRegularRatio ^ (i + 1) * β :=
    mul_pos (pow_pos approxRegularRatio_pos _) hβ
  have hXone : 1 ≤ X := by
    dsimp only [X]
    have hdenle : approxRegularRatio ^ (i + 1) * β ≤ 1 := by
      have hcOne := pow_le_one₀ approxRegularRatio_nonneg
        approxRegularRatio_le_one (n := i + 1)
      calc
        approxRegularRatio ^ (i + 1) * β ≤ 1 * β :=
          mul_le_mul_of_nonneg_right hcOne hβ.le
        _ ≤ 1 := by simpa using hβOne
    apply (le_div_iff₀ hdenpos).2
    have hrOne : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
    nlinarith
  have hceil : (keyLemmaDenseBinReference r i β : ℝ) < X + 1 := by
    unfold keyLemmaDenseBinReference
    exact Nat.ceil_lt_add_one (by positivity)
  calc
    (keyLemmaDenseBinReference r i β : ℝ) < X + 1 := hceil
    _ ≤ 2 * X := by linarith
    _ < 16 * Real.exp 2 * (r : ℝ) * Real.log (r : ℝ) := by
      nlinarith

/-- The ceiling in the dense bin reference costs at most a factor two. -/
theorem keyLemmaDenseBinReference_cast_le_twice_raw
    {r i : ℕ} {β : ℝ} (hr : 0 < r) (hβ : 0 < β)
    (hβOne : β ≤ 1) :
    (keyLemmaDenseBinReference r i β : ℝ) ≤
      16 * (r : ℝ) /
        (approxRegularRatio ^ (i + 1) * β) := by
  let X : ℝ := 8 * (r : ℝ) /
    (approxRegularRatio ^ (i + 1) * β)
  have hcpos : 0 < approxRegularRatio ^ (i + 1) :=
    pow_pos approxRegularRatio_pos _
  have hdenpos : 0 < approxRegularRatio ^ (i + 1) * β :=
    mul_pos hcpos hβ
  have hcOne : approxRegularRatio ^ (i + 1) ≤ 1 :=
    pow_le_one₀ approxRegularRatio_nonneg approxRegularRatio_le_one
  have hdenle : approxRegularRatio ^ (i + 1) * β ≤ 1 := by
    calc
      approxRegularRatio ^ (i + 1) * β ≤ 1 * β :=
        mul_le_mul_of_nonneg_right hcOne hβ.le
      _ ≤ 1 := by simpa using hβOne
  have hrOne : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
  have hXone : 1 ≤ X := by
    dsimp only [X]
    apply (le_div_iff₀ hdenpos).2
    nlinarith
  have hceil : (keyLemmaDenseBinReference r i β : ℝ) < X + 1 := by
    unfold keyLemmaDenseBinReference
    exact Nat.ceil_lt_add_one (by positivity)
  calc
    (keyLemmaDenseBinReference r i β : ℝ) ≤ X + 1 := hceil.le
    _ ≤ 2 * X := by linarith
    _ = 16 * (r : ℝ) /
        (approxRegularRatio ^ (i + 1) * β) := by
      dsimp only [X]
      ring

/-- Under one graph-independent eventual growth estimate, the dense natural
reference has logarithm between `log r` and `3 log r`. -/
theorem keyLemmaDenseBinReference_log_bounds
    {D r i : ℕ} {β : ℝ}
    (hr : 21 ≤ r) (hβ : 0 < β) (hβOne : β ≤ 1)
    (hmax : (D : ℝ) = β * r * Real.log (r : ℝ))
    (hi : i < approxRegularStop D r)
    (hgrowth : 16 * Real.exp 2 * Real.log (r : ℝ) ≤ (r : ℝ) ^ 2) :
    Real.log (r : ℝ) ≤
        Real.log (keyLemmaDenseBinReference r i β : ℝ) ∧
      Real.log (keyLemmaDenseBinReference r i β : ℝ) ≤
        3 * Real.log (r : ℝ) := by
  let Q := keyLemmaDenseBinReference r i β
  have hrpos : (0 : ℝ) < r := by positivity
  have hrQ : (r : ℝ) ≤ Q :=
    le_keyLemmaDenseBinReference_cast (by omega) hβ hβOne
  have hQpos : (0 : ℝ) < Q := hrpos.trans_le hrQ
  have hQrough : (Q : ℝ) <
      16 * Real.exp 2 * (r : ℝ) * Real.log (r : ℝ) := by
    simpa only [Q] using
      keyLemmaDenseBinReference_cast_lt_sixteen_exp_two
        hr hβ hβOne hmax hi
  have hQcube : (Q : ℝ) ≤ (r : ℝ) ^ 3 := by
    calc
      (Q : ℝ) ≤
          16 * Real.exp 2 * (r : ℝ) * Real.log (r : ℝ) :=
        hQrough.le
      _ = (r : ℝ) *
          (16 * Real.exp 2 * Real.log (r : ℝ)) := by ring
      _ ≤ (r : ℝ) * ((r : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hgrowth hrpos.le
      _ = (r : ℝ) ^ 3 := by ring
  constructor
  · exact Real.log_le_log hrpos hrQ
  · calc
      Real.log (Q : ℝ) ≤ Real.log ((r : ℝ) ^ 3) :=
        Real.log_le_log hQpos hQcube
      _ = 3 * Real.log (r : ℝ) := by
        rw [Real.log_pow]
        norm_num

/-- The rational expression arising from the two natural reference
parameters fits under the paper's `5 / (β² c₁^(2j))` envelope. -/
theorem one_add_dense_reference_ratio_le
    {i : ℕ} {β : ℝ} (hβ : 0 < β) (hβOne : β ≤ 1) :
    1 + 24 /
        (β ^ 2 *
          (approxRegularRatio ^ (i + 1) * approxRegularRatio ^ i)) ≤
      5 / (β ^ 2 * (approxRegularRatio ^ (i + 1)) ^ 2) := by
  let a : ℝ := approxRegularRatio ^ i
  let c : ℝ := approxRegularRatio ^ (i + 1)
  have hratioSixth : approxRegularRatio < (1 : ℝ) / 6 := by
    have hexpTwo : (6 : ℝ) < Real.exp 2 := by
      rw [show (2 : ℝ) = (2 : ℕ) * 1 by norm_num,
        Real.exp_nat_mul]
      nlinarith [Real.exp_one_gt_d9]
    unfold approxRegularRatio
    rw [Real.exp_neg]
    simpa only [one_div] using
      (one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 6) hexpTwo)
  have hapos : 0 < a := by
    dsimp only [a]
    exact pow_pos approxRegularRatio_pos _
  have hcpos : 0 < c := by
    dsimp only [c]
    exact pow_pos approxRegularRatio_pos _
  have hcOne : c ≤ 1 := by
    dsimp only [c]
    exact pow_le_one₀ approxRegularRatio_nonneg approxRegularRatio_le_one
  have hβc : 0 ≤ β * c := mul_nonneg hβ.le hcpos.le
  have hβcOne : β * c ≤ 1 := by
    calc
      β * c ≤ β * 1 := mul_le_mul_of_nonneg_left hcOne hβ.le
      _ ≤ 1 := by simpa using hβOne
  have hsq : β ^ 2 * c ^ 2 ≤ 1 := by
    calc
      β ^ 2 * c ^ 2 = (β * c) ^ 2 := by ring
      _ ≤ (1 : ℝ) ^ 2 :=
        (sq_le_sq₀ hβc (by norm_num)).2 hβcOne
      _ = 1 := by norm_num
  have hdenpos : 0 < β ^ 2 * c ^ 2 := by positivity
  have hid :
      (1 + 24 / (β ^ 2 * (c * a))) * (β ^ 2 * c ^ 2) =
        β ^ 2 * c ^ 2 + 24 * approxRegularRatio := by
    have ha : a ≠ 0 := ne_of_gt hapos
    have hc : c ≠ 0 := ne_of_gt hcpos
    have hβne : β ≠ 0 := ne_of_gt hβ
    dsimp only [a, c] at *
    rw [pow_succ]
    field_simp [hβne, ha, hc, ne_of_gt approxRegularRatio_pos]
    <;> ring
  apply (le_div_iff₀ hdenpos).2
  rw [show approxRegularRatio ^ (i + 1) = c by rfl,
    show approxRegularRatio ^ i = a by rfl, hid]
  nlinarith

/-- Complete logarithmic denominator estimate for the dense A.10
application.  Both natural ceilings are retained in the statement. -/
theorem keyLemmaDenseReference_denominator_log_bound
    {D r i : ℕ} {β : ℝ}
    (hr : 21 ≤ r) (hβ : 0 < β) (hβOne : β ≤ 1)
    (hmax : (D : ℝ) = β * r * Real.log (r : ℝ))
    (hi : i < approxRegularStop D r)
    (hgrowth : 16 * Real.exp 2 * Real.log (r : ℝ) ≤ (r : ℝ) ^ 2) :
    Real.log
        (1 + (keyLemmaDenseBinReference r i β : ℝ) *
          Real.log (keyLemmaDenseBinReference r i β) /
            (2 * keyLemmaDenseDegreeReference D i)) ≤
      4 * ((i + 1 : ℕ) : ℝ) + Real.log (5 / β ^ 2) := by
  let Q : ℕ := keyLemmaDenseBinReference r i β
  let R : ℕ := keyLemmaDenseDegreeReference D i
  let a : ℝ := approxRegularRatio ^ i
  let c : ℝ := approxRegularRatio ^ (i + 1)
  let L : ℝ := Real.log (r : ℝ)
  have hrpos : (0 : ℝ) < r := by positivity
  have hLpos : 0 < L := by
    dsimp only [L]
    exact Real.log_pos (by exact_mod_cast (show 1 < r by omega))
  have hapos : 0 < a := by
    dsimp only [a]
    exact pow_pos approxRegularRatio_pos _
  have hcpos : 0 < c := by
    dsimp only [c]
    exact pow_pos approxRegularRatio_pos _
  have hDrealpos : (0 : ℝ) < D := by rw [hmax]; positivity
  have hD : 0 < D := by exact_mod_cast hDrealpos
  have hscalePos : 0 < approxRegularScale D i :=
    approxRegularScale_pos D i hD
  have hRlower : approxRegularScale D i ≤ (R : ℝ) := by
    dsimp only [R, keyLemmaDenseDegreeReference]
    exact approxRegularScale_le_threshold_cast D i
  have hRpos : (0 : ℝ) < R := hscalePos.trans_le hRlower
  obtain ⟨hlogLower, hlogUpper⟩ :=
    keyLemmaDenseBinReference_log_bounds hr hβ hβOne hmax hi hgrowth
  have hQpos : (0 : ℝ) < Q := by
    have hrQ := le_keyLemmaDenseBinReference_cast
      (i := i) (by omega : 0 < r) hβ hβOne
    exact hrpos.trans_le (by simpa only [Q] using hrQ)
  have hlogQpos : 0 < Real.log (Q : ℝ) := by
    exact hLpos.trans_le (by simpa only [Q, L] using hlogLower)
  have hQraw : (Q : ℝ) ≤ 16 * (r : ℝ) / (c * β) := by
    simpa only [Q, c] using
      keyLemmaDenseBinReference_cast_le_twice_raw
        (i := i) (by omega : 0 < r) hβ hβOne
  have hscale : approxRegularScale D i =
      β * (r : ℝ) * L * a := by
    dsimp only [approxRegularScale, L, a]
    rw [hmax]
  have hnumUpper :
      (Q : ℝ) * Real.log Q ≤
        (16 * (r : ℝ) / (c * β)) * (3 * L) := by
    apply mul_le_mul hQraw
      (by simpa only [Q, L] using hlogUpper)
    · exact hlogQpos.le
    · positivity
  have hfrac :
      (Q : ℝ) * Real.log Q / (2 * R) ≤
        24 / (β ^ 2 * (c * a)) := by
    calc
      (Q : ℝ) * Real.log Q / (2 * R) ≤
          ((16 * (r : ℝ) / (c * β)) * (3 * L)) /
            (2 * approxRegularScale D i) := by
        apply div_le_div₀ (by positivity) hnumUpper (by positivity)
        exact mul_le_mul_of_nonneg_left hRlower (by norm_num)
      _ = 24 / (β ^ 2 * (c * a)) := by
        rw [hscale]
        have hβne : β ≠ 0 := ne_of_gt hβ
        have hrne : (r : ℝ) ≠ 0 := ne_of_gt hrpos
        have hLne : L ≠ 0 := ne_of_gt hLpos
        have hane : a ≠ 0 := ne_of_gt hapos
        have hcne : c ≠ 0 := ne_of_gt hcpos
        field_simp [hβne, hrne, hLne, hane, hcne]
        <;> ring
  have hinner :
      1 + (Q : ℝ) * Real.log Q / (2 * R) ≤
        5 / (β ^ 2 * c ^ 2) := by
    calc
      1 + (Q : ℝ) * Real.log Q / (2 * R) ≤
          1 + 24 / (β ^ 2 * (c * a)) := by linarith
      _ ≤ 5 / (β ^ 2 * c ^ 2) := by
        simpa only [a, c] using
          one_add_dense_reference_ratio_le (i := i) hβ hβOne
  have hinsidePos : 0 < 1 + (Q : ℝ) * Real.log Q / (2 * R) := by
    have : 0 ≤ (Q : ℝ) * Real.log Q / (2 * R) := by positivity
    linarith
  have henvPos : 0 < 5 / (β ^ 2 * c ^ 2) := by positivity
  have hlogEnvelope :
      Real.log (5 / (β ^ 2 * c ^ 2)) =
        4 * ((i + 1 : ℕ) : ℝ) + Real.log (5 / β ^ 2) := by
    have hβne : β ≠ 0 := ne_of_gt hβ
    have hcne : c ≠ 0 := ne_of_gt hcpos
    rw [Real.log_div (by norm_num) (mul_ne_zero (pow_ne_zero 2 hβne)
          (pow_ne_zero 2 hcne)),
      Real.log_mul (pow_ne_zero 2 hβne) (pow_ne_zero 2 hcne),
      Real.log_pow, Real.log_pow,
      Real.log_div (by norm_num) (pow_ne_zero 2 hβne),
      Real.log_pow]
    rw [Real.log_pow, approxRegularRatio, Real.log_exp]
    push_cast
    ring
  calc
    Real.log
        (1 + (keyLemmaDenseBinReference r i β : ℝ) *
          Real.log (keyLemmaDenseBinReference r i β) /
            (2 * keyLemmaDenseDegreeReference D i)) =
        Real.log (1 + (Q : ℝ) * Real.log Q / (2 * R)) := by rfl
    _ ≤ Real.log (5 / (β ^ 2 * c ^ 2)) :=
      Real.log_le_log hinsidePos hinner
    _ = 4 * ((i + 1 : ℕ) : ℝ) + Real.log (5 / β ^ 2) :=
      hlogEnvelope

/-- Every pre-stop layer cap is a genuine positive number of balls. -/
theorem keyLemmaLayerDegreeCap_pos_of_lt_stop
    {D r i : ℕ} (hr : 2 ≤ r) (hD : 0 < D)
    (hi : i < approxRegularStop D r) :
    0 < keyLemmaLayerDegreeCap D i := by
  cases i with
  | zero => simpa using hD
  | succ i =>
      rw [keyLemmaLayerDegreeCap_succ]
      have hscale : (1 : ℝ) < approxRegularScale D (i + 1) := by
        have hrReal : (1 : ℝ) < r := by
          exact_mod_cast (show (1 : ℕ) < r by omega)
        exact hrReal.trans
          (approxRegularStop_minimal D r (i + 1) hD (by omega) hi)
      have hthreshold : 1 < approxRegularThreshold D (i + 1) := by
        rw [nat_lt_approxRegularThreshold_iff]
        simpa using hscale
      omega

/-- The affine logarithmic factor in the dense numerical interface is
strictly positive. -/
theorem denseLogBracket_pos {i : ℕ} {β : ℝ}
    (hβ : 0 < β) (hβOne : β ≤ 1) :
    0 < 4 * ((i + 1 : ℕ) : ℝ) + Real.log (5 / β ^ 2) := by
  have hβSq : β ^ 2 ≤ 1 := by nlinarith [sq_nonneg β]
  have hβSqPos : 0 < β ^ 2 := pow_pos hβ _
  have hlog : 0 ≤ Real.log (5 / β ^ 2) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hβSqPos]
    nlinarith
  have hj : (1 : ℝ) ≤ (i + 1 : ℕ) := by exact_mod_cast (show 1 ≤ i + 1 by omega)
  nlinarith

/-- A.10, with exact natural parameters, gives the scalar lower bound used
in the dense raw interface. -/
theorem keyLemmaDenseWeight_scalar_lower_bound
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {D r n i : ℕ} {β : ℝ}
    (hr : 21 ≤ r) (hn : 0 < n) (hβ : 0 < β) (hβOne : β ≤ 1)
    (hmax : (D : ℝ) = β * r * Real.log (r : ℝ))
    (hedgeLower : Real.rpow (r : ℝ) (7 / 4 : ℝ) * n ≤
      (edgeCount G : ℝ))
    (hedgeUpper : (edgeCount G : ℝ) ≤
      (r : ℝ) ^ 2 * Real.log (r : ℝ) * n)
    (hdegreeGrowth : 3 * ((r : ℝ) * Real.log (r : ℝ)) ≤
      Real.rpow (r : ℝ) (7 / 4 : ℝ))
    (hreferenceGrowth :
      16 * Real.exp 2 * Real.log (r : ℝ) ≤ (r : ℝ) ^ 2)
    (hi : i < approxRegularStop D r)
    (hmass : Real.exp (-1) ^ (i + 1) * (edgeCount G : ℝ) ≤
      (edgeCount
        (peelingLayer G (approxRegularThreshold D) (i + 1)) : ℝ))
    (hcountLower : approxRegularThreshold D (i + 1) *
        (peelingBand G (approxRegularThreshold D) (i + 1)).card ≤
      2 * edgeCount
        (peelingLayer G (approxRegularThreshold D) (i + 1)))
    (hcountUpper :
      edgeCount (peelingLayer G (approxRegularThreshold D) (i + 1)) ≤
        (peelingBand G (approxRegularThreshold D) (i + 1)).card *
          keyLemmaLayerDegreeCap D i) :
    Real.log (r : ℝ) /
        (120 * approxRegularScale D i *
          (4 * ((i + 1 : ℕ) : ℝ) + Real.log (5 / β ^ 2))) ≤
      ballsBinsWeight
        (subgraphFindingBinCount n
          (peelingBand G (approxRegularThreshold D) (i + 1)).card)
        (keyLemmaLayerDegreeCap D i) := by
  let q := subgraphFindingBinCount n
    (peelingBand G (approxRegularThreshold D) (i + 1)).card
  let d := keyLemmaLayerDegreeCap D i
  let Q := keyLemmaDenseBinReference r i β
  let R := keyLemmaDenseDegreeReference D i
  let B : ℝ := 4 * ((i + 1 : ℕ) : ℝ) + Real.log (5 / β ^ 2)
  have hlogpos : 0 < Real.log (r : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < r by omega))
  have hDrealpos : (0 : ℝ) < D := by rw [hmax]; positivity
  have hD : 0 < D := by exact_mod_cast hDrealpos
  have hscalePos : 0 < approxRegularScale D i :=
    approxRegularScale_pos D i hD
  have hd : 0 < d := by
    dsimp only [d]
    exact keyLemmaLayerDegreeCap_pos_of_lt_stop (by omega) hD hi
  have hqTwo : 2 ≤ q := by
    dsimp only [q]
    exact two_le_subgraphFindingBinCount_denseLayer G hr hn hβ hβOne
      hmax hedgeLower hdegreeGrowth hmass hcountUpper
  have hqRef : q ≤ Q := by
    dsimp only [q, Q]
    exact subgraphFindingBinCount_le_denseReference G hr hn hβ hβOne
      hmax hedgeUpper hcountLower
  have hdRef : d ≤ R := by
    dsimp only [d, R]
    exact keyLemmaLayerDegreeCap_le_denseDegreeReference D i
  have hweight := ballsBinsWeight_lower_bound_nat_sixty
    hqTwo hd hqRef hdRef
  obtain ⟨hlogLower, _hlogUpper⟩ :=
    keyLemmaDenseBinReference_log_bounds hr hβ hβOne hmax hi
      hreferenceGrowth
  have hlogDenom := keyLemmaDenseReference_denominator_log_bound
    hr hβ hβOne hmax hi hreferenceGrowth
  have hRbound : (R : ℝ) ≤ 2 * approxRegularScale D i := by
    have hceil := denseDegreeReference_cast_le_scale_mul hr hD hi
    dsimp only [R] at hceil ⊢
    nlinarith [hscalePos.le]
  have hRpos : (0 : ℝ) < R := by
    have hRlower : approxRegularScale D i ≤ (R : ℝ) := by
      dsimp only [R, keyLemmaDenseDegreeReference]
      exact approxRegularScale_le_threshold_cast D i
    exact hscalePos.trans_le hRlower
  have hQpos : (0 : ℝ) < Q := by
    have hrQ := le_keyLemmaDenseBinReference_cast
      (i := i) (by omega : 0 < r) hβ hβOne
    exact (show (0 : ℝ) < r by positivity).trans_le
      (by simpa only [Q] using hrQ)
  have hlogQpos : 0 < Real.log (Q : ℝ) := by
    exact hlogpos.trans_le (by simpa only [Q] using hlogLower)
  have hinnerTerm : 0 < (Q : ℝ) * Real.log Q / (2 * R) := by positivity
  have hinnerLogPos :
      0 < Real.log (1 + (Q : ℝ) * Real.log Q / (2 * R)) :=
    Real.log_pos (by linarith)
  have hBpos : 0 < B := by
    dsimp only [B]
    exact denseLogBracket_pos hβ hβOne
  have hproduct :
      (R : ℝ) *
          Real.log (1 + (Q : ℝ) * Real.log Q / (2 * R)) ≤
        (2 * approxRegularScale D i) * B := by
    apply mul_le_mul hRbound
      (by simpa only [Q, R, B] using hlogDenom)
    · exact hinnerLogPos.le
    · positivity
  have hdenom :
      60 * (R : ℝ) *
          Real.log (1 + (Q : ℝ) * Real.log Q / (2 * R)) ≤
        120 * approxRegularScale D i * B := by
    nlinarith
  calc
    Real.log (r : ℝ) /
        (120 * approxRegularScale D i *
          (4 * ((i + 1 : ℕ) : ℝ) + Real.log (5 / β ^ 2))) =
        Real.log (r : ℝ) / (120 * approxRegularScale D i * B) := by rfl
    _ ≤ Real.log (r : ℝ) /
        (60 * (R : ℝ) *
          Real.log (1 + (Q : ℝ) * Real.log Q / (2 * R))) :=
      div_le_div_of_nonneg_left hlogpos.le (by positivity) hdenom
    _ ≤ Real.log (Q : ℝ) /
        (60 * (R : ℝ) *
          Real.log (1 + (Q : ℝ) * Real.log Q / (2 * R))) :=
      div_le_div_of_nonneg_right
        (by simpa only [Q] using hlogLower) (by positivity)
    _ ≤ ballsBinsWeight q d := by
      simpa only [Q, R, q, d] using hweight

/-- The two fractional powers of `β` in the target and dense numerator
combine to the ordinary reciprocal. -/
theorem denseBetaRpow_balance {β : ℝ} (hβ : 0 < β) :
    Real.rpow (1 / β) (1 / 10 : ℝ) /
      Real.rpow β (9 / 10 : ℝ) = 1 / β := by
  rw [show Real.rpow (1 / β) (1 / 10 : ℝ) =
      Real.rpow 1 (1 / 10 : ℝ) / Real.rpow β (1 / 10 : ℝ) from
    Real.div_rpow (by norm_num : (0 : ℝ) ≤ 1) hβ.le _]
  rw [div_div]
  have hadd : Real.rpow β (1 / 10 + 9 / 10 : ℝ) =
      Real.rpow β (1 / 10 : ℝ) * Real.rpow β (9 / 10 : ℝ) :=
    Real.rpow_add hβ _ _
  rw [← hadd]
  norm_num [Real.rpow_one, Real.one_rpow]

/-- The dense peeling decay and the repaired extra factor `exp 2` balance
exactly against the geometric degree scale. -/
theorem denseExpScale_balance (i : ℕ) :
    Real.exp (-1) ^ (i + 1) * Real.exp 2 =
      Real.exp ((i + 1 : ℕ) : ℝ) * approxRegularRatio ^ i := by
  unfold approxRegularRatio
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul,
    ← Real.exp_add, ← Real.exp_add]
  congr 1
  push_cast
  ring

/-- Exact real-arithmetic heart of the dense raw estimate.  The right side
is twice the target, leaving genuine slack after the natural ceilings. -/
theorem denseRaw_scalar_algebra
    {E r β L B : ℝ} {i : ℕ}
    (hr : 0 < r) (hβ : 0 < β) (hL : 0 < L) (hB : 0 < B) :
    (60 * E / (Real.rpow β (9 / 10 : ℝ) * r) *
        (Real.exp ((i + 1 : ℕ) : ℝ) *
          Real.rpow (1 / β) (1 / 10 : ℝ))) * 2 =
      ((Real.exp (-1) ^ (i + 1) * E / 3) *
          (L /
            (120 * (β * r * L * approxRegularRatio ^ i) * B))) *
        (2 * Real.exp 2 * 360 * 60 * B) := by
  have hleft :
      60 * E / (Real.rpow β (9 / 10 : ℝ) * r) *
          (Real.exp ((i + 1 : ℕ) : ℝ) *
            Real.rpow (1 / β) (1 / 10 : ℝ)) * 2 =
        120 * E * Real.exp ((i + 1 : ℕ) : ℝ) / (β * r) := by
    calc
      60 * E / (Real.rpow β (9 / 10 : ℝ) * r) *
          (Real.exp ((i + 1 : ℕ) : ℝ) *
            Real.rpow (1 / β) (1 / 10 : ℝ)) * 2 =
          (120 * E * Real.exp ((i + 1 : ℕ) : ℝ) / r) *
            (Real.rpow (1 / β) (1 / 10 : ℝ) /
              Real.rpow β (9 / 10 : ℝ)) := by ring
      _ = (120 * E * Real.exp ((i + 1 : ℕ) : ℝ) / r) *
          (1 / β) := by rw [denseBetaRpow_balance hβ]
      _ = 120 * E * Real.exp ((i + 1 : ℕ) : ℝ) / (β * r) := by ring
  have hrne : r ≠ 0 := ne_of_gt hr
  have hβne : β ≠ 0 := ne_of_gt hβ
  have hLne : L ≠ 0 := ne_of_gt hL
  have hBne : B ≠ 0 := ne_of_gt hB
  have hane : approxRegularRatio ^ i ≠ 0 :=
    ne_of_gt (pow_pos approxRegularRatio_pos _)
  have hright :
      ((Real.exp (-1) ^ (i + 1) * E / 3) *
          (L /
            (120 * (β * r * L * approxRegularRatio ^ i) * B))) *
          (2 * Real.exp 2 * 360 * 60 * B) =
        120 * E * Real.exp ((i + 1 : ℕ) : ℝ) / (β * r) := by
    calc
      ((Real.exp (-1) ^ (i + 1) * E / 3) *
          (L /
            (120 * (β * r * L * approxRegularRatio ^ i) * B))) *
          (2 * Real.exp 2 * 360 * 60 * B) =
          120 * E * (Real.exp (-1) ^ (i + 1) * Real.exp 2) /
            (β * r * approxRegularRatio ^ i) := by
        field_simp [hrne, hβne, hLne, hBne, hane]
        <;> ring
      _ = 120 * E *
          (Real.exp ((i + 1 : ℕ) : ℝ) * approxRegularRatio ^ i) /
            (β * r * approxRegularRatio ^ i) := by
        rw [denseExpScale_balance i]
      _ = 120 * E * Real.exp ((i + 1 : ℕ) : ℝ) / (β * r) := by
        field_simp [hrne, hβne, hane]
        <;> ring
  exact hleft.trans hright.symm

/-- Complete dense raw interface at fixed parameters.  Its only two
graph-independent side conditions are eventual growth comparisons in `r`.
-/
theorem keyLemmaDenseRawWeightBound_of_keyLemma_hypotheses
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {D r n : ℕ} {β : ℝ}
    (hr : 21 ≤ r)
    (hn : 100 * Real.log (r : ℝ) ≤ (n : ℝ))
    (hβ : 0 < β) (hβOne : β ≤ 1)
    (hmax : (D : ℝ) = β * r * Real.log (r : ℝ))
    (hedgeLower : Real.rpow (r : ℝ) (7 / 4 : ℝ) * n ≤
      (edgeCount G : ℝ))
    (hedgeUpper : (edgeCount G : ℝ) ≤
      (r : ℝ) ^ 2 * Real.log (r : ℝ) * n)
    (hdegreeGrowth : 3 * ((r : ℝ) * Real.log (r : ℝ)) ≤
      Real.rpow (r : ℝ) (7 / 4 : ℝ))
    (hreferenceGrowth :
      16 * Real.exp 2 * Real.log (r : ℝ) ≤ (r : ℝ) ^ 2) :
    KeyLemmaDenseRawWeightBound G D r n β
      (keyLemmaAssemblyTarget G r β) := by
  have hlogpos : 0 < Real.log (r : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < r by omega))
  have hnrealpos : (0 : ℝ) < n :=
    (show (0 : ℝ) < 100 * Real.log (r : ℝ) by positivity).trans_le hn
  have hnpos : 0 < n := by exact_mod_cast hnrealpos
  have hrrealpos : (0 : ℝ) < r := by positivity
  intro i hi hmass hcountLower hcountUpper
  let B : ℝ := 4 * ((i + 1 : ℕ) : ℝ) + Real.log (5 / β ^ 2)
  let W : ℝ := ballsBinsWeight
    (subgraphFindingBinCount n
      (peelingBand G (approxRegularThreshold D) (i + 1)).card)
    (keyLemmaLayerDegreeCap D i)
  have hBpos : 0 < B := by
    dsimp only [B]
    exact denseLogBracket_pos hβ hβOne
  have hscalar :
      Real.log (r : ℝ) /
          (120 * approxRegularScale D i * B) ≤ W := by
    simpa only [B, W] using
      keyLemmaDenseWeight_scalar_lower_bound G hr hnpos hβ hβOne
        hmax hedgeLower hedgeUpper hdegreeGrowth hreferenceGrowth hi hmass
        hcountLower hcountUpper
  have hscale : approxRegularScale D i =
      β * (r : ℝ) * Real.log (r : ℝ) * approxRegularRatio ^ i := by
    rw [approxRegularScale, hmax]
  have hmassNonneg :
      0 ≤ Real.exp (-1) ^ (i + 1) * (edgeCount G : ℝ) / 3 := by
    positivity
  have hdenNonneg :
      0 ≤ 2 * Real.exp 2 * 360 * 60 * B := by positivity
  have hweighted :
      (Real.exp (-1) ^ (i + 1) * (edgeCount G : ℝ) / 3 *
          (Real.log (r : ℝ) /
            (120 * approxRegularScale D i * B))) *
          (2 * Real.exp 2 * 360 * 60 * B) ≤
        (Real.exp (-1) ^ (i + 1) * (edgeCount G : ℝ) / 3 * W) *
          (2 * Real.exp 2 * 360 * 60 * B) := by
    apply mul_le_mul_of_nonneg_right _ hdenNonneg
    exact mul_le_mul_of_nonneg_left hscalar hmassNonneg
  have hlhsNonneg :
      0 ≤ keyLemmaAssemblyTarget G r β *
        keyLemmaDenseNumerator β (i + 1) := by
    apply mul_nonneg
    · exact keyLemmaAssemblyTarget_nonneg G r hβ (by omega)
    · unfold keyLemmaDenseNumerator
      positivity
  have halgebra := denseRaw_scalar_algebra
    (E := (edgeCount G : ℝ)) (r := (r : ℝ)) (β := β)
    (L := Real.log (r : ℝ)) (B := B) (i := i)
    hrrealpos hβ hlogpos hBpos
  calc
    keyLemmaAssemblyTarget G r β *
        keyLemmaDenseNumerator β (i + 1) ≤
      (keyLemmaAssemblyTarget G r β *
        keyLemmaDenseNumerator β (i + 1)) * 2 := by nlinarith
    _ = (Real.exp (-1) ^ (i + 1) * (edgeCount G : ℝ) / 3 *
          (Real.log (r : ℝ) /
            (120 * approxRegularScale D i * B))) *
        (2 * Real.exp 2 * 360 * 60 * B) := by
      simpa only [keyLemmaAssemblyTarget, keyLemmaDenseNumerator, hscale,
        Real.rpow_eq_pow]
        using halgebra
    _ ≤ (Real.exp (-1) ^ (i + 1) * (edgeCount G : ℝ) / 3 * W) *
        (2 * Real.exp 2 * 360 * 60 * B) := hweighted
    _ = (Real.exp (-1) ^ (i + 1) * (edgeCount G : ℝ) / 3 *
          ballsBinsWeight
            (subgraphFindingBinCount n
              (peelingBand G (approxRegularThreshold D) (i + 1)).card)
            (keyLemmaLayerDegreeCap D i)) *
        keyLemmaDenseDenominator β (i + 1) := by
      simp only [W, B, keyLemmaDenseDenominator, keyLemmaDenseConstant]

/-! ## Uniform eventual closure -/

/-- Eventually the degree comparison used by the dense nondegeneracy
argument holds with its required factor three. -/
theorem exists_keyLemma_three_degree_growth_threshold :
    ∃ r₀ : ℕ, ∀ r : ℕ, r₀ ≤ r →
      3 * ((r : ℝ) * Real.log (r : ℝ)) ≤
        Real.rpow (r : ℝ) (7 / 4 : ℝ) := by
  have htend :
      Tendsto
        (fun r : ℕ ↦
          Real.rpow (r : ℝ) (3 / 4 : ℝ) / Real.log (r : ℝ))
        atTop atTop :=
    (tendsto_rpow_div_log_atTop
      (show (0 : ℝ) < 3 / 4 by norm_num)).comp
        tendsto_natCast_atTop_atTop
  have heventRatio : ∀ᶠ r : ℕ in atTop,
      (3 : ℝ) ≤
        Real.rpow (r : ℝ) (3 / 4 : ℝ) / Real.log (r : ℝ) :=
    htend.eventually (eventually_ge_atTop 3)
  have heventTwo : ∀ᶠ r : ℕ in atTop, 2 ≤ r := eventually_ge_atTop 2
  obtain ⟨r₀, hr₀⟩ := eventually_atTop.1 (heventRatio.and heventTwo)
  refine ⟨r₀, ?_⟩
  intro r hr
  obtain ⟨hratio, hrTwo⟩ := hr₀ r hr
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hlogpos : 0 < Real.log (r : ℝ) :=
    Real.log_pos (by exact_mod_cast hrTwo)
  have hlogpow : 3 * Real.log (r : ℝ) ≤
      Real.rpow (r : ℝ) (3 / 4 : ℝ) := by
    exact (le_div_iff₀ hlogpos).1 hratio
  calc
    3 * ((r : ℝ) * Real.log (r : ℝ)) =
        (r : ℝ) * (3 * Real.log (r : ℝ)) := by ring
    _ ≤ (r : ℝ) * Real.rpow (r : ℝ) (3 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_left hlogpow hrpos.le
    _ = Real.rpow (r : ℝ) (7 / 4 : ℝ) := by
      change (r : ℝ) * (r : ℝ) ^ (3 / 4 : ℝ) =
        (r : ℝ) ^ (7 / 4 : ℝ)
      rw [show (7 / 4 : ℝ) = 1 + 3 / 4 by norm_num,
        Real.rpow_add hrpos, Real.rpow_one]

/-- Eventually the dense bin reference is at most `r³`; this is the sole
extra growth estimate used by its logarithmic denominator bound. -/
theorem exists_keyLemma_dense_reference_growth_threshold :
    ∃ r₀ : ℕ, ∀ r : ℕ, r₀ ≤ r →
      16 * Real.exp 2 * Real.log (r : ℝ) ≤ (r : ℝ) ^ 2 := by
  have htend :
      Tendsto
        (fun r : ℕ ↦
          Real.rpow (r : ℝ) (2 : ℝ) / Real.log (r : ℝ))
        atTop atTop :=
    (tendsto_rpow_div_log_atTop (show (0 : ℝ) < 2 by norm_num)).comp
      tendsto_natCast_atTop_atTop
  have heventRatio : ∀ᶠ r : ℕ in atTop,
      16 * Real.exp 2 ≤
        Real.rpow (r : ℝ) (2 : ℝ) / Real.log (r : ℝ) :=
    htend.eventually (eventually_ge_atTop (16 * Real.exp 2))
  have heventTwo : ∀ᶠ r : ℕ in atTop, 2 ≤ r := eventually_ge_atTop 2
  obtain ⟨r₀, hr₀⟩ := eventually_atTop.1 (heventRatio.and heventTwo)
  refine ⟨r₀, ?_⟩
  intro r hr
  obtain ⟨hratio, hrTwo⟩ := hr₀ r hr
  have hlogpos : 0 < Real.log (r : ℝ) :=
    Real.log_pos (by exact_mod_cast hrTwo)
  have hcross : 16 * Real.exp 2 * Real.log (r : ℝ) ≤
      Real.rpow (r : ℝ) (2 : ℝ) :=
    (le_div_iff₀ hlogpos).1 hratio
  simpa only [Real.rpow_eq_pow, Real.rpow_two] using hcross

/-- Graph-uniform eventual closure of the complete dense raw interface. -/
theorem exists_keyLemmaDenseRawWeightBound_eventually :
    ∃ r₀ : ℕ, ∀ r : ℕ, r₀ ≤ r →
      ∀ n : ℕ, 100 * Real.log (r : ℝ) ≤ (n : ℝ) →
        ∀ N : ℕ, ∀ G : SimpleGraph (Fin N), ∀ β : ℝ,
          (7 * Real.log (r : ℝ))⁻¹ ≤ β →
          β ≤ keyLemmaGlobalBeta0 →
          ((@SimpleGraph.maxDegree (Fin N) G inferInstance
              (Classical.decRel _)) : ℝ) =
            β * r * Real.log (r : ℝ) →
          Real.rpow (r : ℝ) (7 / 4 : ℝ) * n ≤
            (edgeCount G : ℝ) →
          (edgeCount G : ℝ) ≤
            (r : ℝ) ^ 2 * Real.log (r : ℝ) * n →
          KeyLemmaDenseRawWeightBound G
            (@SimpleGraph.maxDegree (Fin N) G inferInstance
              (Classical.decRel _)) r n β
            (keyLemmaAssemblyTarget G r β) := by
  obtain ⟨rDegree, hDegree⟩ :=
    exists_keyLemma_three_degree_growth_threshold
  obtain ⟨rReference, hReference⟩ :=
    exists_keyLemma_dense_reference_growth_threshold
  refine ⟨max 21 (max rDegree rReference), ?_⟩
  intro r hrLarge n hn N G β hβLower hβUpper hmax hedgeLower hedgeUpper
  letI : DecidableRel G.Adj := Classical.decRel _
  have hr : 21 ≤ r :=
    (le_max_left 21 (max rDegree rReference)).trans hrLarge
  have hrDegree : rDegree ≤ r :=
    (le_max_left rDegree rReference).trans
      ((le_max_right 21 (max rDegree rReference)).trans hrLarge)
  have hrReference : rReference ≤ r :=
    (le_max_right rDegree rReference).trans
      ((le_max_right 21 (max rDegree rReference)).trans hrLarge)
  have hlogpos : 0 < Real.log (r : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < r by omega))
  have hβpos : 0 < β := by
    exact (inv_pos.mpr (mul_pos (by norm_num) hlogpos)).trans_le hβLower
  have hβOne : β ≤ 1 := hβUpper.trans keyLemmaGlobalBeta0_mem.2
  exact keyLemmaDenseRawWeightBound_of_keyLemma_hypotheses G hr hn
    hβpos hβOne hmax hedgeLower hedgeUpper (hDegree r hrDegree)
      (hReference r hrReference)

end

end LeanCo.SizeRamsey
