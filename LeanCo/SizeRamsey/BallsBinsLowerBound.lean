import LeanCo.SizeRamsey.BallsBinsNegativeAssociation
import LeanCo.SizeRamsey.BallsBinsQMonotone

/-!
# Explicit lower bounds for the balls-and-bins weight

This file supplies the analytic occupancy estimate used in the path
size--Ramsey lower bound.  All probability statements remain literal finite
averages; the only inputs are the negative-association and monotonicity
modules built over `PathLowerBound`.
-/

namespace LeanCo.SizeRamsey

open Finset Function

noncomputable section

/-- If the expected number of bins reaching `t` is at least one, negative
association makes the maximum reach `t` with probability at least `1/2`.
This is the finite point at which the second-moment argument becomes a
usable numerical bound. -/
theorem half_threshold_le_expectedMaxBinLoad_of_mass
    {q d t : ℕ} (hq : 2 ≤ q) (i : Fin q)
    (hmass : Fintype.card (Fin d → Fin q) ≤
      q * (binLoadAtLeastEvent (d := d) i t).card) :
    (t : ℝ) / 2 ≤ expectedMaxBinLoad q d := by
  let A : ℝ := (binLoadAtLeastEvent (d := d) i t).card
  let N : ℝ := Fintype.card (Fin d → Fin q)
  let S : ℝ := q * A + q * (q - 1) * (A ^ 2 / N)
  have hN : 0 < N := by
    dsimp only [N]
    have : Nonempty (Fin d → Fin q) := ⟨fun _ ↦ i⟩
    exact_mod_cast Fintype.card_pos
  have hmassR : N ≤ (q : ℝ) * A := by
    dsimp only [N, A]
    exact_mod_cast hmass
  have hA : 0 < A := by
    have hqR : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
    nlinarith
  have hfixed : 0 <
      ((binLoadAtLeastEvent (d := d) i t).card : ℝ) := by
    exact hA
  have hraw := expectedMaxBinLoad_lower_bound_of_negative_association
    hq i hfixed
  dsimp only at hraw
  have hqR : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hqm1 : (q : ℝ) - 1 ≤ q := by linarith
  have hqm1pos : (0 : ℝ) < (q : ℝ) - 1 := by
    have hq2R : (2 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hden : 0 < N + ((q : ℝ) - 1) * A := by positivity
  have hfrac : (1 : ℝ) / 2 ≤
      ((q : ℝ) * A) /
        (N + ((q : ℝ) - 1) * A) := by
    apply (le_div_iff₀ hden).2
    have hsubmul : ((q : ℝ) - 1) * A ≤ q * A :=
      mul_le_mul_of_nonneg_right hqm1 hA.le
    nlinarith
  have hSform :
      N * S = ((q : ℝ) * A) *
        (N + ((q : ℝ) - 1) * A) := by
    dsimp only [S]
    field_simp [ne_of_gt hN]
  have hsimplify :
      (((q : ℝ) * A) ^ 2 / (N * S)) =
        ((q : ℝ) * A) /
          (N + ((q : ℝ) - 1) * A) := by
    rw [hSform, pow_two]
    field_simp [ne_of_gt hqR, ne_of_gt hA, ne_of_gt hden]
  have hmul := mul_le_mul_of_nonneg_left hfrac (by positivity : (0 : ℝ) ≤ t)
  rw [hsimplify] at hraw
  calc
    (t : ℝ) / 2 = (t : ℝ) * ((1 : ℝ) / 2) := by ring
    _ ≤ (t : ℝ) *
        (((q : ℝ) * A) /
          (N + ((q : ℝ) - 1) * A)) := hmul
    _ ≤ expectedMaxBinLoad q d := by
      simpa only [A, N, S] using hraw

/-- Normalised version of `half_threshold_le_expectedMaxBinLoad_of_mass`. -/
theorem threshold_div_two_balls_le_ballsBinsWeight_of_mass
    {q d t : ℕ} (hq : 2 ≤ q) (hd : 0 < d) (i : Fin q)
    (hmass : Fintype.card (Fin d → Fin q) ≤
      q * (binLoadAtLeastEvent (d := d) i t).card) :
    (t : ℝ) / (2 * d) ≤ ballsBinsWeight q d := by
  rw [ballsBinsWeight]
  have h := half_threshold_le_expectedMaxBinLoad_of_mass hq i hmass
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  calc
    (t : ℝ) / (2 * d) = ((t : ℝ) / 2) / d := by ring
    _ ≤ expectedMaxBinLoad q d / d :=
      div_le_div_of_nonneg_right h hdR.le

/-- In the dense regime `q*t ≤ d`, every allocation has a bin of load at
least `t`; summing over the symmetric bins gives the mass condition needed
by the second-moment bridge. -/
theorem allocation_card_le_mul_tail_card_of_mul_threshold_le
    {q d t : ℕ} (hq : 0 < q) (i : Fin q) (hqt : q * t ≤ d) :
    Fintype.card (Fin d → Fin q) ≤
      q * (binLoadAtLeastEvent (d := d) i t).card := by
  have hpoint : ∀ f : Fin d → Fin q, 1 ≤ heavyBinCount f t := by
    intro f
    by_contra hzero
    have hcountZero : heavyBinCount f t = 0 := by omega
    have hall : ∀ j : Fin q, binLoad f j < t := by
      intro j
      by_contra hj
      have hjmem : j ∈
          (Finset.univ.filter fun k : Fin q ↦ t ≤ binLoad f k) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      have : 0 < heavyBinCount f t :=
        Finset.card_pos.mpr ⟨j, hjmem⟩
      omega
    have ht : 0 < t := by
      have h0 := hall (⟨0, hq⟩ : Fin q)
      omega
    have hsumle : ∑ j : Fin q, binLoad f j ≤
        ∑ _j : Fin q, (t - 1) := by
      apply Finset.sum_le_sum
      intro j _hj
      have := hall j
      omega
    have hsumlt : ∑ j : Fin q, binLoad f j < q * t := by
      calc
        ∑ j : Fin q, binLoad f j ≤ ∑ _j : Fin q, (t - 1) := hsumle
        _ = q * (t - 1) := by simp
        _ < q * t := Nat.mul_lt_mul_of_pos_left (by omega) hq
    rw [sum_binLoad] at hsumlt
    omega
  calc
    Fintype.card (Fin d → Fin q) = ∑ _f : Fin d → Fin q, 1 := by simp
    _ ≤ ∑ f : Fin d → Fin q, heavyBinCount f t :=
      Finset.sum_le_sum fun f _ ↦ hpoint f
    _ = q * (binLoadAtLeastEvent (d := d) i t).card :=
      sum_heavyBinCount_eq_mul_fixed i

/-- The exact point mass at load `t` is contained in the upper tail. -/
theorem mul_choose_pow_le_mul_tail_card {q d t : ℕ}
    (i : Fin q) :
    q * (Nat.choose d t * (q - 1) ^ (d - t)) ≤
      q * (binLoadAtLeastEvent (d := d) i t).card :=
  Nat.mul_le_mul_left q (choose_mul_pow_le_card_binLoadAtLeastEvent i t)

/-- A point-mass count large enough to cover the allocation space implies
the normalised half-threshold lower bound. -/
theorem threshold_div_two_balls_le_ballsBinsWeight_of_pointMass
    {q d t : ℕ} (hq : 2 ≤ q) (hd : 0 < d) (i : Fin q)
    (hpoint : q ^ d ≤ q * (Nat.choose d t * (q - 1) ^ (d - t))) :
    (t : ℝ) / (2 * d) ≤ ballsBinsWeight q d := by
  apply threshold_div_two_balls_le_ballsBinsWeight_of_mass hq hd i
  simpa only [Fintype.card_fun, Fintype.card_fin] using
    hpoint.trans (mul_choose_pow_le_mul_tail_card i)

/-! ## Elementary analytic estimates for the explicit threshold -/

/-- For `x ≥ 2`, the logarithm of one failed-bin probability has the
uniform lower bound used below. -/
theorem neg_two_div_le_log_one_sub_inv {x : ℝ} (hx : 2 ≤ x) :
    -2 / x ≤ Real.log (1 - 1 / x) := by
  have hxpos : 0 < x := by linarith
  have hxone : 1 < x := by linarith
  have hxsub : 0 < x - 1 := by linarith
  have hz : 0 < 1 - 1 / x := by
    exact sub_pos.mpr ((div_lt_one hxpos).2 hxone)
  have hlog := Real.one_sub_inv_le_log_of_pos hz
  have hid : 1 - (1 - 1 / x)⁻¹ = -1 / (x - 1) := by
    field_simp [ne_of_gt hxpos, ne_of_gt hxsub]
    ring
  rw [hid] at hlog
  have hfrac : 1 / (x - 1) ≤ 2 / x := by
    apply (div_le_div_iff₀ hxsub hxpos).2
    nlinarith
  calc
    -2 / x = -(2 / x) := by ring
    _ ≤ -(1 / (x - 1)) := neg_le_neg hfrac
    _ = -1 / (x - 1) := by ring
    _ ≤ Real.log (1 - 1 / x) := hlog

/-- Exponentiated form of `neg_two_div_le_log_one_sub_inv`. -/
theorem exp_neg_two_mul_div_le_one_sub_inv_pow
    {x : ℝ} (hx : 2 ≤ x) (d : ℕ) :
    Real.exp (-2 * d / x) ≤ (1 - 1 / x) ^ d := by
  have hxpos : 0 < x := by linarith
  have hxone : 1 < x := by linarith
  have hz : 0 < 1 - 1 / x :=
    sub_pos.mpr ((div_lt_one hxpos).2 hxone)
  have hlog := neg_two_div_le_log_one_sub_inv hx
  have hmul := mul_le_mul_of_nonneg_left hlog
    (show (0 : ℝ) ≤ d by positivity)
  calc
    Real.exp (-2 * d / x) = Real.exp ((d : ℝ) * (-2 / x)) := by
      congr 1
      ring
    _ ≤ Real.exp ((d : ℝ) * Real.log (1 - 1 / x)) :=
      Real.exp_le_exp.mpr hmul
    _ = Real.exp (Real.log ((1 - 1 / x) ^ d)) := by
      rw [Real.log_pow]
    _ = (1 - 1 / x) ^ d := Real.exp_log (pow_pos hz d)

/-- A deliberately elementary lower bound on a binomial coefficient.  The
factor `2` leaves enough slack to avoid an upper Stirling estimate. -/
theorem div_two_mul_pow_le_choose {d t : ℕ}
    (ht : 0 < t) (h2t : 2 * t ≤ d) :
    (((d : ℝ) / (2 * t)) ^ t) ≤ (Nat.choose d t : ℝ) := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hbaseNat : d ≤ 2 * (d + 1 - t) := by omega
  have hbase : (d : ℝ) / 2 ≤ (d + 1 - t : ℕ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    exact_mod_cast (by simpa [mul_comm] using hbaseNat)
  have hpowbase : ((d : ℝ) / 2) ^ t ≤
      ((d + 1 - t : ℕ) : ℝ) ^ t := by
    gcongr
  have hfac : (t.factorial : ℝ) ≤ (t : ℝ) ^ t := by
    exact_mod_cast Nat.factorial_le_pow t
  have hchoose :
      (((d + 1 - t : ℕ) : ℝ) ^ t) / (t.factorial : ℝ) ≤
        (Nat.choose d t : ℝ) := Nat.pow_le_choose t d
  calc
    ((d : ℝ) / (2 * t)) ^ t =
        (((d : ℝ) / 2) ^ t) / ((t : ℝ) ^ t) := by
      have hbaseEq : (d : ℝ) / (2 * t) = ((d : ℝ) / 2) / t := by
        field_simp [ne_of_gt htR]
      rw [hbaseEq, div_pow]
    _ ≤ (((d + 1 - t : ℕ) : ℝ) ^ t) / ((t : ℝ) ^ t) :=
      div_le_div_of_nonneg_right hpowbase (by positivity)
    _ ≤ (((d + 1 - t : ℕ) : ℝ) ^ t) / (t.factorial : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hfac
    _ ≤ (Nat.choose d t : ℝ) := hchoose

/-- A logarithmic certificate implying that the exact load-`t` point mass
has total expected bin count at least one.  This packages all combinatorial
and exponential estimates, leaving the final occupancy bound as a purely
one-variable choice of `t`. -/
theorem pointMass_of_log_certificate {q d t : ℕ}
    (hq : 2 ≤ q) (ht : 0 < t) (h2t : 2 * t ≤ d)
    (hcert : (t : ℝ) * Real.log (2 * q * t / d) + 2 * d / q ≤
      Real.log q) :
    q ^ d ≤ q * (Nat.choose d t * (q - 1) ^ (d - t)) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hdposNat : 0 < d := by omega
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hdposNat
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  have htd : t ≤ d := by omega
  let r : ℝ := 2 * q * t / d
  have hrpos : 0 < r := by
    dsimp only [r]
    positivity
  have hinv : (d : ℝ) / (2 * q * t) = r⁻¹ := by
    dsimp only [r]
    field_simp
  have hlogform :
      Real.exp (Real.log q - (t : ℝ) * Real.log r - 2 * d / q) =
        (q : ℝ) * ((d : ℝ) / (2 * q * t)) ^ t *
          Real.exp (-2 * d / q) := by
    rw [sub_eq_add_neg (Real.log q - _), sub_eq_add_neg,
      Real.exp_add, Real.exp_add, Real.exp_log hqpos]
    have hpowexp : Real.exp (-((t : ℝ) * Real.log r)) = (r⁻¹) ^ t := by
      rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log hrpos, inv_pow]
    rw [hpowexp, hinv]
    congr 2 <;> ring
  have hcore : (1 : ℝ) ≤
      (q : ℝ) * ((d : ℝ) / (2 * q * t)) ^ t *
        Real.exp (-2 * d / q) := by
    rw [← hlogform, ← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    dsimp only [r]
    linarith
  have hchoose := div_two_mul_pow_le_choose ht h2t
  have hchooseScaled :
      ((d : ℝ) / (2 * q * t)) ^ t ≤
        (Nat.choose d t : ℝ) / (q : ℝ) ^ t := by
    calc
      ((d : ℝ) / (2 * q * t)) ^ t =
          (((d : ℝ) / (2 * t)) ^ t) / (q : ℝ) ^ t := by
        rw [← div_pow]
        congr 1
        field_simp
      _ ≤ (Nat.choose d t : ℝ) / (q : ℝ) ^ t :=
        div_le_div_of_nonneg_right hchoose (by positivity)
  have hfail0 := exp_neg_two_mul_div_le_one_sub_inv_pow
    (show (2 : ℝ) ≤ (q : ℝ) by exact_mod_cast hq) (d - t)
  have hexpmono : Real.exp (-2 * d / q) ≤
      Real.exp (-2 * (d - t : ℕ) / q) := by
    apply Real.exp_le_exp.mpr
    have hsub : (d - t : ℕ) ≤ d := Nat.sub_le d t
    have hsubR : ((d - t : ℕ) : ℝ) ≤ d := by exact_mod_cast hsub
    have hqnonneg : (0 : ℝ) ≤ q := hqpos.le
    apply (div_le_div_iff_of_pos_right hqpos).2
    nlinarith
  have hfail : Real.exp (-2 * d / q) ≤
      (1 - 1 / (q : ℝ)) ^ (d - t) := hexpmono.trans hfail0
  have hqpowpos : 0 < (q : ℝ) ^ t := pow_pos hqpos t
  have hscaled : (1 : ℝ) ≤
      (q : ℝ) * ((Nat.choose d t : ℝ) / (q : ℝ) ^ t) *
        (1 - 1 / (q : ℝ)) ^ (d - t) := by
    calc
      (1 : ℝ) ≤ (q : ℝ) * ((d : ℝ) / (2 * q * t)) ^ t *
          Real.exp (-2 * d / q) := hcore
      _ ≤ (q : ℝ) * ((Nat.choose d t : ℝ) / (q : ℝ) ^ t) *
          Real.exp (-2 * d / q) := by
        gcongr
      _ ≤ (q : ℝ) * ((Nat.choose d t : ℝ) / (q : ℝ) ^ t) *
          (1 - 1 / (q : ℝ)) ^ (d - t) := by
        gcongr
  have hreal : ((q : ℝ) ^ d) ≤
      (q : ℝ) * (Nat.choose d t : ℝ) *
        (((q - 1 : ℕ) : ℝ) ^ (d - t)) := by
    have hqsub : (((q - 1 : ℕ) : ℝ)) = (q : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ q)]
      norm_num
    have hbase : (q : ℝ) - 1 =
        (q : ℝ) * (1 - 1 / (q : ℝ)) := by
      field_simp
    have hpowdecomp :
        (((q - 1 : ℕ) : ℝ) ^ (d - t)) =
          (q : ℝ) ^ (d - t) *
            (1 - 1 / (q : ℝ)) ^ (d - t) := by
      rw [hqsub, hbase, mul_pow]
    rw [hpowdecomp]
    have hpowadd : (q : ℝ) ^ d =
        (q : ℝ) ^ t * (q : ℝ) ^ (d - t) := by
      rw [← pow_add, Nat.add_sub_of_le htd]
    rw [hpowadd]
    rw [show (q : ℝ) * (Nat.choose d t : ℝ) *
        ((q : ℝ) ^ (d - t) * (1 - 1 / (q : ℝ)) ^ (d - t)) =
      ((q : ℝ) * (Nat.choose d t : ℝ) *
        (1 - 1 / (q : ℝ)) ^ (d - t)) * (q : ℝ) ^ (d - t) by ring]
    apply (mul_le_mul_iff_of_pos_right (pow_pos hqpos (d - t))).2
    calc
      (q : ℝ) ^ t = (q : ℝ) ^ t * 1 := by ring
      _ ≤ (q : ℝ) ^ t *
          ((q : ℝ) * ((Nat.choose d t : ℝ) / (q : ℝ) ^ t) *
            (1 - 1 / (q : ℝ)) ^ (d - t)) :=
        mul_le_mul_of_nonneg_left hscaled (by positivity)
      _ = (q : ℝ) * (Nat.choose d t : ℝ) *
          (1 - 1 / (q : ℝ)) ^ (d - t) := by
        field_simp [ne_of_gt hqpowpos]
  norm_cast at hreal
  simpa [mul_assoc] using hreal

/-! ## The explicit Appendix A.10 scale -/

/-- The elementary lower tangent estimate for `log (1 + c)`. -/
theorem div_one_add_le_log_one_add {c : ℝ} (hc : 0 ≤ c) :
    c / (1 + c) ≤ Real.log (1 + c) := by
  have hpos : 0 < 1 + c := by linarith
  have h := Real.one_sub_inv_le_log_of_pos hpos
  calc
    c / (1 + c) = 1 - (1 + c)⁻¹ := by
      field_simp [ne_of_gt hpos]
      ring
    _ ≤ Real.log (1 + c) := h

/-- The real threshold whose natural floor is used in the point-mass
argument. -/
def ballsBinsExplicitThreshold (q d : ℕ) : ℝ :=
  Real.log (q : ℝ) /
    (20 * Real.log (1 + (q : ℝ) * Real.log q / (2 * d)))

theorem ballsBinsExplicitThreshold_nonneg {q d : ℕ}
    (hq : 2 ≤ q) (hd : 0 < d) :
    0 ≤ ballsBinsExplicitThreshold q d := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hlogpos : 0 < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast hq)
  have hcpos : 0 < (q : ℝ) * Real.log q / (2 * d) := by positivity
  have hellpos : 0 < Real.log (1 + (q : ℝ) * Real.log q / (2 * d)) :=
    Real.log_pos (by linarith)
  exact (div_nonneg hlogpos.le (by positivity))

/-- Rewriting the target in terms of the explicit threshold. -/
theorem explicit_target_eq_threshold_div_six {q d : ℕ} :
    Real.log (q : ℝ) /
        (120 * d * Real.log (1 + (q : ℝ) * Real.log q / (2 * d))) =
      ballsBinsExplicitThreshold q d / (6 * d) := by
  unfold ballsBinsExplicitThreshold
  ring

/-- In the only nontrivial range (threshold bigger than the elementary
`1/d` bound), the chosen load is far below `d/2`. -/
theorem ballsBinsExplicitThreshold_lt_three_div_twenty_balls
    {q d : ℕ} (hq : 2 ≤ q) (hd : 0 < d)
    (hy : 6 < ballsBinsExplicitThreshold q d) :
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
  have hy' : 6 < L / (20 * ell) := by
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
        L / (20 * ell) ≤ L / (20 * L) := by
          exact div_le_div_of_nonneg_left hLpos.le (by positivity)
            (mul_le_mul_of_nonneg_left hlog (by norm_num))
        _ = (1 : ℝ) / 20 := by field_simp [ne_of_gt hLpos]
    linarith
  have hellLower : c / (1 + c) ≤ ell := by
    simpa only [ell] using div_one_add_le_log_one_add hcpos.le
  have hrough : L / (20 * ell) ≤ L / (20 * (c / (1 + c))) := by
    exact div_le_div_of_nonneg_left hLpos.le (by positivity)
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

/-- In the sparse regime, every integer load below the explicit threshold
satisfies the logarithmic point-mass certificate. -/
theorem log_certificate_of_le_explicitThreshold
    {q d t : ℕ} (hq : 2 ≤ q) (hd : 0 < d)
    (ht : (t : ℝ) ≤ ballsBinsExplicitThreshold q d)
    (hsparse : d < q * t) :
    (t : ℝ) * Real.log (2 * q * t / d) + 2 * d / q ≤
      Real.log q := by
  let L : ℝ := Real.log (q : ℝ)
  let c : ℝ := (q : ℝ) * L / (2 * d)
  let ell : ℝ := Real.log (1 + c)
  let y : ℝ := L / (20 * ell)
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
  have ht' : (t : ℝ) ≤ y := by
    simpa only [ballsBinsExplicitThreshold, L, c, ell, y] using ht
  have hsparseR : (d : ℝ) / q < t := by
    apply (div_lt_iff₀ hqpos).2
    exact_mod_cast (by simpa [mul_comm] using hsparse)
  have hmu : (d : ℝ) / q < L / (20 * ell) :=
    hsparseR.trans_le ht'
  have hcTen : 10 * ell < c := by
    dsimp only [c]
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * (d : ℝ))).2
    have hcross :=
      (div_lt_div_iff₀ hqpos (by positivity : (0 : ℝ) < 20 * ell)).1 hmu
    nlinarith
  have hellLower : c / (1 + c) ≤ ell := by
    simpa only [ell] using div_one_add_le_log_one_add hcpos.le
  have honeAddTen : 10 < 1 + c := by
    have hfrac : 10 * (c / (1 + c)) < c :=
      (mul_le_mul_of_nonneg_left hellLower (by norm_num)).trans_lt hcTen
    have hfrac' : 10 * c / (1 + c) < c := by
      convert hfrac using 1 <;> ring
    have hmul : 10 * c < c * (1 + c) :=
      (div_lt_iff₀ (by linarith : 0 < 1 + c)).1 hfrac'
    have := (mul_lt_mul_iff_of_pos_right hcpos).1
      (show 10 * c < (1 + c) * c by nlinarith)
    exact this
  have hellOne : 1 < ell := by
    dsimp only [ell]
    apply (Real.lt_log_iff_exp_lt (by linarith : 0 < 1 + c)).2
    exact Real.exp_one_lt_three.trans (by linarith)
  let r : ℝ := 2 * q * t / d
  have hrpos : 0 < r := by
    dsimp only [r]
    have htpos : 0 < t := by
      by_contra hzero
      have : t = 0 := by omega
      simp [this] at hsparse
    positivity
  have hrTwo : 2 < r := by
    dsimp only [r]
    apply (lt_div_iff₀ hdpos).2
    have hsparseCast : (d : ℝ) < q * t := by exact_mod_cast hsparse
    nlinarith
  have hrUpper : r ≤ c / (5 * ell) := by
    calc
      r ≤ 2 * (q : ℝ) * y / d := by
        dsimp only [r]
        gcongr
      _ = c / (5 * ell) := by
        dsimp only [y, c]
        field_simp [ne_of_gt hdpos, ne_of_gt hellpos]
        ring
  have hcEll : c ≤ ell * (1 + c) :=
    (div_le_iff₀ (by linarith : 0 < 1 + c)).1 hellLower
  have hcFrac : c / (5 * ell) ≤ 1 + c := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 5 * ell)).2
    calc
      c ≤ ell * (1 + c) := hcEll
      _ ≤ (1 + c) * (5 * ell) := by
        have hcOne : 0 ≤ 1 + c := by positivity
        nlinarith [mul_nonneg hcOne hellpos.le]
  have hrOneAdd : r ≤ 1 + c := hrUpper.trans hcFrac
  have hlogrpos : 0 < Real.log r := Real.log_pos (by linarith)
  have hlogr : Real.log r ≤ ell := by
    dsimp only [ell]
    exact Real.log_le_log hrpos hrOneAdd
  have hterm : (t : ℝ) * Real.log r ≤ L / 20 := by
    calc
      (t : ℝ) * Real.log r ≤ y * ell :=
        mul_le_mul ht' hlogr hlogrpos.le
          (by exact (show 0 ≤ y from le_trans (Nat.cast_nonneg t) ht'))
      _ = L / 20 := by
        dsimp only [y]
        field_simp [ne_of_gt hellpos]
  have hmuSmall : (d : ℝ) / q < L / 20 := by
    calc
      (d : ℝ) / q < L / (20 * ell) := hmu
      _ < L / 20 := by
        apply (div_lt_div_iff₀ (by positivity : (0 : ℝ) < 20 * ell)
          (by norm_num : (0 : ℝ) < 20)).2
        nlinarith
  have hremaining : 2 * (d : ℝ) / q < L / 10 := by
    have : 2 * ((d : ℝ) / q) < 2 * (L / 20) := by linarith
    convert this using 1 <;> ring
  have hcert' : (t : ℝ) * Real.log r + 2 * d / q ≤ L := by
    have : (t : ℝ) * Real.log r + 2 * d / q < 3 * L / 20 := by
      linarith
    linarith
  simpa only [r, L] using hcert'

/-- Natural-parameter specialization of Appendix Lemma A.10, before
monotonic transfer.  The constant `120` is exactly the paper-facing one. -/
theorem ballsBinsWeight_lower_bound_same_parameters
    {q d : ℕ} (hq : 2 ≤ q) (hd : 0 < d) :
    Real.log (q : ℝ) /
        (120 * d * Real.log (1 + (q : ℝ) * Real.log q / (2 * d))) ≤
      ballsBinsWeight q d := by
  rw [explicit_target_eq_threshold_div_six]
  let y : ℝ := ballsBinsExplicitThreshold q d
  have hyNonneg : 0 ≤ y := ballsBinsExplicitThreshold_nonneg hq hd
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  by_cases hySmall : y ≤ 6
  · calc
      y / (6 * d) ≤ (6 : ℝ) / (6 * d) :=
        div_le_div_of_nonneg_right hySmall (by positivity)
      _ = (1 : ℝ) / d := by field_simp
      _ ≤ ballsBinsWeight q d :=
        one_div_balls_le_ballsBinsWeight (by omega) hd
  · have hyLarge : 6 < y := lt_of_not_ge hySmall
    let t : ℕ := ⌊y⌋₊
    have htLe : (t : ℝ) ≤ y := by
      dsimp only [t]
      exact Nat.floor_le hyNonneg
    have htSix : 6 ≤ t := by
      dsimp only [t]
      exact Nat.le_floor hyLarge.le
    have htpos : 0 < t := by omega
    have hyThree : y ≤ 3 * (t : ℝ) := by
      have hfloor := Nat.lt_floor_add_one y
      have htCast : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
      calc
        y ≤ (t : ℝ) + 1 := hfloor.le
        _ ≤ 3 * (t : ℝ) := by nlinarith
    have hyBall := ballsBinsExplicitThreshold_lt_three_div_twenty_balls
      hq hd hyLarge
    have htHalfNat : 2 * t ≤ d := by
      have htReal : 2 * (t : ℝ) < d := by
        calc
          2 * (t : ℝ) ≤ 2 * y := by linarith
          _ < 2 * (3 * (d : ℝ) / 20) := by linarith
          _ < d := by nlinarith
      exact_mod_cast htReal.le
    have htarget : y / (6 * d) ≤ (t : ℝ) / (2 * d) := by
      apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 6 * d)
        (by positivity : (0 : ℝ) < 2 * d)).2
      nlinarith
    let i : Fin q := ⟨0, by omega⟩
    have hthreshold : (t : ℝ) / (2 * d) ≤ ballsBinsWeight q d := by
      by_cases hdense : q * t ≤ d
      · apply threshold_div_two_balls_le_ballsBinsWeight_of_mass hq hd i
        exact allocation_card_le_mul_tail_card_of_mul_threshold_le
          (by omega) i hdense
      · have hsparse : d < q * t := by omega
        have hcert := log_certificate_of_le_explicitThreshold hq hd
          (show (t : ℝ) ≤ ballsBinsExplicitThreshold q d by exact htLe)
          hsparse
        apply threshold_div_two_balls_le_ballsBinsWeight_of_pointMass
          hq hd i
        exact pointMass_of_log_certificate hq htpos htHalfNat hcert
    exact htarget.trans hthreshold

/-- Iterated form of bin-count monotonicity. -/
theorem ballsBinsWeight_antitone_bins_of_le {q Q d : ℕ}
    (hq : 0 < q) (hQ : q ≤ Q) :
    ballsBinsWeight Q d ≤ ballsBinsWeight q d := by
  induction Q, hQ using Nat.le_induction with
  | base => exact le_rfl
  | succ Q hqQ ih =>
      exact (ballsBinsWeight_antitone_bins
        (d := d) (lt_of_lt_of_le hq hqQ)).trans ih

/-- Paper-facing natural specialization of Appendix Lemma A.10.

It allows the actual bin and ball counts to be bounded above by convenient
natural reference parameters `Q,D`, exactly as needed in the Key Lemma.
The v1 constant and formula are preserved literally. -/
theorem ballsBinsWeight_lower_bound_nat
    {q d Q D : ℕ} (hq : 2 ≤ q) (hd : 0 < d)
    (hQ : q ≤ Q) (hD : d ≤ D) :
    Real.log (Q : ℝ) /
        (120 * D * Real.log (1 + (Q : ℝ) * Real.log Q / (2 * D))) ≤
      ballsBinsWeight q d := by
  have hQtwo : 2 ≤ Q := hq.trans hQ
  have hDpos : 0 < D := hd.trans_le hD
  have hsame := ballsBinsWeight_lower_bound_same_parameters hQtwo hDpos
  have hballs : ballsBinsWeight Q D ≤ ballsBinsWeight Q d :=
    ballsBinsWeight_antitone_balls (by omega) hd hD
  have hbins : ballsBinsWeight Q d ≤ ballsBinsWeight q d :=
    ballsBinsWeight_antitone_bins_of_le (by omega) hQ
  exact hsame.trans (hballs.trans hbins)

end

end LeanCo.SizeRamsey
