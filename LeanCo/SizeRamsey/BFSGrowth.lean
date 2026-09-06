import LeanCo.SizeRamsey.BFSLevels
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The first slowly growing BFS ball

This file isolates the stopping-time and exponential-growth arithmetic in
Lemma 2.2.  The graph-theoretic degree estimates are kept for the localisation
module; here the stopping index is constructed literally by `Nat.find`.
-/

namespace LeanCo.SizeRamsey

open Finset SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- At a positive radius `q`, the closed BFS ball grows by a factor at most
two relative to the preceding ball. -/
def IsSlowBall [Fintype V] (G : SimpleGraph V) (root : V) (q : ℕ) : Prop :=
  0 < q ∧ #(closedBallFinset G root q) ≤
    2 * #(closedBallFinset G root (q - 1))

theorem exists_isSlowBall (hG : G.Connected) [Fintype V] (root : V) :
    ∃ q : ℕ, IsSlowBall G root q := by
  classical
  let N := Fintype.card V
  have hBN : closedBallFinset G root N = Finset.univ :=
    closedBallFinset_card_eq_univ hG root
  have hBN1 : closedBallFinset G root (N + 1) = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro v
    rw [mem_closedBallFinset]
    exact (connected_dist_lt_card hG root v).le.trans (Nat.le_add_right N 1)
  have hNpos : 0 < N := by
    dsimp only [N]
    exact Fintype.card_pos_iff.mpr ⟨root⟩
  refine ⟨N + 1, by omega, ?_⟩
  rw [hBN1, show N + 1 - 1 = N by omega, hBN]
  simp only [Finset.card_univ]
  omega

/-- The least positive radius at which the BFS ball grows by at most a
factor of two. -/
noncomputable def firstSlowBall (G : SimpleGraph V) (hG : G.Connected)
    [Fintype V] (root : V) : ℕ := by
  classical
  exact Nat.find (exists_isSlowBall hG root)

theorem firstSlowBall_spec (G : SimpleGraph V) (hG : G.Connected)
    [Fintype V] (root : V) :
    IsSlowBall G root (firstSlowBall G hG root) := by
  classical
  exact Nat.find_spec (exists_isSlowBall hG root)

theorem firstSlowBall_pos (G : SimpleGraph V) (hG : G.Connected)
    [Fintype V] (root : V) :
    0 < firstSlowBall G hG root :=
  (firstSlowBall_spec G hG root).1

/-- Every earlier positive ball grows by a factor strictly greater than two. -/
theorem firstSlowBall_fast_before (G : SimpleGraph V) (hG : G.Connected)
    [Fintype V] (root : V) {j : ℕ} (hjpos : 0 < j)
    (hj : j < firstSlowBall G hG root) :
    2 * #(closedBallFinset G root (j - 1)) <
      #(closedBallFinset G root j) := by
  classical
  by_contra hnot
  have hslow : IsSlowBall G root j :=
    ⟨hjpos, Nat.le_of_not_gt hnot⟩
  have hminimal : firstSlowBall G hG root ≤ j := by
    simpa [firstSlowBall] using
      (Nat.find_min' (exists_isSlowBall hG root) hslow)
  exact (not_lt_of_ge hminimal) hj

theorem card_closedBallFinset_zero (hG : G.Connected) [Fintype V]
    (root : V) : #(closedBallFinset G root 0) = 1 := by
  classical
  rw [closedBallFinset_zero hG root, Finset.card_singleton]

/-- Before the stopping index, the radius-`j` ball contains at least `2^j`
vertices. -/
theorem pow_two_le_card_closedBall_before (G : SimpleGraph V) (hG : G.Connected)
    [Fintype V] (root : V) {j : ℕ}
    (hj : j < firstSlowBall G hG root) :
    2 ^ j ≤ #(closedBallFinset G root j) := by
  induction j with
  | zero =>
      simpa [card_closedBallFinset_zero hG root]
  | succ j ih =>
      have hjprev : j < firstSlowBall G hG root := by omega
      have hfast := firstSlowBall_fast_before G hG root (j := j + 1) (by omega) hj
      have hmul : 2 * 2 ^ j ≤ 2 * #(closedBallFinset G root j) :=
        Nat.mul_le_mul_left 2 (ih hjprev)
      rw [show j + 1 - 1 = j by omega] at hfast
      rw [pow_succ, mul_comm]
      exact hmul.trans hfast.le

/-- If the first ball already grows by more than two, then the stopping
radius is at least two. -/
theorem two_le_firstSlowBall_of_first_growth (G : SimpleGraph V)
    (hG : G.Connected) [Fintype V] (root : V)
    (hfirst : 2 * #(closedBallFinset G root 0) <
      #(closedBallFinset G root 1)) :
    2 ≤ firstSlowBall G hG root := by
  have hpos := firstSlowBall_pos G hG root
  by_contra hnot
  have hqone : firstSlowBall G hG root = 1 := by omega
  have hslow := (firstSlowBall_spec G hG root).2
  rw [hqone, show 1 - 1 = 0 by omega] at hslow
  omega

/-- The exponential growth just before the stopping radius is strict. -/
theorem pow_two_pred_lt_card_closedBall_pred (G : SimpleGraph V)
    (hG : G.Connected) [Fintype V] (root : V)
    (hq : 2 ≤ firstSlowBall G hG root) :
    2 ^ (firstSlowBall G hG root - 1) <
      #(closedBallFinset G root (firstSlowBall G hG root - 1)) := by
  let q := firstSlowBall G hG root
  have hpredlt : q - 1 < q := by omega
  have hfast := firstSlowBall_fast_before G hG root
    (j := q - 1) (by omega) (by omega)
  have hprev : q - 1 - 1 < q := by omega
  have hpowprev := pow_two_le_card_closedBall_before G hG root hprev
  have hmul : 2 * 2 ^ (q - 1 - 1) ≤
      2 * #(closedBallFinset G root (q - 1 - 1)) :=
    Nat.mul_le_mul_left 2 hpowprev
  have hqpred : q - 1 = (q - 1 - 1) + 1 := by omega
  calc
    2 ^ (q - 1) = 2 * 2 ^ (q - 1 - 1) := by
      conv_lhs => rw [hqpred, pow_succ]
      exact Nat.mul_comm _ _
    _ ≤ 2 * #(closedBallFinset G root (q - 1 - 1)) := hmul
    _ < #(closedBallFinset G root (q - 1)) := hfast

/-- Consequently the stopping radius is logarithmic in the number of
vertices, exactly in the real base-two form used in the paper. -/
theorem firstSlowBall_lt_one_add_logb_card (G : SimpleGraph V)
    (hG : G.Connected) [Fintype V] (root : V)
    (hq : 2 ≤ firstSlowBall G hG root) :
    (firstSlowBall G hG root : ℝ) <
      1 + Real.logb 2 (Fintype.card V : ℝ) := by
  have hpowBall := pow_two_pred_lt_card_closedBall_pred G hG root hq
  have hballCard : #(closedBallFinset G root (firstSlowBall G hG root - 1)) ≤
      Fintype.card V := Finset.card_le_univ _
  have hpowNat : 2 ^ (firstSlowBall G hG root - 1) < Fintype.card V :=
    hpowBall.trans_le hballCard
  have hpowReal : ((2 ^ (firstSlowBall G hG root - 1) : ℕ) : ℝ) <
      (Fintype.card V : ℝ) := by exact_mod_cast hpowNat
  rw [Nat.cast_pow, Nat.cast_ofNat] at hpowReal
  have hlog := Real.logb_lt_logb (b := (2 : ℝ))
    (x := (2 : ℝ) ^ (firstSlowBall G hG root - 1))
    (y := (Fintype.card V : ℝ)) (by norm_num)
    (by positivity) hpowReal
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at hlog
  norm_num at hlog
  have hqpos := firstSlowBall_pos G hG root
  norm_num only [Nat.cast_sub hqpos, Nat.cast_one] at hlog
  linarith

end LeanCo.SizeRamsey
