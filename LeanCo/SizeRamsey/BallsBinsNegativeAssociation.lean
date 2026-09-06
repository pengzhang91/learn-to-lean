import LeanCo.SizeRamsey.PathLowerBound
import LeanCo.SizeRamsey.WeightedAntivary

/-!
# Negative association of two bin loads

The exact conditional-fibre count is provided by `card_binLoadEqTailEvent`:
after fixing the load of one bin, the other bin is a named bin among the
remaining `q - 1` bins.  Its normalised tail is antitone in the first load,
so weighted Chebyshev gives the desired negative-correlation inequality.
-/

namespace LeanCo.SizeRamsey

open Finset Function

noncomputable section

/-- The load, packaged in the finite interval `0, ..., d`. -/
private def loadIndexNA {q d : ℕ} (i : Fin q)
    (f : Fin d → Fin q) : Fin (d + 1) :=
  ⟨binLoad f i, Nat.lt_succ_of_le (binLoad_le_numberOfBalls f i)⟩

private theorem loadIndexNA_eq_iff {q d : ℕ} (i : Fin q)
    (f : Fin d → Fin q) (a : Fin (d + 1)) :
    loadIndexNA i f = a ↔ binLoad f i = a.1 := by
  rw [Fin.ext_iff]
  rfl

private theorem sum_eqSlices_fin {q d : ℕ} (i : Fin q) :
    (∑ a : Fin (d + 1), (binLoadEqEvent (d := d) i a.1).card) =
      Fintype.card (Fin d → Fin q) := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Fin d → Fin q)))
    (t := (Finset.univ : Finset (Fin (d + 1))))
    (f := loadIndexNA i) (by intro f _; exact Finset.mem_univ _)
  rw [Finset.card_univ] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  ext f
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    binLoadEqEvent, loadIndexNA_eq_iff]

private theorem sum_eqTailSlices_fin {q d : ℕ}
    (i j : Fin q) (t : ℕ) :
    (∑ a : Fin (d + 1),
      (binLoadEqTailEvent (d := d) i j a.1 t).card) =
      (binLoadAtLeastEvent (d := d) j t).card := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise
    (s := binLoadAtLeastEvent (d := d) j t)
    (t := (Finset.univ : Finset (Fin (d + 1))))
    (f := loadIndexNA i) (by intro f _; exact Finset.mem_univ _)
  rw [h]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  ext f
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    binLoadAtLeastEvent, binLoadEqTailEvent, loadIndexNA_eq_iff]
  tauto

private theorem sum_eqSlices_indicator_fin {q d : ℕ}
    (i : Fin q) (t : ℕ) :
    (∑ a : Fin (d + 1),
      if t ≤ a.1 then (binLoadEqEvent (d := d) i a.1).card else 0) =
      (binLoadAtLeastEvent (d := d) i t).card := by
  classical
  let T : Finset (Fin (d + 1)) := Finset.univ.filter fun a ↦ t ≤ a.1
  have h := Finset.sum_card_fiberwise_eq_card_filter
    (s := (Finset.univ : Finset (Fin d → Fin q))) T (loadIndexNA i)
  rw [← Finset.sum_filter]
  change (∑ a ∈ T, (binLoadEqEvent (d := d) i a.1).card) = _
  calc
    (∑ a ∈ T, (binLoadEqEvent (d := d) i a.1).card) =
        ∑ a ∈ T,
          ((Finset.univ : Finset (Fin d → Fin q)).filter
            fun f ↦ loadIndexNA i f = a).card := by
      apply Finset.sum_congr rfl
      intro a _
      congr 1
      ext f
      simp only [binLoadEqEvent, loadIndexNA_eq_iff,
        Finset.mem_filter, Finset.mem_univ, true_and]
    _ = ((Finset.univ : Finset (Fin d → Fin q)).filter
          fun f ↦ loadIndexNA i f ∈ T).card := h
    _ = (binLoadAtLeastEvent (d := d) i t).card := by
      congr 1
      ext f
      simp only [T, binLoadAtLeastEvent, loadIndexNA,
        Finset.mem_filter, Finset.mem_univ, true_and]

private theorem sum_eqTailSlices_indicator_fin {q d : ℕ}
    (i j : Fin q) (t : ℕ) :
    (∑ a : Fin (d + 1),
      if t ≤ a.1 then
        (binLoadEqTailEvent (d := d) i j a.1 t).card else 0) =
      (twoBinLoadAtLeastEvent (d := d) i j t).card := by
  classical
  let T : Finset (Fin (d + 1)) := Finset.univ.filter fun a ↦ t ≤ a.1
  have h := Finset.sum_card_fiberwise_eq_card_filter
    (s := binLoadAtLeastEvent (d := d) j t) T (loadIndexNA i)
  rw [← Finset.sum_filter]
  change (∑ a ∈ T,
    (binLoadEqTailEvent (d := d) i j a.1 t).card) = _
  calc
    (∑ a ∈ T, (binLoadEqTailEvent (d := d) i j a.1 t).card) =
        ∑ a ∈ T,
          ((binLoadAtLeastEvent (d := d) j t).filter
            fun f ↦ loadIndexNA i f = a).card := by
      apply Finset.sum_congr rfl
      intro a _
      congr 1
      ext f
      simp only [binLoadAtLeastEvent, binLoadEqTailEvent,
        loadIndexNA_eq_iff, Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    _ = ((binLoadAtLeastEvent (d := d) j t).filter
          fun f ↦ loadIndexNA i f ∈ T).card := h
    _ = (twoBinLoadAtLeastEvent (d := d) i j t).card := by
      congr 1
      ext f
      simp only [T, binLoadAtLeastEvent, twoBinLoadAtLeastEvent,
        loadIndexNA, Finset.mem_filter, Finset.mem_univ, true_and]
      tauto

/-- Two distinct upper-tail events in the uniform balls-and-bins space are
negatively correlated, in division-free real counting form. -/
theorem twoBinLoadAtLeastEvent_mul_card_le_mul_cards_real
    {q d t : ℕ} (hq : 2 ≤ q) (i j : Fin q) (hij : i ≠ j) :
    ((twoBinLoadAtLeastEvent (d := d) i j t).card : ℝ) *
        Fintype.card (Fin d → Fin q) ≤
      ((binLoadAtLeastEvent (d := d) i t).card : ℝ) *
        (binLoadAtLeastEvent (d := d) j t).card := by
  classical
  let B := {k : Fin q // k ≠ i}
  let jb : B := ⟨j, fun h ↦ hij h.symm⟩
  let w : Fin (d + 1) → ℕ := fun a ↦
    Nat.choose d a.1 * (q - 1) ^ (d - a.1)
  let f : Fin (d + 1) → ℝ := fun a ↦
    if t ≤ a.1 then 1 else 0
  let g : Fin (d + 1) → ℝ := fun a ↦
    namedBinTailFraction B jb (d - a.1) t
  have hqm1 : 0 < q - 1 := by omega
  have hcardB : Fintype.card B = q - 1 := by
    dsimp only [B]
    rw [Fintype.card_subtype_compl (fun k : Fin q ↦ k = i)]
    simp
  letI : Nonempty B := ⟨jb⟩
  have hf : Monotone f := by
    intro a b hab
    by_cases ha : t ≤ a.1
    · have hb : t ≤ b.1 := ha.trans hab
      simp [f, ha, hb]
    · by_cases hb : t ≤ b.1 <;> simp [f, ha, hb]
  have hg : Antitone g := by
    intro a b hab
    apply namedBinTailFraction_mono_trials jb t
    exact Nat.sub_le_sub_left hab d
  have hpoint (a : Fin (d + 1)) :
      (w a : ℝ) * g a =
        ((binLoadEqTailEvent (d := d) i j a.1 t).card : ℝ) := by
    rw [card_binLoadEqTailEvent i j hij]
    simp only [w, g, namedBinTailFraction, hcardB, Nat.cast_mul,
      Nat.cast_pow]
    have hp : ((q - 1 : ℕ) : ℝ) ^ (d - a.1) ≠ 0 := by
      positivity
    field_simp
    rfl
  have htotal :
      (∑ a, (w a : ℝ)) = (Fintype.card (Fin d → Fin q) : ℝ) := by
    have h := congrArg (fun n : ℕ ↦ (n : ℝ))
      (sum_eqSlices_fin (d := d) i)
    simpa only [Nat.cast_sum, w, card_binLoadEqEvent] using h
  have hfirst :
      (∑ a, (w a : ℝ) * f a) =
        ((binLoadAtLeastEvent (d := d) i t).card : ℝ) := by
    have h := congrArg (fun n : ℕ ↦ (n : ℝ))
      (sum_eqSlices_indicator_fin (d := d) i t)
    simpa only [Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, w, f,
      card_binLoadEqEvent, mul_ite, mul_one, mul_zero] using h
  have hsecond :
      (∑ a, (w a : ℝ) * g a) =
        ((binLoadAtLeastEvent (d := d) j t).card : ℝ) := by
    rw [show (∑ a, (w a : ℝ) * g a) =
        ∑ a : Fin (d + 1),
          ((binLoadEqTailEvent (d := d) i j a.1 t).card : ℝ) by
      apply Finset.sum_congr rfl
      intro a _
      exact hpoint a]
    exact_mod_cast sum_eqTailSlices_fin (d := d) i j t
  have hjoint :
      (∑ a, (w a : ℝ) * (f a * g a)) =
        ((twoBinLoadAtLeastEvent (d := d) i j t).card : ℝ) := by
    have h := congrArg (fun n : ℕ ↦ (n : ℝ))
      (sum_eqTailSlices_indicator_fin (d := d) i j t)
    rw [Nat.cast_sum] at h
    rw [← h]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : t ≤ a.1
    · simp only [f, ha, if_true, one_mul]
      exact hpoint a
    · simp [f, ha]
  have hcov := weighted_antivary_sum w f g hf hg
  rw [htotal, hjoint, hfirst, hsecond] at hcov
  simpa only [mul_comm] using hcov

/-- Natural-number counting form of two-bin negative association. -/
theorem twoBinLoadAtLeastEvent_negative_association
    {q d t : ℕ} (hq : 2 ≤ q) (i j : Fin q) (hij : i ≠ j) :
    (twoBinLoadAtLeastEvent (d := d) i j t).card *
        Fintype.card (Fin d → Fin q) ≤
      (binLoadAtLeastEvent (d := d) i t).card *
        (binLoadAtLeastEvent (d := d) j t).card := by
  exact_mod_cast
    twoBinLoadAtLeastEvent_mul_card_le_mul_cards_real hq i j hij

/-- Division form of negative association. -/
theorem twoBinLoadAtLeastEvent_card_le_mul_div_card
    {q d t : ℕ} (hq : 2 ≤ q) (i j : Fin q) (hij : i ≠ j) :
    ((twoBinLoadAtLeastEvent (d := d) i j t).card : ℝ) ≤
      ((binLoadAtLeastEvent (d := d) i t).card : ℝ) *
          (binLoadAtLeastEvent (d := d) j t).card /
        Fintype.card (Fin d → Fin q) := by
  haveI : Nonempty (Fin d → Fin q) := ⟨fun _ ↦ i⟩
  have hN : (0 : ℝ) < Fintype.card (Fin d → Fin q) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Fin d → Fin q))
  apply (le_div_iff₀ hN).2
  exact twoBinLoadAtLeastEvent_mul_card_le_mul_cards_real hq i j hij

/-- The off-diagonal hypothesis of
`expectedMaxBinLoad_lower_bound_of_pair_bound` holds with `C = 1`. -/
theorem ballsBins_pair_bound_C_one {q d t : ℕ} (hq : 2 ≤ q)
    (i₀ : Fin q) :
    ∀ i j : Fin q, i ≠ j →
      ((twoBinLoadAtLeastEvent (d := d) i j t).card : ℝ) ≤
        (1 : ℝ) *
            ((binLoadAtLeastEvent (d := d) i₀ t).card : ℝ) ^ 2 /
          Fintype.card (Fin d → Fin q) := by
  intro i j hij
  have h := twoBinLoadAtLeastEvent_card_le_mul_div_card
    (d := d) (t := t) hq i j hij
  rw [card_binLoadAtLeastEvent_eq i i₀,
    card_binLoadAtLeastEvent_eq j i₀] at h
  simpa only [one_mul, pow_two] using h

/-- Paley--Zygmund lower bound with the pair-correlation constant discharged
by negative association (`C = 1`). -/
theorem expectedMaxBinLoad_lower_bound_of_negative_association
    {q d t : ℕ} (hq : 2 ≤ q) (i₀ : Fin q)
    (hfixed : 0 < ((binLoadAtLeastEvent (d := d) i₀ t).card : ℝ)) :
    let A : ℝ := (binLoadAtLeastEvent (d := d) i₀ t).card
    let N : ℝ := Fintype.card (Fin d → Fin q)
    let S : ℝ := q * A + q * (q - 1) * (A ^ 2 / N)
    (t : ℝ) * ((q * A) ^ 2 / (N * S)) ≤ expectedMaxBinLoad q d := by
  simpa only [one_mul] using
    (expectedMaxBinLoad_lower_bound_of_pair_bound (C := 1) i₀ hfixed
      (ballsBins_pair_bound_C_one hq i₀))

end

end LeanCo.SizeRamsey
