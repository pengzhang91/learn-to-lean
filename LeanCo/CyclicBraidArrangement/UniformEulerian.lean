import LeanCo.CyclicBraidArrangement.CharacteristicBridge
import LeanCo.CyclicBraidArrangement.Uniform

/-!
# Eulerian grouping for uniform interval deformations

This file groups the normalized cyclic-order sum by its cyclic descent
number.  The resulting finite cardinal is the paper's Eulerian coefficient
`A(n - 1, d)`, using the cyclic-order interpretation stated immediately
before Corollary 4.1.
-/

namespace CyclicBraidArrangement

open scoped BigOperators

namespace DeformationMatrix

/-- The Eulerian coefficient in the cyclic-order model used by the paper:
normalized cyclic orders on `n` labels with `d + 1` cyclic descents. -/
noncomputable def cyclicEulerianNumber (n d : ℕ) [NeZero n] : ℕ := by
  classical
  exact ((Finset.univ : Finset (NormalizedCycle n)).filter
    (fun w ↦ cyclicDescents w.1 = d + 1)).card

private theorem nextPosition_zero {n : ℕ} [NeZero n] (hn : 2 ≤ n) :
    nextPosition n 0 = (1 : Fin n) := by
  ext
  simp [nextPosition, Nat.mod_eq_of_lt (by omega : 1 < n)]

private theorem cyclicDescents_lt_card {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) (w : NormalizedCycle n) :
    cyclicDescents w.1 < n := by
  classical
  let s := (Finset.univ.filter (cyclicDescent w.1) : Finset (Fin n))
  have hs : s ⊆ Finset.univ := Finset.subset_univ _
  have hzero : (0 : Fin n) ∉ s := by
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [cyclicDescent, nextPosition_zero hn, w.2]
    exact Fin.not_lt_zero _
  have hproper : s ⊂ Finset.univ := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hs, ?_⟩
    intro hEq
    have : (0 : Fin n) ∈ s := by rw [hEq]; simp
    exact hzero this
  simpa [cyclicDescents, s] using Finset.card_lt_card hproper

private theorem nextPosition_last {n : ℕ} [NeZero n] (hn : 2 ≤ n) :
    nextPosition n ⟨n - 1, by omega⟩ = (0 : Fin n) := by
  change (⟨n - 1, by omega⟩ : Fin n) + 1 = 0
  ext
  simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 1 < n),
    Nat.sub_add_cancel (by omega : 1 ≤ n)]

private theorem one_le_cyclicDescents {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) (w : NormalizedCycle n) :
    1 ≤ cyclicDescents w.1 := by
  classical
  let last : Fin n := ⟨n - 1, by omega⟩
  have hlast0 : w.1 last ≠ 0 := by
    intro h
    have hlast_ne : last ≠ (0 : Fin n) := by
      intro heq
      have := congrArg Fin.val heq
      dsimp [last] at this
      omega
    have hw : w.1 last = w.1 0 := by simpa [w.2] using h
    exact hlast_ne (w.1.injective hw)
  have hdes : cyclicDescent w.1 last := by
    rw [cyclicDescent, nextPosition_last hn, w.2]
    exact Fin.pos_iff_ne_zero.mpr hlast0
  unfold cyclicDescents
  exact Finset.one_le_card.mpr ⟨last, Finset.mem_filter.mpr ⟨by simp, hdes⟩⟩

private theorem descentIndex_mem_range {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) (w : NormalizedCycle n) :
    cyclicDescents w.1 - 1 ∈ Finset.range (n - 1) := by
  rw [Finset.mem_range]
  have hlo := one_le_cyclicDescents hn w
  have hhi := cyclicDescents_lt_card hn w
  omega

/-- Corollary 4.1 at the cyclic-formula level, with the sum grouped by the
Eulerian coefficient described in the paper.  The signed integer expression
for `v - u` avoids an unnecessary assumption comparing `u` and `v`. -/
theorem cycleFormula_uniform_eulerian
    {n u v : ℕ} [NeZero n] (hn : 2 ≤ n) (t : ℚ) :
    cycleFormula (uniform n u v) t =
      ∑ d ∈ Finset.range (n - 1),
        (cyclicEulerianNumber n d : ℚ) *
          generalizedChoose
            (t - (((n : ℤ) * u + ((v : ℤ) - u) * (d + 1) : ℤ) : ℚ) - 1)
            (n - 1) := by
  classical
  rw [cycleFormula_uniform hn]
  let g : NormalizedCycle n → ℕ := fun w ↦ cyclicDescents w.1 - 1
  let f : ℕ → ℚ := fun d ↦ generalizedChoose
    (t - (((n : ℤ) * u + ((v : ℤ) - u) * (d + 1) : ℤ) : ℚ) - 1)
    (n - 1)
  calc
    (∑ w : NormalizedCycle n,
        generalizedChoose
          (t - (((n : ℤ) * u + ((v : ℤ) - u) * cyclicDescents w.1 : ℤ) : ℚ) - 1)
          (n - 1)) =
        ∑ w : NormalizedCycle n, f (g w) := by
          apply Finset.sum_congr rfl
          intro w _
          dsimp [f, g]
          have h := one_le_cyclicDescents hn w
          have hnat : cyclicDescents w.1 = cyclicDescents w.1 - 1 + 1 :=
            (Nat.sub_add_cancel h).symm
          have hint : (cyclicDescents w.1 : ℤ) =
              ((cyclicDescents w.1 - 1 : ℕ) : ℤ) + 1 := by
            exact_mod_cast hnat
          rw [hint]
    _ = ∑ d ∈ Finset.range (n - 1),
          ∑ w ∈ (Finset.univ : Finset (NormalizedCycle n)) with g w = d,
            f d := by
          symm
          exact Finset.sum_fiberwise_of_maps_to'
            (s := (Finset.univ : Finset (NormalizedCycle n)))
            (t := Finset.range (n - 1))
            (g := g) (fun w _ ↦ descentIndex_mem_range hn w) f
    _ = ∑ d ∈ Finset.range (n - 1),
          (cyclicEulerianNumber n d : ℚ) * f d := by
          apply Finset.sum_congr rfl
          intro d _
          rw [Finset.sum_const, nsmul_eq_mul]
          congr 1
          norm_cast
          unfold cyclicEulerianNumber g
          congr 1
          ext w
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          have hlo := one_le_cyclicDescents hn w
          omega
    _ = _ := rfl

end DeformationMatrix

end CyclicBraidArrangement
