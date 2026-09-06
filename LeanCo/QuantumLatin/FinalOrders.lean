import LeanCo.QuantumLatin.OrderData
import LeanCo.QuantumLatin.OrderNinety
import LeanCo.QuantumLatin.PointedEight
import LeanCo.QuantumLatin.PointedTwelve
import LeanCo.QuantumLatin.RegularCyclic
import LeanCo.QuantumLatin.SingularConstruction

/-!
# The order classification

This file closes the arithmetic part of Zhang--Cao's main theorem.  The
seventeen values below are exactly the possible exceptions in Theorem 1.2.
Odd orders and multiples of four use the direct constructions.  Orders
congruent to two modulo four use the singular product, with a finite checked
table below `266` and a uniform coprime outer order thereafter.
-/

namespace LeanCo.QuantumLatin

/-- The seventeen possible exceptions in Theorem 1.2 of the paper. -/
def IsExceptionalOrder (v : ℕ) : Prop :=
  v = 10 ∨ v = 14 ∨ v = 18 ∨ v = 22 ∨ v = 26 ∨
  v = 30 ∨ v = 34 ∨ v = 38 ∨ v = 42 ∨ v = 46 ∨
  v = 54 ∨ v = 58 ∨ v = 62 ∨ v = 66 ∨ v = 74 ∨
  v = 82 ∨ v = 94

instance (v : ℕ) : Decidable (IsExceptionalOrder v) := by
  unfold IsExceptionalOrder
  infer_instance

/-! ## Numerical wrappers for the two pointed inputs -/

theorem existsMaximalRQLS_seven_singular {n h : ℕ}
    (hhn : h ≤ n) (hn : OuterOK n) (hh : SupportedOrder h) :
    ExistsMaximalRQLS (n * 7 + h) := by
  obtain ⟨A⟩ := exists_biresolution_fin_of_outerOK hn
  obtain ⟨D⟩ := existsMaximalRQLS_of_supportedOrder hh
  obtain ⟨R, hR⟩ := exists_regular_seven
  exact existsMaximalRQLS_singularProduct_fin hhn A R
    pointedMaximalRQLSEight D hR pointedMaximalRQLSEight_regular

theorem existsMaximalRQLS_eleven_singular {n h : ℕ}
    (hhn : h ≤ n) (hn : OuterOK n) (hh : SupportedOrder h) :
    ExistsMaximalRQLS (n * 11 + h) := by
  obtain ⟨A⟩ := exists_biresolution_fin_of_outerOK hn
  obtain ⟨D⟩ := existsMaximalRQLS_of_supportedOrder hh
  obtain ⟨R, hR⟩ := exists_regular_eleven
  exact existsMaximalRQLS_singularProduct_fin hhn A R
    pointedMaximalRQLSTwelve D hR pointedMaximalRQLSTwelve_regular

/-! ## A finite certificate for the small `2 mod 4` orders -/

/-- A bounded, executable certificate that `v` has a usable singular-product
decomposition with inner order `m`.  Forty outer candidates suffice below
the cutoff used here. -/
def SmallRecipeAt (m v : ℕ) : Prop :=
  ∃ n : Fin 40,
    m * n.1 ≤ v ∧
    v - m * n.1 ≤ n.1 ∧
    OuterOK n.1 ∧
    SupportedOrder (v - m * n.1)

instance (m v : ℕ) : Decidable (SmallRecipeAt m v) := by
  unfold SmallRecipeAt
  infer_instance

def SmallRecipe (v : ℕ) : Prop :=
  SmallRecipeAt 7 v ∨ SmallRecipeAt 11 v

instance (v : ℕ) : Decidable (SmallRecipe v) := by
  unfold SmallRecipe
  infer_instance

theorem existsMaximalRQLS_of_smallRecipe {v : ℕ} (hv : SmallRecipe v) :
    ExistsMaximalRQLS v := by
  rcases hv with ⟨n, hnv, hhn, hn, hh⟩ | ⟨n, hnv, hhn, hn, hh⟩
  · have H := existsMaximalRQLS_seven_singular hhn hn hh
    convert H using 1 <;> omega
  · have H := existsMaximalRQLS_eleven_singular hhn hn hh
    convert H using 1 <;> omega

/-- Exhaustive arithmetic certificate for all relevant orders below `266`.
It checks only finite arithmetic predicates with kernel `decide`; no
mathematical construction is evaluated. -/
theorem smallRecipe_below_cutoff :
    ∀ v : Fin 266,
      7 ≤ v.1 → v.1 % 4 = 2 →
      ¬ IsExceptionalOrder v.1 → v.1 ≠ 90 → SmallRecipe v.1 := by
  intro v hv hv4 hvNotExceptional hv90
  let q := v.1 / 4
  have hq : q < 66 := by
    dsimp only [q]
    omega
  have hvEq : v.1 = 4 * q + 2 := by
    dsimp only [q]
    omega
  interval_cases q
  all_goals norm_num [hvEq] at hv
  all_goals norm_num [hvEq] at hv90
  all_goals norm_num [hvEq, IsExceptionalOrder] at hvNotExceptional
  all_goals simp only [hvEq]
  · exact Or.inl ⟨⟨7, by decide⟩, by decide, by decide, by decide, by decide⟩
  · exact Or.inl ⟨⟨9, by decide⟩, by decide, by decide, by decide, by decide⟩
  · exact Or.inl ⟨⟨11, by decide⟩, by decide, by decide, by decide, by decide⟩
  · exact Or.inl ⟨⟨11, by decide⟩, by decide, by decide, by decide, by decide⟩
  · exact Or.inl ⟨⟨13, by decide⟩, by decide, by decide, by decide, by decide⟩
  · exact Or.inl ⟨⟨13, by decide⟩, by decide, by decide, by decide, by decide⟩
  · exact Or.inl ⟨⟨14, by decide⟩, by decide, by decide, by decide, by decide⟩
  · exact Or.inl ⟨⟨14, by decide⟩, by decide, by decide, by decide, by decide⟩
  · exact Or.inl ⟨⟨15, by decide⟩, by decide, by decide, by decide, by decide⟩
  · exact Or.inl ⟨⟨15, by decide⟩, by decide, by decide, by decide, by decide⟩
  · exact Or.inr ⟨⟨11, by decide⟩, by decide, by decide, by decide, by decide⟩
  · exact Or.inl ⟨⟨17, by decide⟩, by decide, by decide, by decide, by decide⟩
  · exact Or.inl ⟨⟨17, by decide⟩, by decide, by decide, by decide, by decide⟩
  · exact Or.inl ⟨⟨17, by decide⟩, by decide, by decide, by decide, by decide⟩
  · exact Or.inl ⟨⟨18, by decide⟩, by decide, by decide, by decide, by decide⟩
  · exact Or.inl ⟨⟨18, by decide⟩, by decide, by decide, by decide, by decide⟩
  · exact Or.inl ⟨⟨19, by decide⟩, by decide, by decide, by decide, by decide⟩
  · exact Or.inl ⟨⟨19, by decide⟩, by decide, by decide, by decide, by decide⟩
  · exact Or.inl ⟨⟨21, by decide⟩, by decide, by decide, by decide, by decide⟩
  · exact Or.inl ⟨⟨21, by decide⟩, by decide, by decide, by decide, by decide⟩
  · exact Or.inl ⟨⟨21, by decide⟩, by decide, by decide, by decide, by decide⟩
  · exact Or.inl ⟨⟨21, by decide⟩, by decide, by decide, by decide, by decide⟩
  · exact Or.inl ⟨⟨23, by decide⟩, by decide, by decide, by decide, by decide⟩
  · exact Or.inl ⟨⟨23, by decide⟩, by decide, by decide, by decide, by decide⟩
  · exact Or.inl ⟨⟨23, by decide⟩, by decide, by decide, by decide, by decide⟩
  · exact Or.inl ⟨⟨23, by decide⟩, by decide, by decide, by decide, by decide⟩
  · exact Or.inl ⟨⟨25, by decide⟩, by decide, by decide, by decide, by decide⟩
  · exact Or.inl ⟨⟨25, by decide⟩, by decide, by decide, by decide, by decide⟩
  · exact Or.inl ⟨⟨25, by decide⟩, by decide, by decide, by decide, by decide⟩
  · exact Or.inl ⟨⟨25, by decide⟩, by decide, by decide, by decide, by decide⟩
  · exact Or.inr ⟨⟨17, by decide⟩, by decide, by decide, by decide, by decide⟩
  · exact Or.inr ⟨⟨18, by decide⟩, by decide, by decide, by decide, by decide⟩
  · exact Or.inl ⟨⟨29, by decide⟩, by decide, by decide, by decide, by decide⟩
  · exact Or.inl ⟨⟨29, by decide⟩, by decide, by decide, by decide, by decide⟩
  · exact Or.inl ⟨⟨29, by decide⟩, by decide, by decide, by decide, by decide⟩
  · exact Or.inl ⟨⟨29, by decide⟩, by decide, by decide, by decide, by decide⟩
  · exact Or.inl ⟨⟨29, by decide⟩, by decide, by decide, by decide, by decide⟩
  · exact Or.inl ⟨⟨29, by decide⟩, by decide, by decide, by decide, by decide⟩
  · exact Or.inl ⟨⟨31, by decide⟩, by decide, by decide, by decide, by decide⟩
  · exact Or.inl ⟨⟨31, by decide⟩, by decide, by decide, by decide, by decide⟩
  · exact Or.inl ⟨⟨31, by decide⟩, by decide, by decide, by decide, by decide⟩
  · exact Or.inl ⟨⟨31, by decide⟩, by decide, by decide, by decide, by decide⟩
  · exact Or.inr ⟨⟨21, by decide⟩, by decide, by decide, by decide, by decide⟩
  · exact Or.inl ⟨⟨35, by decide⟩, by decide, by decide, by decide, by decide⟩
  · exact Or.inl ⟨⟨35, by decide⟩, by decide, by decide, by decide, by decide⟩
  · exact Or.inl ⟨⟨35, by decide⟩, by decide, by decide, by decide, by decide⟩

/-! ## A uniform outer order for the large case -/

/-- The first integer of the form `6q+1` or `6q+5` at or above `a`.
It lies at most three places above `a` and is coprime to both two and three. -/
def nextOuter (a : ℕ) : ℕ :=
  if a % 6 ≤ 1 then 6 * (a / 6) + 1 else 6 * (a / 6) + 5

theorem nextOuter_bounds (a : ℕ) :
    a ≤ nextOuter a ∧ nextOuter a ≤ a + 3 := by
  have hr : a % 6 < 6 := Nat.mod_lt _ (by decide)
  have ha : a % 6 + 6 * (a / 6) = a := Nat.mod_add_div a 6
  by_cases h : a % 6 ≤ 1
  · simp only [nextOuter, if_pos h]
    omega
  · simp only [nextOuter, if_neg h]
    omega

private theorem coprime_six_mul_add_one (q : ℕ) :
    Nat.Coprime 2 (6 * q + 1) ∧ Nat.Coprime 3 (6 * q + 1) := by
  constructor
  · rw [show 6 * q + 1 = 1 + 2 * (3 * q) by omega,
      Nat.coprime_add_mul_left_right]
    norm_num
  · rw [show 6 * q + 1 = 1 + 3 * (2 * q) by omega,
      Nat.coprime_add_mul_left_right]
    norm_num

private theorem coprime_six_mul_add_five (q : ℕ) :
    Nat.Coprime 2 (6 * q + 5) ∧ Nat.Coprime 3 (6 * q + 5) := by
  constructor
  · rw [show 6 * q + 5 = 1 + 2 * (3 * q + 2) by omega,
      Nat.coprime_add_mul_left_right]
    norm_num
  · rw [show 6 * q + 5 = 2 + 3 * (2 * q + 1) by omega,
      Nat.coprime_add_mul_left_right]
    norm_num

theorem nextOuter_coprime (a : ℕ) :
    Nat.Coprime 2 (nextOuter a) ∧ Nat.Coprime 3 (nextOuter a) := by
  by_cases h : a % 6 ≤ 1
  · simpa [nextOuter, h] using coprime_six_mul_add_one (a / 6)
  · simpa [nextOuter, h] using coprime_six_mul_add_five (a / 6)

theorem nextOuter_outerOK (a : ℕ) : OuterOK (nextOuter a) :=
  Or.inl (nextOuter_coprime a)

private theorem cutoff_arithmetic {v : ℕ} (hv : 266 ≤ v) :
    v ≤ 8 * ((v + 7) / 8) ∧
      7 * (((v + 7) / 8) + 3) + 7 ≤ v := by
  omega

/-- Uniform singular-product construction for every sufficiently large order
congruent to two modulo four. -/
theorem existsMaximalRQLS_large_two_mod_four {v : ℕ}
    (hv : 266 ≤ v) (hv4 : v % 4 = 2) : ExistsMaximalRQLS v := by
  let a := (v + 7) / 8
  let n := nextOuter a
  let h := v - 7 * n
  have hnBounds : a ≤ n ∧ n ≤ a + 3 := by
    simpa [n] using nextOuter_bounds a
  have hvBounds := cutoff_arithmetic hv
  have h7nv : 7 * n ≤ v := by
    dsimp only [a] at hnBounds
    omega
  have hh7 : 7 ≤ h := by
    dsimp only [a] at hnBounds
    dsimp only [h]
    omega
  have hhn : h ≤ n := by
    dsimp only [a] at hnBounds
    dsimp only [h]
    omega
  have hnOdd : Odd n := Nat.coprime_two_left.mp (nextOuter_coprime a).1
  have h7nOdd : Odd (7 * n) := (by norm_num : Odd 7).mul hnOdd
  have hvEven : Even v := by
    rw [Nat.even_iff]
    omega
  have hhOdd : Odd h := by
    dsimp only [h]
    rw [Nat.odd_sub' h7nv]
    exact iff_of_true h7nOdd hvEven
  have hh : SupportedOrder h := Or.inr (Or.inr (Or.inl ⟨hh7, hhOdd⟩))
  have H := existsMaximalRQLS_seven_singular hhn
    (nextOuter_outerOK a) hh
  convert H using 1 <;> dsimp only [h] <;> omega

theorem existsMaximalRQLS_small_two_mod_four {v : ℕ}
    (hv : 7 ≤ v) (hvlt : v < 266) (hv4 : v % 4 = 2)
    (hvNotExceptional : ¬ IsExceptionalOrder v) : ExistsMaximalRQLS v := by
  by_cases hv90 : v = 90
  · subst v
    exact existsMaximalRQLS_ninety
  · exact existsMaximalRQLS_of_smallRecipe
      (smallRecipe_below_cutoff ⟨v, hvlt⟩ hv hv4 hvNotExceptional hv90)

/-! ## The main theorem -/

/-- Zhang--Cao, Theorem 1.2: every order at least seven admits a
maximal-cardinality resolvable quantum Latin square, apart from the seventeen
orders explicitly left open by the paper. -/
theorem existsMaximalRQLS_main {v : ℕ} (hv : 7 ≤ v)
    (hvNotExceptional : ¬ IsExceptionalOrder v) : ExistsMaximalRQLS v := by
  by_cases hvOdd : Odd v
  · exact existsMaximalRQLS_of_supportedOrder
      (Or.inr (Or.inr (Or.inl ⟨hv, hvOdd⟩)))
  by_cases hvFour : 4 ∣ v
  · by_cases hvEight : v = 8
    · subst v
      exact existsMaximalRQLS_eight
    · have hvTwelve : 12 ≤ v := by
        obtain ⟨k, hk⟩ := hvFour
        omega
      exact existsMaximalRQLS_of_supportedOrder
        (Or.inr (Or.inr (Or.inr ⟨hvTwelve, hvFour⟩)))
  have hvEven : Even v := Nat.not_odd_iff_even.mp hvOdd
  have hvModTwo : v % 2 = 0 := Nat.even_iff.mp hvEven
  have hvModFourNe : v % 4 ≠ 0 := by
    intro h
    exact hvFour (Nat.dvd_iff_mod_eq_zero.mpr h)
  have hv4 : v % 4 = 2 := by
    have hr := Nat.mod_lt v (by decide : 0 < 4)
    omega
  by_cases hvLarge : 266 ≤ v
  · exact existsMaximalRQLS_large_two_mod_four hvLarge hv4
  · exact existsMaximalRQLS_small_two_mod_four hv (by omega) hv4
      hvNotExceptional

/-- A paper-numbered alias for the end-to-end theorem. -/
theorem zhangCao_theorem_1_2 {v : ℕ} (hv : 7 ≤ v)
    (hvNotExceptional : ¬ IsExceptionalOrder v) : ExistsMaximalRQLS v :=
  existsMaximalRQLS_main hv hvNotExceptional

end LeanCo.QuantumLatin
