import LeanCo.CyclicBraidArrangement.FerrersFactorizationDirect

/-!
# Drop-last algebra for the Ferrers insertion recurrence

This file isolates the finite-set, height, product, and falling-factorial
identities needed after the safe cyclic insertion equivalences are built.
It does not depend on those equivalences.
-/

namespace CyclicBraidArrangement

open scoped BigOperators

namespace DeformationMatrix

noncomputable section

/-- Dropping the last coordinate and mapping back by `Fin.castSucc` gives
exactly the original column set with its last element erased. -/
theorem map_ferrersDropLastColumns {n : ℕ}
    (C : Finset (Fin (n + 1))) :
    (ferrersDropLastColumns C).map Fin.castSuccEmb =
      C.erase (Fin.last n) := by
  classical
  ext i
  constructor
  · intro hi
    rw [Finset.mem_map] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    exact Finset.mem_erase.mpr
      ⟨Fin.castSucc_ne_last j, (mem_ferrersDropLastColumns C j).mp hj⟩
  · intro hi
    obtain ⟨hilast, hiC⟩ := Finset.mem_erase.mp hi
    obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr hilast
    rw [Finset.mem_map]
    exact ⟨j, (mem_ferrersDropLastColumns C j).mpr hiC, rfl⟩

theorem card_ferrersDropLastColumns_of_not_mem {n : ℕ}
    (C : Finset (Fin (n + 1))) (htop : Fin.last n ∉ C) :
    (ferrersDropLastColumns C).card = C.card := by
  have h := congrArg Finset.card (map_ferrersDropLastColumns C)
  simpa [Finset.card_map, Finset.erase_eq_of_notMem htop] using h

theorem card_ferrersDropLastColumns_of_mem {n : ℕ}
    (C : Finset (Fin (n + 1))) (htop : Fin.last n ∈ C) :
    (ferrersDropLastColumns C).card = C.card - 1 := by
  have h := congrArg Finset.card (map_ferrersDropLastColumns C)
  simpa [Finset.card_map, Finset.card_erase_of_mem htop] using h

theorem card_eq_card_ferrersDropLastColumns_add_one_of_mem {n : ℕ}
    (C : Finset (Fin (n + 1))) (htop : Fin.last n ∈ C) :
    C.card = (ferrersDropLastColumns C).card + 1 := by
  rw [card_ferrersDropLastColumns_of_mem C htop]
  exact (Nat.sub_add_cancel (Finset.one_le_card.mpr ⟨Fin.last n, htop⟩)).symm

/-- Ferrers height is unchanged for every lower column after dropping the
last coordinate. -/
theorem ferrersHeight_dropLast_castSucc {n : ℕ}
    (C : Finset (Fin (n + 1))) (c : Fin n) :
    ferrersHeight C c.castSucc =
      ferrersHeight (ferrersDropLastColumns C) c := by
  classical
  unfold ferrersHeight
  let lower : Finset (Fin n) :=
    (Finset.Iio c).filter fun b ↦ b ∉ ferrersDropLastColumns C
  let upper : Finset (Fin (n + 1)) :=
    (Finset.Iio c.castSucc).filter fun b ↦ b ∉ C
  have hmap : lower.map Fin.castSuccEmb = upper := by
    ext i
    constructor
    · intro hi
      rw [Finset.mem_map] at hi
      obtain ⟨j, hj, rfl⟩ := hi
      change j ∈ lower at hj
      change j.castSucc ∈ upper
      simpa [lower, upper] using hj
    · intro hi
      change i ∈ upper at hi
      have hilast : i ≠ Fin.last n := by
        intro h
        subst i
        have hlt := Finset.mem_Iio.mp (Finset.mem_filter.mp hi).1
        exact (not_lt_of_ge (Fin.le_last _)) hlt
      obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr hilast
      rw [Finset.mem_map]
      refine ⟨j, ?_, rfl⟩
      change j ∈ lower
      simpa [lower, upper] using hi
  have hcard := congrArg Finset.card hmap
  simpa [lower, upper, Finset.card_map] using hcard.symm

/-- At the last label, height counts precisely the lower labels not selected
as columns. -/
theorem ferrersHeight_last_eq_sub_card_drop {n : ℕ}
    (C : Finset (Fin (n + 1))) :
    ferrersHeight C (Fin.last n) =
      n - (ferrersDropLastColumns C).card := by
  have hselected :
      ferrersSelectedBelow C (Fin.last n) =
        (ferrersDropLastColumns C).card := by
    unfold ferrersSelectedBelow
    have hmap := map_ferrersDropLastColumns C
    have hcard := congrArg Finset.card hmap
    rw [Finset.card_map] at hcard
    have herase :
        ((Finset.Iio (Fin.last n)).filter fun b ↦ b ∈ C) =
          C.erase (Fin.last n) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_Iio, Finset.mem_erase]
      rw [Fin.lt_last_iff_ne_last]
    rw [herase]
    exact hcard.symm
  have hsum := ferrersHeight_add_ferrersSelectedBelow C (Fin.last n)
  rw [hselected] at hsum
  simpa using Nat.eq_sub_of_add_eq hsum

/-- Reindex a product over the dropped columns by `Fin.castSucc`. -/
theorem prod_ferrersDropLastColumns {n : ℕ} {M : Type*}
    [CommMonoid M] (C : Finset (Fin (n + 1))) (f : Fin (n + 1) → M) :
    (∏ c ∈ ferrersDropLastColumns C, f c.castSucc) =
      ∏ c ∈ C.erase (Fin.last n), f c := by
  classical
  calc
    (∏ c ∈ ferrersDropLastColumns C, f c.castSucc) =
        ∏ c ∈ (ferrersDropLastColumns C).map Fin.castSuccEmb, f c :=
      (Finset.prod_map (ferrersDropLastColumns C) Fin.castSuccEmb f).symm
    _ = _ := by rw [map_ferrersDropLastColumns]

theorem prod_eq_prod_ferrersDropLastColumns_of_not_mem {n : ℕ}
    {M : Type*} [CommMonoid M] (C : Finset (Fin (n + 1)))
    (f : Fin (n + 1) → M) (htop : Fin.last n ∉ C) :
    (∏ c ∈ C, f c) =
      ∏ c ∈ ferrersDropLastColumns C, f c.castSucc := by
  rw [prod_ferrersDropLastColumns, Finset.erase_eq_of_notMem htop]

theorem prod_eq_last_mul_prod_ferrersDropLastColumns_of_mem {n : ℕ}
    {M : Type*} [CommMonoid M] (C : Finset (Fin (n + 1)))
    (f : Fin (n + 1) → M) (htop : Fin.last n ∈ C) :
    (∏ c ∈ C, f c) =
      f (Fin.last n) *
        ∏ c ∈ ferrersDropLastColumns C, f c.castSucc := by
  rw [prod_ferrersDropLastColumns]
  exact (Finset.mul_prod_erase C f htop).symm

/-- Appending one more falling-factorial term. -/
theorem fallingFactorialValue_succ (x : ℚ) (k : ℕ) :
    fallingFactorialValue x (k + 1) =
      fallingFactorialValue x k * (x - k) := by
  unfold fallingFactorialValue
  rw [Finset.prod_range_succ]

theorem zero_not_mem_ferrersDropLastColumns {n : ℕ} [NeZero n]
    (C : Finset (Fin (n + 1))) (hzero : (0 : Fin (n + 1)) ∉ C) :
    (0 : Fin n) ∉ ferrersDropLastColumns C := by
  simpa using hzero

theorem card_ferrersDropLastColumns_lt {n : ℕ} [NeZero n]
    (C : Finset (Fin (n + 1))) (hzero : (0 : Fin (n + 1)) ∉ C) :
    (ferrersDropLastColumns C).card < n := by
  have hz := zero_not_mem_ferrersDropLastColumns C hzero
  have hproper : ferrersDropLastColumns C ⊂
      (Finset.univ : Finset (Fin n)) := by
    refine Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ _, ?_⟩
    intro h
    apply hz
    rw [h]
    simp
  simpa using Finset.card_lt_card hproper

/-- The product of linear Ferrers factors simply reindexes when the last
label is not a column. -/
theorem ferrersLinearProduct_dropLast_of_not_mem {n : ℕ}
    (C : Finset (Fin (n + 1))) (t : ℚ)
    (htop : Fin.last n ∉ C) :
    (∏ c ∈ C, (t - C.card - ferrersHeight C c)) =
      ∏ c ∈ ferrersDropLastColumns C,
        (t - (ferrersDropLastColumns C).card -
          ferrersHeight (ferrersDropLastColumns C) c) := by
  rw [prod_eq_prod_ferrersDropLastColumns_of_not_mem C
    (fun c ↦ t - C.card - ferrersHeight C c) htop]
  apply Finset.prod_congr rfl
  intro c hc
  rw [card_ferrersDropLastColumns_of_not_mem C htop,
    ferrersHeight_dropLast_castSucc]

/-- If the last label is selected, its factor separates and every lower
factor is the corresponding factor at the shifted evaluation `t-1`. -/
theorem ferrersLinearProduct_dropLast_of_mem {n : ℕ}
    (C : Finset (Fin (n + 1))) (t : ℚ)
    (htop : Fin.last n ∈ C) :
    (∏ c ∈ C, (t - C.card - ferrersHeight C c)) =
      (t - n - 1) *
        ∏ c ∈ ferrersDropLastColumns C,
          ((t - 1) - (ferrersDropLastColumns C).card -
            ferrersHeight (ferrersDropLastColumns C) c) := by
  rw [prod_eq_last_mul_prod_ferrersDropLastColumns_of_mem C
    (fun c ↦ t - C.card - ferrersHeight C c) htop]
  have hcard := card_eq_card_ferrersDropLastColumns_add_one_of_mem C htop
  have htopHeight := ferrersHeight_last_eq_sub_card_drop C
  congr 1
  · push_cast [hcard, htopHeight]
    have hle : (ferrersDropLastColumns C).card ≤ n := by
      simpa using Finset.card_le_univ (ferrersDropLastColumns C)
    rw [Nat.cast_sub hle]
    ring
  · apply Finset.prod_congr rfl
    intro c hc
    rw [ferrersHeight_dropLast_castSucc, hcard]
    push_cast
    ring

/-- The initial falling-factorial block gains the factor `t-n` when an
unselected last label is retained as an ordinary label. -/
theorem ferrersBaseFactor_dropLast_of_not_mem {n : ℕ} [NeZero n]
    (C : Finset (Fin (n + 1))) (t : ℚ)
    (hzero : (0 : Fin (n + 1)) ∉ C)
    (htop : Fin.last n ∉ C) :
    fallingFactorialValue (t - C.card - 1)
        ((n + 1) - C.card - 1) =
      (t - n) *
        fallingFactorialValue
          (t - (ferrersDropLastColumns C).card - 1)
          (n - (ferrersDropLastColumns C).card - 1) := by
  let D := ferrersDropLastColumns C
  change fallingFactorialValue (t - C.card - 1)
        ((n + 1) - C.card - 1) =
      (t - n) * fallingFactorialValue (t - D.card - 1)
        (n - D.card - 1)
  have hcard : D.card = C.card :=
    card_ferrersDropLastColumns_of_not_mem C htop
  have hlt : D.card < n := card_ferrersDropLastColumns_lt C hzero
  have hlen : (n + 1) - C.card - 1 =
      (n - D.card - 1) + 1 := by omega
  rw [hlen, fallingFactorialValue_succ, ← hcard]
  have hle : D.card + 1 ≤ n := hlt
  have hcast : ((n - D.card - 1 : ℕ) : ℚ) =
      (n : ℚ) - D.card - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n - D.card),
      Nat.cast_sub hlt.le]
    norm_num
  rw [hcast]
  push_cast
  ring

/-- Selecting the last label shifts the lower-rank evaluation by one but
does not otherwise change the initial falling-factorial block. -/
theorem ferrersBaseFactor_dropLast_of_mem {n : ℕ}
    (C : Finset (Fin (n + 1))) (t : ℚ)
    (htop : Fin.last n ∈ C) :
    fallingFactorialValue (t - C.card - 1)
        ((n + 1) - C.card - 1) =
      fallingFactorialValue
        ((t - 1) - (ferrersDropLastColumns C).card - 1)
        (n - (ferrersDropLastColumns C).card - 1) := by
  have hcard := card_eq_card_ferrersDropLastColumns_add_one_of_mem C htop
  congr 2
  · push_cast [hcard]
    ring
  · omega

/-- Rational Ferrers product recurrence for an unselected last label. -/
theorem ferrersShiFactorValue_dropLast_of_not_mem {n : ℕ} [NeZero n]
    (C : Finset (Fin (n + 1))) (t : ℚ)
    (hzero : (0 : Fin (n + 1)) ∉ C)
    (htop : Fin.last n ∉ C) :
    ferrersShiFactorValue C t =
      (t - n) * ferrersShiFactorValue (ferrersDropLastColumns C) t := by
  unfold ferrersShiFactorValue
  rw [ferrersBaseFactor_dropLast_of_not_mem C t hzero htop,
    ferrersLinearProduct_dropLast_of_not_mem C t htop]
  ring

/-- Rational Ferrers product recurrence for a selected last label. -/
theorem ferrersShiFactorValue_dropLast_of_mem {n : ℕ}
    (C : Finset (Fin (n + 1))) (t : ℚ)
    (htop : Fin.last n ∈ C) :
    ferrersShiFactorValue C t =
      (t - n - 1) *
        ferrersShiFactorValue (ferrersDropLastColumns C) (t - 1) := by
  unfold ferrersShiFactorValue
  rw [ferrersBaseFactor_dropLast_of_mem C t htop,
    ferrersLinearProduct_dropLast_of_mem C t htop]
  ring

end

end DeformationMatrix

end CyclicBraidArrangement
