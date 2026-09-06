import LeanCo.CyclicBraidArrangement.ArrangementCharacteristic

/-!
# Agreement with the paper's signed interval arrangement

The core arrangement module uses oriented nonnegative equations.  Here that
encoding is proved equivalent to the paper's literal equations
`x_i - x_j = s` with `-m_ij ≤ s ≤ m_ji` for `i < j`.
-/

namespace CyclicBraidArrangement

namespace DeformationMatrix

variable {n : ℕ}

/-- Literal complement predicate for the signed interval arrangement in
Definition 1.1, after base change to a commutative ring. -/
def AvoidsPaperArrangement (M : DeformationMatrix n)
    {R : Type*} [CommRing R] (x : Fin n → R) : Prop :=
  ∀ i j : Fin n, i.val < j.val → ∀ s : ℤ,
    -(M.entry i j : ℤ) ≤ s → s ≤ (M.entry j i : ℤ) →
      x i - x j ≠ (s : R)

/-- The oriented forbidden-equation encoding is exactly the paper's signed
interval encoding. -/
theorem avoidsEveryForbiddenEquation_iff_avoidsPaperArrangement
    (M : DeformationMatrix n) {R : Type*} [CommRing R]
    (x : Fin n → R) :
    (∀ e : M.ForbiddenEquation, ¬ M.SatisfiesEquation x e) ↔
      M.AvoidsPaperArrangement x := by
  constructor
  · intro hord i j hij s hlo hhi hEq
    by_cases hs : 0 ≤ s
    · let r : ℕ := s.toNat
      have hrs : (r : ℤ) = s := Int.toNat_of_nonneg hs
      have hr : r ≤ M.entry j i := by
        exact_mod_cast hrs.trans_le hhi
      let e : M.ForbiddenEquation :=
        ⟨j, ⟨⟨i, by omega⟩, ⟨r, Nat.lt_succ_of_le hr⟩⟩⟩
      apply hord e
      unfold SatisfiesEquation
      change x i - x j = (r : R)
      have hrsR := congrArg (fun z : ℤ ↦ (z : R)) hrs
      push_cast at hrsR
      exact hEq.trans hrsR.symm
    · have hsneg : s < 0 := lt_of_not_ge hs
      let r : ℕ := (-s).toNat
      have hrs : (r : ℤ) = -s := Int.toNat_of_nonneg (by omega)
      have hr : r ≤ M.entry i j := by
        exact_mod_cast (show (r : ℤ) ≤ (M.entry i j : ℤ) by rw [hrs]; omega)
      let e : M.ForbiddenEquation :=
        ⟨i, ⟨⟨j, by omega⟩, ⟨r, Nat.lt_succ_of_le hr⟩⟩⟩
      apply hord e
      unfold SatisfiesEquation
      change x j - x i = (r : R)
      have hneg := congrArg Neg.neg hEq
      rw [neg_sub, ← Int.cast_neg, ← hrs] at hneg
      simpa [e] using hneg
  · intro hpaper e heq
    rcases lt_or_gt_of_ne (e.source_ne_target M) with hlt | hgt
    · have hd : (e.distance M : ℤ) ≤
          (M.entry (e.source M) (e.target M) : ℤ) := by
        exact_mod_cast e.distance_le M
      have hforbid := hpaper (e.source M) (e.target M) hlt
        (-(e.distance M : ℤ)) (by omega) (by omega)
      apply hforbid
      unfold SatisfiesEquation at heq
      calc
        x (e.source M) - x (e.target M) =
            -(x (e.target M) - x (e.source M)) := by abel
        _ = -((e.distance M : ℕ) : R) := congrArg Neg.neg heq
        _ = ((-(e.distance M : ℤ) : ℤ) : R) := by simp
    · have hforbid := hpaper (e.target M) (e.source M) hgt
        (e.distance M : ℤ) (by omega)
        (by exact_mod_cast (e.distance_le M))
      apply hforbid
      unfold SatisfiesEquation at heq
      simpa using heq

/-- Membership in the genuine finite-ring complement is the literal paper
arrangement-complement predicate. -/
theorem finiteFieldComplement_iff_avoidsPaperArrangement
    (M : DeformationMatrix n) {R : Type*} [CommRing R]
    (x : Fin n → R) :
    (∀ e : M.ForbiddenEquation, ¬ M.SatisfiesEquation x e) ↔
      M.AvoidsPaperArrangement x :=
  M.avoidsEveryForbiddenEquation_iff_avoidsPaperArrangement x

end DeformationMatrix

end CyclicBraidArrangement
