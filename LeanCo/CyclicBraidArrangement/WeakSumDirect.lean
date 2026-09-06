import LeanCo.CyclicBraidArrangement.WeakSumConverse
import Mathlib.Logic.Equiv.Fintype

namespace CyclicBraidArrangement

open scoped BigOperators

namespace WeakSumConverse

/-- The local identity obtained by swapping two adjacent vertices in a tour. -/
def AdjacentSwapIdentity {n : ℕ} (D : Fin n → Fin n → ℝ) : Prop :=
  ∀ a b c d, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    D a b + D b c + D c d = D a c + D c b + D b d

/-- Vanishing alternating sums on every off-diagonal bipartite rectangle. -/
def RectangleIdentity {n : ℕ} (D : Fin n → Fin n → ℝ) : Prop :=
  ∀ i k j l, i ≠ k → j ≠ l → i ≠ j → i ≠ l → k ≠ j → k ≠ l →
    D i j + D k l = D i l + D k j

/-- Equality of total sums localizes to three exceptional coordinates. -/
lemma sum_three_eq_of_sum_eq_of_eq_off
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p q r : ι) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (f g : ι → ℝ) (hsum : ∑ i, f i = ∑ i, g i)
    (hoff : ∀ i, i ≠ p → i ≠ q → i ≠ r → f i = g i) :
    f p + f q + f r = g p + g q + g r := by
  classical
  let s : Finset ι := ((Finset.univ.erase p).erase q).erase r
  have hp : p ∈ (Finset.univ : Finset ι) := Finset.mem_univ p
  have hq : q ∈ (Finset.univ.erase p : Finset ι) := by simp [hpq.symm]
  have hr : r ∈ ((Finset.univ.erase p).erase q : Finset ι) := by
    simp [hpr.symm, hqr.symm]
  have hrest : ∑ i ∈ s, f i = ∑ i ∈ s, g i := by
    apply Finset.sum_congr rfl
    intro i hi
    apply hoff i
    · intro hip; subst i; simp [s] at hi
    · intro hiq; subst i; simp [s] at hi
    · intro hir; subst i; simp [s] at hi
  have hf : (∑ i, f i) = f p + f q + f r + ∑ i ∈ s, f i := by
    change Finset.univ.sum f = _
    have hp' := Finset.sum_erase_add Finset.univ f hp
    have hq' := Finset.sum_erase_add (Finset.univ.erase p) f hq
    have hr' := Finset.sum_erase_add ((Finset.univ.erase p).erase q) f hr
    dsimp [s]
    linarith
  have hg : (∑ i, g i) = g p + g q + g r + ∑ i ∈ s, g i := by
    change Finset.univ.sum g = _
    have hp' := Finset.sum_erase_add Finset.univ g hp
    have hq' := Finset.sum_erase_add (Finset.univ.erase p) g hq
    have hr' := Finset.sum_erase_add ((Finset.univ.erase p).erase q) g hr
    dsimp [s]
    linarith
  linarith

/-- Constancy of Hamiltonian tour weights gives the adjacent-swap identity. -/
theorem adjacentSwapIdentity_of_constant_hamiltonian_weight
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (D : Fin n → Fin n → ℝ)
    (hconst : ∀ a b : DeformationMatrix.CyclicOrdering n,
      additiveCycleWeight D a = additiveCycleWeight D b) :
    AdjacentSwapIdentity D := by
  classical
  intro a b c d hab hac had hbc hbd hcd
  let pos : Fin 4 → Fin n := Fin.castLE hn
  let target : Fin 4 → Fin n := ![a, b, c, d]
  have hpos : Function.Injective pos := by
    exact Fin.castLE_injective hn
  have htarget : Function.Injective target := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [target]
  obtain ⟨w, hw⟩ := Equiv.Perm.exists_extending_pair pos target hpos htarget
  let p0 : Fin n := pos 0
  let p1 : Fin n := pos 1
  let p2 : Fin n := pos 2
  let p3 : Fin n := pos 3
  have hp01 : p0 ≠ p1 := by simp [p0, p1, pos, Fin.castLE]
  have hp02 : p0 ≠ p2 := by simp [p0, p2, pos, Fin.castLE]
  have hp12 : p1 ≠ p2 := by simp [p1, p2, pos, Fin.castLE]
  have hp13 : p1 ≠ p3 := by simp [p1, p3, pos, Fin.castLE]
  have hp23 : p2 ≠ p3 := by simp [p2, p3, pos, Fin.castLE]
  have hp0v : p0.val = 0 := by simp [p0, pos, Fin.castLE]
  have hp1v : p1.val = 1 := by simp [p1, pos, Fin.castLE]
  have hp2v : p2.val = 2 := by simp [p2, pos, Fin.castLE]
  have hp3v : p3.val = 3 := by simp [p3, pos, Fin.castLE]
  have honev : ((1 : Fin n).val) = 1 := by
    change 1 % n = 1
    exact Nat.mod_eq_of_lt (by omega)
  have hnext0 : DeformationMatrix.nextPosition n p0 = p1 := by
    apply Fin.ext
    change (p0 + 1).val = p1.val
    rw [Fin.val_add_eq_of_add_lt]
    · rw [hp0v, hp1v, honev]
    · rw [hp0v, honev]
      omega
  have hnext1 : DeformationMatrix.nextPosition n p1 = p2 := by
    apply Fin.ext
    change (p1 + 1).val = p2.val
    rw [Fin.val_add_eq_of_add_lt]
    · rw [hp1v, hp2v, honev]
    · rw [hp1v, honev]
      omega
  have hnext2 : DeformationMatrix.nextPosition n p2 = p3 := by
    apply Fin.ext
    change (p2 + 1).val = p3.val
    rw [Fin.val_add_eq_of_add_lt]
    · rw [hp2v, hp3v, honev]
    · rw [hp2v, honev]
      omega
  have hw0 : w p0 = a := by simpa [p0, pos, target] using hw 0
  have hw1 : w p1 = b := by simpa [p1, pos, target] using hw 1
  have hw2 : w p2 = c := by simpa [p2, pos, target] using hw 2
  have hw3 : w p3 = d := by simpa [p3, pos, target] using hw 3
  let sw : Equiv.Perm (Fin n) := Equiv.swap p1 p2
  let w' : DeformationMatrix.CyclicOrdering n := sw.trans w
  have hsw0 : sw p0 = p0 := by
    exact Equiv.swap_apply_of_ne_of_ne hp01 hp02
  have hsw1 : sw p1 = p2 := by simp [sw]
  have hsw2 : sw p2 = p1 := by simp [sw]
  have hsw3 : sw p3 = p3 := by
    exact Equiv.swap_apply_of_ne_of_ne hp13.symm hp23.symm
  have hsum :
      (∑ k, D (w k) (w (DeformationMatrix.nextPosition n k))) =
        ∑ k, D (w' k) (w' (DeformationMatrix.nextPosition n k)) := by
    simpa only [additiveCycleWeight] using hconst w w'
  have hoff : ∀ k, k ≠ p0 → k ≠ p1 → k ≠ p2 →
      D (w k) (w (DeformationMatrix.nextPosition n k)) =
        D (w' k) (w' (DeformationMatrix.nextPosition n k)) := by
    intro k hk0 hk1 hk2
    have hn1 : DeformationMatrix.nextPosition n k ≠ p1 := by
      intro heq
      have := (DeformationMatrix.nextPosition n).injective
      exact hk0 (this (heq.trans hnext0.symm))
    have hn2 : DeformationMatrix.nextPosition n k ≠ p2 := by
      intro heq
      have := (DeformationMatrix.nextPosition n).injective
      exact hk1 (this (heq.trans hnext1.symm))
    simp [w', sw, Equiv.trans_apply,
      Equiv.swap_apply_of_ne_of_ne hk1 hk2,
      Equiv.swap_apply_of_ne_of_ne hn1 hn2]
  have hlocal := sum_three_eq_of_sum_eq_of_eq_off p0 p1 p2 hp01 hp02 hp12
    (fun k ↦ D (w k) (w (DeformationMatrix.nextPosition n k)))
    (fun k ↦ D (w' k) (w' (DeformationMatrix.nextPosition n k))) hsum hoff
  simpa [w', sw, Equiv.trans_apply, hnext0, hnext1, hnext2,
    hw0, hw1, hw2, hw3, hp01, hp02, hp12, hp13, hp23,
    hp01.symm, hp02.symm, hp12.symm, hp13.symm, hp23.symm,
    hsw0, hsw1, hsw2, hsw3] using hlocal

/-- Three adjacent-swap equations give one rectangle equation. -/
theorem rectangleIdentity_of_adjacentSwapIdentity
    {n : ℕ} (D : Fin n → Fin n → ℝ) (hD : AdjacentSwapIdentity D) :
    RectangleIdentity D := by
  intro i k j l hik hjl hij hil hkj hkl
  have h₁ := hD i k j l hik hij hil hkj hkl hjl
  have h₂ := hD i k l j hik hil hij hkl hkj hjl.symm
  have h₃ := hD i j l k hij hil hik hjl hkj.symm hkl.symm
  linarith

lemma exists_avoiding_three {n : ℕ} (hn : 3 < n) (a b c : Fin n) :
    ∃ d : Fin n, d ≠ a ∧ d ≠ b ∧ d ≠ c := by
  classical
  by_contra h
  push Not at h
  have hu : (Finset.univ : Finset (Fin n)) ⊆ {a, b, c} := by
    intro d hd
    by_cases hda : d = a
    · simp [hda]
    by_cases hdb : d = b
    · simp [hdb]
    have hdc : d = c := h d hda hdb
    simp [hdc]
  have hc := Finset.card_le_card hu
  have hthree : ({a, b, c} : Finset (Fin n)).card ≤ 3 := by
    calc
      ({a, b, c} : Finset (Fin n)).card ≤ ({b, c} : Finset (Fin n)).card + 1 :=
        Finset.card_insert_le _ _
      _ ≤ ({c} : Finset (Fin n)).card + 1 + 1 := by
        have hbc : ({b, c} : Finset (Fin n)).card ≤
            ({c} : Finset (Fin n)).card + 1 := Finset.card_insert_le _ _
        omega
      _ ≤ 3 := by simp
  simp only [Finset.card_univ, Fintype.card_fin] at hc
  omega

/-- Rectangle identities on the loop-free arc set construct row and column
potentials directly. -/
theorem weakSum_of_rectangleIdentity {n : ℕ} [NeZero n] (hn : 4 ≤ n)
    (D : Fin n → Fin n → ℝ) (hD : RectangleIdentity D) : IsWeakSum D := by
  classical
  let a : Fin n := 0
  choose c hc using fun i : Fin n ↦
    Fin.exists_ne_and_ne_of_two_lt a i (show 2 < n by omega)
  have hca (i : Fin n) : c i ≠ a := (hc i).1
  have hci (i : Fin n) : c i ≠ i := (hc i).2
  let ρ : Fin n → ℝ := fun i ↦ if i = a then 0 else D i (c i) - D a (c i)
  have hmain (i j : Fin n) (hia : i ≠ a) (hja : j ≠ a) (hij : i ≠ j) :
      D i j = ρ i + D a j := by
    by_cases hjc : j = c i
    · subst j
      simp [ρ, hia]
    · have hr := hD i a j (c i) hia hjc hij (hci i).symm hja.symm (hca i).symm
      simp only [ρ, if_neg hia]
      linarith
  let b : Fin n := c a
  have hba : b ≠ a := hca a
  let γ : Fin n → ℝ := fun j ↦ if j = a then D b a - ρ b else D a j
  refine ⟨ρ, γ, ?_⟩
  intro i j hij
  by_cases hia : i = a
  · subst i
    simp [ρ, γ, hij.symm]
  by_cases hja : j = a
  · subst j
    by_cases hib : i = b
    · subst i
      simp [γ]
    · obtain ⟨l, hla, hli, hlb⟩ :=
        exists_avoiding_three (show 3 < n by omega) a i b
      have hil : i ≠ l := hli.symm
      have hbl : b ≠ l := hlb.symm
      have hrect := hD i b a l hib hla.symm hia hil hba hbl
      have hi := hmain i l hia hla hil
      have hb := hmain b l hba hla hbl
      simp only [γ, if_pos rfl]
      linarith
  · rw [hmain i j hia hja hij]
    simp [γ, hja]

/-- For at least four vertices, constant tour weight implies weak row-plus-column form. -/
theorem weakSum_of_constant_hamiltonian_weight_ge_four
    {n : ℕ} [NeZero n] (hn : 4 ≤ n) (D : Fin n → Fin n → ℝ)
    (hconst : ∀ a b : DeformationMatrix.CyclicOrdering n,
      additiveCycleWeight D a = additiveCycleWeight D b) : IsWeakSum D := by
  apply weakSum_of_rectangleIdentity hn D
  apply rectangleIdentity_of_adjacentSwapIdentity D
  exact adjacentSwapIdentity_of_constant_hamiltonian_weight hn D hconst

/-- Every loop-free two-by-two matrix is weak row-plus-column. -/
theorem weakSum_fin_two (D : Fin 2 → Fin 2 → ℝ) : IsWeakSum D := by
  refine ⟨![D 0 1, D 1 0], fun _ ↦ 0, ?_⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

/-- On three vertices, equality of the two oriented cycle weights gives weak-sum form. -/
theorem weakSum_fin_three_of_constant
    (D : Fin 3 → Fin 3 → ℝ)
    (hconst : ∀ a b : DeformationMatrix.CyclicOrdering 3,
      additiveCycleWeight D a = additiveCycleWeight D b) : IsWeakSum D := by
  have hcycle := hconst (Equiv.refl (Fin 3)) (Equiv.swap (1 : Fin 3) 2)
  simp [additiveCycleWeight, DeformationMatrix.nextPosition,
    Equiv.swap_apply_def, Fin.sum_univ_succ] at hcycle
  refine ⟨![0, D 1 2 - D 0 2, D 2 1 - D 0 1],
    ![D 1 0 - D 1 2 + D 0 2, D 0 1, D 0 2], ?_⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all
  all_goals linarith

/-- Direct characterization of constant Hamiltonian-cycle weights, with no
external affine-hull premise. -/
theorem constant_hamiltonian_weight_iff_weakSum_direct
    {n : ℕ} [NeZero n] (hn : 2 ≤ n) (D : Fin n → Fin n → ℝ) :
    (∀ a b : DeformationMatrix.CyclicOrdering n,
      additiveCycleWeight D a = additiveCycleWeight D b) ↔ IsWeakSum D := by
  constructor
  · intro hconst
    rcases Nat.eq_or_lt_of_le hn with h2 | hn2
    · subst n
      exact weakSum_fin_two D
    · by_cases h3 : n = 3
      · subst n
        exact weakSum_fin_three_of_constant D hconst
      · exact weakSum_of_constant_hamiltonian_weight_ge_four
          (show 4 ≤ n by omega) D hconst
  · intro hD a b
    rcases hD with ⟨ρ, γ, hD⟩
    have weight_eq (w : DeformationMatrix.CyclicOrdering n) :
        additiveCycleWeight D w = (∑ i, ρ i) + ∑ i, γ i := by
      have hadj : ∀ k, w k ≠ w (DeformationMatrix.nextPosition n k) :=
        fun k ↦ w.injective.ne
          (DeformationMatrix.nextPosition_ne_self hn k).symm
      simp_rw [additiveCycleWeight, hD _ _ (hadj _),
        Finset.sum_add_distrib]
      rw [Equiv.sum_comp w ρ]
      simpa only [Equiv.trans_apply] using congrArg
        (fun z ↦ (∑ i, ρ i) + z)
        (Equiv.sum_comp ((DeformationMatrix.nextPosition n).trans w) γ)
    rw [weight_eq a, weight_eq b]

/-- Direct matrix-difference form of the constant-cycle characterization. -/
theorem cycleWeight_difference_constant_iff_weakSum_direct
    {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (M N : Fin n → Fin n → ℝ) :
    (∀ a b : DeformationMatrix.CyclicOrdering n,
      additiveCycleWeight N a - additiveCycleWeight M a =
        additiveCycleWeight N b - additiveCycleWeight M b) ↔
      IsWeakSum (fun i j ↦ N i j - M i j) := by
  rw [← constant_hamiltonian_weight_iff_weakSum_direct hn]
  constructor
  · intro h a b
    simpa only [additiveCycleWeight_sub] using h a b
  · intro h a b
    simpa only [additiveCycleWeight_sub] using h a b

end WeakSumConverse
end CyclicBraidArrangement
