import LeanCo.PackingEdgeColoring.GoodColoring

/-!
# Canonical representatives under induced-colour symmetry

The paper repeatedly says "by symmetry" before reducing the colours on two
distinguished edges to five cases.  These lemmas make that reduction explicit:
the matching colour is fixed and a permutation of the induced palette sends
any ordered pair to one of the five advertised representatives.
-/

namespace LeanCo.PackingEdgeColoring

noncomputable section

/-- Two distinct members of a palette with at least two colours can be sent
to `0` and `1` by a palette permutation; equal members are both sent to `0`. -/
theorem exists_perm_normalizing_two {n : ℕ} (i j : Fin (n + 2)) :
    ∃ σ : Equiv.Perm (Fin (n + 2)),
      σ i = 0 ∧ (i = j → σ j = 0) ∧ (i ≠ j → σ j = 1) := by
  classical
  let τ : Equiv.Perm (Fin (n + 2)) := Equiv.swap i 0
  by_cases hij : i = j
  · refine ⟨τ, ?_, ?_, ?_⟩
    · exact Equiv.swap_apply_left i 0
    · intro h
      subst j
      exact Equiv.swap_apply_left i 0
    · exact fun h ↦ False.elim (h hij)
  · let j' : Fin (n + 2) := τ j
    have hτi : τ i = 0 := Equiv.swap_apply_left i 0
    have hj'0 : j' ≠ 0 := by
      intro hj
      apply hij
      apply τ.injective
      simpa [j', hj, hτi]
    let υ : Equiv.Perm (Fin (n + 2)) := Equiv.swap j' 1
    have hυ0 : υ 0 = 0 := by
      exact Equiv.swap_apply_of_ne_of_ne hj'0.symm (by simp)
    refine ⟨υ * τ, ?_, ?_, ?_⟩
    · rw [Equiv.Perm.mul_apply, hτi, hυ0]
    · intro h
      exact False.elim (hij h)
    · intro _
      change υ (τ j) = 1
      exact Equiv.swap_apply_left j' 1

/-- The five ordered-pair normal forms used throughout both colouring
arguments. -/
def IsCanonicalColorPair {n : ℕ}
    (a b : OneTwoColor (n + 2)) : Prop :=
  (a = none ∧ b = none) ∨
  (a = none ∧ b = some 0) ∨
  (a = some 0 ∧ b = none) ∨
  (a = some 0 ∧ b = some 0) ∨
  (a = some 0 ∧ b = some 1)

/-- Every ordered pair of semantic colours has a canonical representative
after permuting only the induced palette. -/
theorem exists_permuteInducedColor_canonical_pair {n : ℕ}
    (a b : OneTwoColor (n + 2)) :
    ∃ σ : Equiv.Perm (Fin (n + 2)),
      IsCanonicalColorPair (permuteInducedColor σ a)
        (permuteInducedColor σ b) := by
  classical
  cases a with
  | none =>
      cases b with
      | none =>
          exact ⟨1, Or.inl ⟨rfl, rfl⟩⟩
      | some j =>
          let σ : Equiv.Perm (Fin (n + 2)) := Equiv.swap j 0
          refine ⟨σ, Or.inr (Or.inl ⟨rfl, ?_⟩)⟩
          change some (σ j) = some 0
          rw [Equiv.swap_apply_left]
  | some i =>
      cases b with
      | none =>
          let σ : Equiv.Perm (Fin (n + 2)) := Equiv.swap i 0
          refine ⟨σ, Or.inr (Or.inr (Or.inl ⟨?_, rfl⟩))⟩
          change some (σ i) = some 0
          rw [Equiv.swap_apply_left]
      | some j =>
          obtain ⟨σ, hσi, hsame, hdiff⟩ :=
            exists_perm_normalizing_two i j
          by_cases hij : i = j
          · refine ⟨σ, Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, ?_⟩)))⟩
            · exact congrArg some hσi
            · exact congrArg some (hsame hij)
          · refine ⟨σ, Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩)))⟩
            · exact congrArg some hσi
            · exact congrArg some (hdiff hij)

/-- Good-five colourings may be normalized to the five pair cases without
changing goodness. -/
theorem GoodFive.exists_permuted_canonical_pair
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {colour : G.edgeSet → OneTwoColor 5} (hgood : GoodFive G colour)
    (e f : G.edgeSet) :
    ∃ σ : Equiv.Perm (Fin 5),
      GoodFive G (permuteInducedColors G σ colour) ∧
      IsCanonicalColorPair
        (permuteInducedColors G σ colour e)
        (permuteInducedColors G σ colour f) := by
  obtain ⟨σ, hcanon⟩ :=
    exists_permuteInducedColor_canonical_pair (colour e) (colour f)
  exact ⟨σ, (goodFive_permute_iff G σ colour).mpr hgood, hcanon⟩

/-- The analogous normalization for good-four colourings. -/
theorem GoodFour.exists_permuted_canonical_pair
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {colour : G.edgeSet → OneTwoColor 4} (hgood : GoodFour G colour)
    (e f : G.edgeSet) :
    ∃ σ : Equiv.Perm (Fin 4),
      GoodFour G (permuteInducedColors G σ colour) ∧
      IsCanonicalColorPair
        (permuteInducedColors G σ colour e)
        (permuteInducedColors G σ colour f) := by
  obtain ⟨σ, hcanon⟩ :=
    exists_permuteInducedColor_canonical_pair (colour e) (colour f)
  exact ⟨σ, (goodFour_permute_iff G σ colour).mpr hgood, hcanon⟩

end

end LeanCo.PackingEdgeColoring
