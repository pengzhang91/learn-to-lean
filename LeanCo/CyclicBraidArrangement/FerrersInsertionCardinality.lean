import LeanCo.CyclicBraidArrangement.FerrersInsertionEquivalence
import LeanCo.CyclicBraidArrangement.FerrersRecurrenceAlgebra

/-!
# Cardinal induction for Ferrers cyclic insertion

The safety-sensitive deletion/insertion maps live in
`FerrersInsertionEquivalence`.  This file consumes only their equivalence
interfaces and performs the remaining cardinal and product induction.
-/

namespace CyclicBraidArrangement

open scoped BigOperators

namespace DeformationMatrix

noncomputable section

theorem card_sigma_ferrersUnusedSlot {n q : ℕ} [NeZero n] [NeZero q]
    (C : Finset (Fin n)) :
    Fintype.card
        (Σ p : AnchoredFerrersBoxPlacement (n := n) (q := q) C,
          FerrersUnusedSlot C p) =
      (q - n) *
        Fintype.card (AnchoredFerrersBoxPlacement (n := n) (q := q) C) := by
  rw [Fintype.card_sigma]
  simp_rw [card_ferrersUnusedSlot]
  simp [mul_comm]

theorem ferrersColumns_fin_one_eq_empty (C : Finset (Fin 1))
    (hzero : (0 : Fin 1) ∉ C) : C = ∅ := by
  ext i
  fin_cases i
  simp [hzero]

/-- There is exactly one anchored Ferrers placement in rank one whenever
the unique label is not selected. -/
theorem card_anchoredFerrersBoxPlacement_fin_one
    (q : ℕ) [NeZero q] (C : Finset (Fin 1))
    (hzero : (0 : Fin 1) ∉ C) :
    Fintype.card
        (AnchoredFerrersBoxPlacement (n := 1) (q := q) C) = 1 := by
  classical
  have hC := ferrersColumns_fin_one_eq_empty C hzero
  subst C
  let e0 : Fin 1 ↪ Fin q :=
    ⟨fun _ ↦ 0, fun a b _ ↦ Subsingleton.elim a b⟩
  let p0 : AnchoredFerrersBoxPlacement (n := 1) (q := q) ∅ :=
    ⟨e0, rfl, by simp⟩
  letI : Unique
      (AnchoredFerrersBoxPlacement (n := 1) (q := q) ∅) :=
    { default := p0
      uniq := by
        intro p
        apply Subtype.ext
        apply Function.Embedding.ext
        intro i
        have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
        subst i
        exact p.2.1 }
  exact Fintype.card_unique

/-- A cardinal equality for the box model canonically supplies the concrete
insertion equivalence required by `FerrersInsertionEquivalence`. -/
theorem nonempty_ferrersInsertionEquiv_of_card_eq
    {n q : ℕ} [NeZero n] [NeZero q]
    (C : Finset (Fin n))
    (hcard : Fintype.card
        (AnchoredFerrersBoxPlacement (n := n) (q := q) C) =
      Fintype.card (FerrersInsertionData q C)) :
    Nonempty
      ((graphicalShi (ferrersGraph C)).AnchoredFiniteFieldComplement
          (ZMod q) ≃ FerrersInsertionData q C) := by
  exact ⟨(anchoredFerrersComplementEquivBox C).trans
    (Fintype.equivOfCardEq hcard)⟩

theorem card_anchored_eq_insertionData_of_factorValue_eq
    {n q : ℕ} [NeZero n] [NeZero q]
    (C : Finset (Fin n)) (hzero : (0 : Fin n) ∉ C) (hq : n ≤ q)
    (hfactor : ferrersShiFactorValue C q =
      (Fintype.card
        (AnchoredFerrersBoxPlacement (n := n) (q := q) C) : ℚ)) :
    Fintype.card
        (AnchoredFerrersBoxPlacement (n := n) (q := q) C) =
      Fintype.card (FerrersInsertionData q C) := by
  have hdata := ferrersShiFactorValue_natCast_eq_card q C hzero hq
  exact_mod_cast hfactor.symm.trans hdata

/-- Packaging a uniform placement-cardinality proof gives the exact
insertion-equivalence interface used by the factorization theorem. -/
theorem ferrersInsertionEquivalence_of_card_eq
    (hcard : ∀ {n : ℕ} [NeZero n] (C : Finset (Fin n)),
      (0 : Fin n) ∉ C → ∀ (q : ℕ) [NeZero q], n ≤ q →
        Fintype.card
            (AnchoredFerrersBoxPlacement (n := n) (q := q) C) =
          Fintype.card (FerrersInsertionData q C)) :
    FerrersInsertionEquivalence := by
  intro n hn C hzero q hqInst hq
  exact nonempty_ferrersInsertionEquiv_of_card_eq C
    (hcard C hzero q hq)

end

end DeformationMatrix

end CyclicBraidArrangement
