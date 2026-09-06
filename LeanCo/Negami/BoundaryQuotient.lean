import LeanCo.Negami.BoundaryGluing

/-! The boundary quotient identity of Section 5. -/

namespace LeanCo.Negami

open scoped BigOperators

namespace BoundaryData

variable {P : Type} [Fintype P] [DecidableEq P]

/-- Degree contributed by a state of boundary type `π` after imposing the
identifications described by `α`. -/
noncomputable def quotientDegree (K : BoundaryData P) (ρ : P → P → ℕ)
    (α : P) (S : Finset K.Edge) : Degree →₀ ℕ :=
  Finsupp.single 0 (K.internalComponents S + ρ α (K.boundaryType S)) +
    Finsupp.single 1 S.card +
    Finsupp.single 2 (Nat.card K.Edge - S.card)

/-- Right-hand side of the boundary quotient identity, before grouping states
with the same boundary partition. -/
noncomputable def quotientStateSum (K : BoundaryData P) (ρ : P → P → ℕ)
    (α : P) (R : Type*) [CommSemiring R] : MvPolynomial Degree R :=
  ∑ S : Finset K.Edge, MvPolynomial.monomial (quotientDegree K ρ α S) 1

/-- State-preserving realization of the graph quotient `K/α`. -/
structure Quotient (K : BoundaryData P) (Q : NegamiData)
    (ρ : P → P → ℕ) (α : P) where
  states : Finset Q.Edge ≃ Finset K.Edge
  selected_card : ∀ S : Finset Q.Edge, S.card = (states S).card
  edge_card : Nat.card Q.Edge = Nat.card K.Edge
  componentEquiv : ∀ S : Finset Q.Edge,
    Fin (Q.components S) ≃
      Fin (K.internalComponents (states S)) ⊕
        Fin (ρ α (K.boundaryType (states S)))

/-- The quotient component count follows from its decomposition into internal
components and generated boundary blocks. -/
theorem Quotient.component_formula {K : BoundaryData P} {Q : NegamiData}
    {ρ : P → P → ℕ} {α : P} (W : Quotient K Q ρ α)
    (S : Finset Q.Edge) :
    Q.components S = K.internalComponents (W.states S) +
      ρ α (K.boundaryType (W.states S)) := by
  have h := Fintype.card_congr (W.componentEquiv S)
  simpa only [Fintype.card_fin, Fintype.card_sum] using h

theorem Quotient.degree_eq {K : BoundaryData P} {Q : NegamiData}
    {ρ : P → P → ℕ} {α : P} (W : Quotient K Q ρ α)
    (S : Finset Q.Edge) :
    Q.degree S = quotientDegree K ρ α (W.states S) := by
  classical
  have hK : (W.states S).card ≤ Nat.card K.Edge := by
    simpa only [Nat.card_eq_fintype_card] using Finset.card_le_univ (W.states S)
  ext i
  fin_cases i <;> simp [NegamiData.degree, quotientDegree, W.component_formula,
    W.selected_card, W.edge_card, -Nat.card_eq_fintype_card]

/-- Lemma 5.1: the polynomial of `K/α` is the boundary-state sum weighted by
`t ^ ρ(α,π)`.  `quotientStateSum` is definitionally the same sum with states
listed before grouping by `π`. -/
theorem polynomial_quotient {K : BoundaryData P} {Q : NegamiData}
    {ρ : P → P → ℕ} {α : P} (W : Quotient K Q ρ α)
    (R : Type*) [CommSemiring R] :
    Q.polynomial R = quotientStateSum K ρ α R := by
  classical
  rw [NegamiData.polynomial, quotientStateSum]
  exact Fintype.sum_equiv W.states _ _ fun S ↦ by rw [W.degree_eq S]

end BoundaryData
end LeanCo.Negami
