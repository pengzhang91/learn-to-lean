import LeanCo.Negami.BoundaryGluing

/-!
# The categorical boundary pairing

This is the literal graded-object form of Theorem 4.5.  Boundary states are
grouped by their induced partition, paired by a one-dimensional object in
degree `rho(pi,sigma)`, and then summed over both partitions.  A gluing witness
supplies a degree-preserving equivalence from the state object of the glued
graph to this direct sum.
-/

open scoped BigOperators

namespace LeanCo.Negami
namespace BoundaryData

variable {P : Type} [Fintype P] [DecidableEq P]

/-- The boundary-state object `N_{U,pi}(K)` from Definition 4.4. -/
noncomputable abbrev boundaryObject (K : BoundaryData P) (π : P) : GradedObject := {
  Basis := {S : Finset K.Edge // K.boundaryType S = π}
  fintypeBasis := inferInstance
  degree := fun S =>
    ⟨K.internalComponents S.1, S.1.card, Nat.card K.Edge - S.1.card⟩
}

/-- The one-dimensional pairing object `Theta_{pi,sigma}` from Section 7. -/
noncomputable abbrev thetaObject (ρ : P → P → ℕ) (π σ : P) : GradedObject := {
  Basis := Unit
  fintypeBasis := inferInstance
  degree := fun _ => ⟨ρ π σ, 0, 0⟩
}

/-- Entry of the categorical Gram pairing.  Tensoring with the one-dimensional
`thetaObject` is represented equivalently by its grading shift. -/
noncomputable abbrev matrixEntryObject (K H : BoundaryData P)
    (ρ : P → P → ℕ) (π σ : P) : GradedObject :=
  GradedObject.shift ⟨ρ π σ, 0, 0⟩
    (GradedObject.tensor (K.boundaryObject π) (H.boundaryObject σ))

/-- The direct sum over all pairs of boundary partitions in Equation (4.7). -/
noncomputable abbrev categoricalPairing (K H : BoundaryData P)
    (ρ : P → P → ℕ) : GradedObject :=
  GradedObject.sigma (fun p : P × P =>
    matrixEntryObject K H ρ p.1 p.2)

omit [Fintype P] [DecidableEq P] in
theorem hilbert_thetaObject {R : Type*} [CommSemiring R]
    (ρ : P → P → ℕ) (π σ : P) (t x y : R) :
    (thetaObject ρ π σ).hilbert t x y = t ^ ρ π σ := by
  simp [GradedObject.hilbert, thetaObject, gradeWeight]

/-- Entrywise decategorification of the categorical Gram pairing. -/
theorem hilbert_categoricalPairing {R : Type*} [CommSemiring R]
    (K H : BoundaryData P) (ρ : P → P → ℕ) (t x y : R) :
    (categoricalPairing K H ρ).hilbert t x y =
      ∑ p : P × P, t ^ ρ p.1 p.2 *
        (K.boundaryObject p.1).hilbert t x y *
        (H.boundaryObject p.2).hilbert t x y := by
  rw [GradedObject.hilbert_sigma]
  apply Finset.sum_congr rfl
  intro p _
  rw [GradedObject.hilbert_shift, GradedObject.hilbert_tensor]
  simp [gradeWeight, mul_assoc]

private noncomputable def boundaryFiberEquiv (K H : BoundaryData P) (p : P × P) :
    {z : Finset K.Edge × Finset H.Edge //
      (K.boundaryType z.1, H.boundaryType z.2) = p} ≃
      ({S : Finset K.Edge // K.boundaryType S = p.1} ×
        {S : Finset H.Edge // H.boundaryType S = p.2}) where
  toFun z :=
    (⟨z.1.1, congrArg Prod.fst z.2⟩, ⟨z.1.2, congrArg Prod.snd z.2⟩)
  invFun z := ⟨(z.1.1, z.2.1), Prod.ext z.1.2 z.2.2⟩
  left_inv z := by ext <;> rfl
  right_inv z := by ext <;> rfl

/-- Regroup the state-pair bijection by the two induced boundary partitions. -/
noncomputable def Gluing.categoricalStateEquiv {G : NegamiData}
    {K H : BoundaryData P} {ρ : P → P → ℕ} (W : Gluing G K H ρ) :
    Finset G.Edge ≃ (categoricalPairing K H ρ).Basis :=
  W.states |>.trans
    ((Equiv.sigmaFiberEquiv
      (fun z : Finset K.Edge × Finset H.Edge =>
        (K.boundaryType z.1, H.boundaryType z.2))).symm |>.trans
      (Equiv.sigmaCongrRight (boundaryFiberEquiv K H)))

@[simp] theorem Gluing.categoricalStateEquiv_left {G : NegamiData}
    {K H : BoundaryData P} {ρ : P → P → ℕ} (W : Gluing G K H ρ)
    (S : Finset G.Edge) :
    (W.categoricalStateEquiv S).2.1.1 = (W.states S).1 := by
  rfl

@[simp] theorem Gluing.categoricalStateEquiv_right {G : NegamiData}
    {K H : BoundaryData P} {ρ : P → P → ℕ} (W : Gluing G K H ρ)
    (S : Finset G.Edge) :
    (W.categoricalStateEquiv S).2.2.1 = (W.states S).2 := by
  rfl

@[simp] theorem Gluing.categoricalStateEquiv_index {G : NegamiData}
    {K H : BoundaryData P} {ρ : P → P → ℕ} (W : Gluing G K H ρ)
    (S : Finset G.Edge) :
    (W.categoricalStateEquiv S).1 =
      (K.boundaryType (W.states S).1, H.boundaryType (W.states S).2) := by
  rfl

/-- Lemma 4.3 and the edge bookkeeping imply equality of all three degrees. -/
theorem Gluing.triDegree_eq_categoricalPairing
    {G : NegamiData} {K H : BoundaryData P}
    {ρ : P → P → ℕ} (W : Gluing G K H ρ) (S : Finset G.Edge) :
    (categoricalPairing K H ρ).degree (W.categoricalStateEquiv S) =
      G.triDegree S := by
  ext
  · simp [categoricalPairing, matrixEntryObject, boundaryObject,
      NegamiData.triDegree, W.component_formula]
    rw [W.categoricalStateEquiv_left S, W.categoricalStateEquiv_right S,
      W.categoricalStateEquiv_index S]
    simp
    omega
  · simp [categoricalPairing, matrixEntryObject, boundaryObject,
      NegamiData.triDegree, W.selected_card]
    rw [W.categoricalStateEquiv_left S, W.categoricalStateEquiv_right S]
  · simp [categoricalPairing, matrixEntryObject, boundaryObject,
      NegamiData.triDegree]
    rw [W.categoricalStateEquiv_left S, W.categoricalStateEquiv_right S]
    have hK : (W.states S).1.card ≤ Fintype.card K.Edge :=
      Finset.card_le_univ (W.states S).1
    have hH : (W.states S).2.card ≤ Fintype.card H.Edge :=
      Finset.card_le_univ (W.states S).2
    have hedge : Fintype.card G.Edge =
        Fintype.card K.Edge + Fintype.card H.Edge := by
      simpa [Nat.card_eq_fintype_card] using W.edge_card
    have hselected := W.selected_card S
    omega

/-- Theorem 4.5: the object-level categorical splitting formula. -/
noncomputable def Gluing.categoricalObjectEquiv
    {G : NegamiData} {K H : BoundaryData P}
    {ρ : P → P → ℕ} (W : Gluing G K H ρ) :
    GradedObject.Equiv G.stateObject (categoricalPairing K H ρ) where
  basisEquiv := W.categoricalStateEquiv
  degree_eq := W.triDegree_eq_categoricalPairing

/-- The categorical equivalence induces an honest linear equivalence after
realization over any coefficient semiring. -/
noncomputable def Gluing.categoricalRealizationEquiv
    {G : NegamiData} {K H : BoundaryData P}
    {ρ : P → P → ℕ} (W : Gluing G K H ρ) (k : Type*) [Semiring k] :
    G.stateObject.realization k ≃ₗ[k] (categoricalPairing K H ρ).realization k :=
  W.categoricalObjectEquiv.toLinearEquiv

/-- Decategorification of the grouped object-level formula. -/
theorem Gluing.hilbert_categoricalPairing
    {G : NegamiData} {K H : BoundaryData P} {ρ : P → P → ℕ}
    (W : Gluing G K H ρ) {R : Type*} [CommSemiring R] (t x y : R) :
    G.stateObject.hilbert t x y =
      ∑ p : P × P, t ^ ρ p.1 p.2 *
        (K.boundaryObject p.1).hilbert t x y *
        (H.boundaryObject p.2).hilbert t x y := by
  rw [W.categoricalObjectEquiv.hilbert_eq]
  exact LeanCo.Negami.BoundaryData.hilbert_categoricalPairing K H ρ t x y

end BoundaryData
end LeanCo.Negami
