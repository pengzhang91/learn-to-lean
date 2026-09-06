import LeanCo.CyclicBraidArrangement.ArrangementMainTheorem

/-!
# Transposition and coordinate negation

This file formalizes the arrangement isomorphism in Remark 2.1.  Reversing
every oriented defining equation and negating all coordinates identifies a
matrix deformation with the deformation for the transposed matrix.  The
independent Whitney characteristic polynomials are therefore equal, without
any cyclic-compatibility hypothesis.
-/

namespace CyclicBraidArrangement

namespace DeformationMatrix

variable {n : ℕ}

/-- Reversal of an oriented forbidden equation under matrix transposition. -/
def transposeForbiddenEquationEquiv (M : DeformationMatrix n) :
    M.ForbiddenEquation ≃ M.transpose.ForbiddenEquation where
  toFun e :=
    ⟨e.target M, ⟨e.source M, e.source_ne_target M⟩, e.2.2⟩
  invFun e :=
    ⟨e.target M.transpose,
      ⟨e.source M.transpose, e.source_ne_target M.transpose⟩, e.2.2⟩
  left_inv e := by
    rcases e with ⟨a, b, r⟩
    rfl
  right_inv e := by
    rcases e with ⟨a, b, r⟩
    rfl

@[simp] theorem transposeForbiddenEquationEquiv_source
    (M : DeformationMatrix n) (e : M.ForbiddenEquation) :
    (M.transposeForbiddenEquationEquiv e).source M.transpose = e.target M := rfl

@[simp] theorem transposeForbiddenEquationEquiv_target
    (M : DeformationMatrix n) (e : M.ForbiddenEquation) :
    (M.transposeForbiddenEquationEquiv e).target M.transpose = e.source M := rfl

@[simp] theorem transposeForbiddenEquationEquiv_distance
    (M : DeformationMatrix n) (e : M.ForbiddenEquation) :
    (M.transposeForbiddenEquationEquiv e).distance M.transpose = e.distance M := rfl

/-- Negating coordinates turns satisfaction of a transposed equation into
satisfaction of the original equation. -/
theorem satisfiesEquation_transpose_neg_iff (M : DeformationMatrix n)
    {R : Type*} [Ring R] (x : Fin n → R) (e : M.ForbiddenEquation) :
    M.transpose.SatisfiesEquation (fun i ↦ -x i)
        (M.transposeForbiddenEquationEquiv e) ↔
      M.SatisfiesEquation x e := by
  unfold SatisfiesEquation
  simp only [transposeForbiddenEquationEquiv_source,
    transposeForbiddenEquationEquiv_target,
    transposeForbiddenEquationEquiv_distance]
  simp only [neg_sub_neg]

/-- The literal modular complements are equivalent by `x ↦ -x`.  This is
the finite-ring realization of the arrangement isomorphism from Remark 2.1. -/
def finiteFieldComplementTransposeEquiv (M : DeformationMatrix n)
    (R : Type*) [Ring R] :
    M.FiniteFieldComplement R ≃ M.transpose.FiniteFieldComplement R where
  toFun x := ⟨fun i ↦ -x.1 i, by
    intro e hbad
    let e' := (M.transposeForbiddenEquationEquiv).symm e
    have heq : M.transposeForbiddenEquationEquiv e' = e :=
      (M.transposeForbiddenEquationEquiv).apply_symm_apply e
    apply x.2 e'
    exact (M.satisfiesEquation_transpose_neg_iff x.1 e').mp
      (heq ▸ hbad)⟩
  invFun x := ⟨fun i ↦ -x.1 i, by
    intro e hbad
    apply x.2 (M.transposeForbiddenEquationEquiv e)
    have h := (M.satisfiesEquation_transpose_neg_iff
      (fun i ↦ -x.1 i) e).mpr hbad
    simpa using h⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    simp
  right_inv x := by
    apply Subtype.ext
    funext i
    simp

/-- The independently defined Whitney characteristic polynomial is invariant
under transposition, with no compatibility assumption. -/
theorem whitneyCharacteristicPolynomial_transpose (M : DeformationMatrix n) :
    M.transpose.whitneyCharacteristicPolynomial =
      M.whitneyCharacteristicPolynomial := by
  apply polynomial_eq_of_eventually_natCast_eval_eq
  refine ⟨max (max M.transpose.equationStabilityBound
    M.equationStabilityBound) 1, ?_⟩
  intro q hq
  have hqpos : 0 < q :=
    lt_of_lt_of_le Nat.zero_lt_one ((Nat.le_max_right _ 1).trans hq)
  letI : NeZero q := ⟨Nat.ne_of_gt hqpos⟩
  have htrans : M.transpose.equationStabilityBound ≤ q := by
    calc
      M.transpose.equationStabilityBound ≤
          max M.transpose.equationStabilityBound M.equationStabilityBound :=
        Nat.le_max_left _ _
      _ ≤ max (max M.transpose.equationStabilityBound
          M.equationStabilityBound) 1 := Nat.le_max_left _ _
      _ ≤ q := hq
  have hbase : M.equationStabilityBound ≤ q := by
    calc
      M.equationStabilityBound ≤
          max M.transpose.equationStabilityBound M.equationStabilityBound :=
        Nat.le_max_right _ _
      _ ≤ max (max M.transpose.equationStabilityBound
          M.equationStabilityBound) 1 := Nat.le_max_left _ _
      _ ≤ q := hq
  rw [M.transpose.eval_whitneyCharacteristicPolynomial_eq_complementCard
      htrans,
    M.eval_whitneyCharacteristicPolynomial_eq_complementCard
      hbase]
  exact_mod_cast Fintype.card_congr
    (M.finiteFieldComplementTransposeEquiv (ZMod q)).symm

/-- Transposition exchanges the two vertex-extension parameters. -/
theorem transpose_extend (M : DeformationMatrix n) (α β : Fin n → ℕ) :
    (M.extend α β).transpose = M.transpose.extend β α := by
  cases M with
  | mk entry hdiag =>
      rw [CyclicBraidArrangement.DeformationMatrix.mk.injEq]
      funext i j
      by_cases hij : i = j
      · subst j
        simp [extend, transpose]
      · have hji : j ≠ i := Ne.symm hij
        simp [extend, transpose, hij, hji, Nat.add_comm, Nat.add_left_comm]

/-- Remark 2.1 for the independently defined characteristic polynomial of a
two-sided extension. -/
theorem whitneyCharacteristicPolynomial_extend_transpose
    (M : DeformationMatrix n) (α β : Fin n → ℕ) :
    (M.extend α β).whitneyCharacteristicPolynomial =
      (M.transpose.extend β α).whitneyCharacteristicPolynomial := by
  rw [← M.transpose_extend α β,
    whitneyCharacteristicPolynomial_transpose]

/-- Negation also identifies the independently defined reduced characteristic
polynomials, without a compatibility assumption. -/
theorem whitneyReducedCharacteristicPolynomial_transpose
    (M : DeformationMatrix n) :
    M.transpose.whitneyReducedCharacteristicPolynomial =
      M.whitneyReducedCharacteristicPolynomial := by
  unfold whitneyReducedCharacteristicPolynomial
  rw [M.whitneyCharacteristicPolynomial_transpose]

/-- The same-parameter transpose invariance asserted in Remark 2.1.  The
negation isomorphism first swaps the two parameter vectors, and the
unconditional equal-total redistribution theorem swaps them back. -/
theorem whitneyCharacteristicPolynomial_extend_transpose_sameParameters
    [NeZero n] (hn : 2 ≤ n) (M : DeformationMatrix n)
    (hM : M.CyclicallyCompatible) (α β : Fin n → ℕ) :
    (M.extend α β).whitneyCharacteristicPolynomial =
      (M.transpose.extend α β).whitneyCharacteristicPolynomial := by
  calc
    (M.extend α β).whitneyCharacteristicPolynomial =
        (M.transpose.extend β α).whitneyCharacteristicPolynomial :=
      M.whitneyCharacteristicPolynomial_extend_transpose α β
    _ = (M.transpose.extend α β).whitneyCharacteristicPolynomial :=
      M.transpose.whitney_redistribution hn
        (M.cyclicallyCompatible_transpose hM) β α α β (by
          simp only [add_comm])

end DeformationMatrix

end CyclicBraidArrangement
