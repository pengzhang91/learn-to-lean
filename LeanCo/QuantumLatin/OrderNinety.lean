import LeanCo.QuantumLatin.OddOrders
import LeanCo.QuantumLatin.BlockProduct

/-!
# The exceptional order 90

This closes Lemma 4.10 using the two explicit Sage Latin squares of order 10
and ten phase-disjoint copies of the cyclic order-nine RQLS.
-/

namespace LeanCo.QuantumLatin

theorem existsMaximalRQLS_ninety : ExistsMaximalRQLS 90 := by
  letI : NeZero 9 := ⟨by decide⟩
  obtain ⟨⟨μ, hμ⟩⟩ := exists_odd_cyclicCertificate 9 (by decide) (by decide)
  let R : MaximalRQLS (ZMod 9) := cyclicMaximalRQLS 9 μ hμ
  have hde : (0 : ZMod 9) ≠ 1 := by decide
  have hnz : ∀ i j, R.square.entry i j 0 ≠ 0 ∧
      R.square.entry i j 1 ≠ 0 := by
    intro i j
    exact ⟨fourierKet_apply_ne_zero 9 μ i j 0,
      fourierKet_apply_ne_zero 9 μ i j 1⟩
  obtain ⟨B⟩ := R.exists_phaseDisjoint_copies hde hnz 10
  obtain ⟨A⟩ := resolvedSquare_ten
  simpa using existsMaximalRQLS_card (resolvedBlockMaximalRQLS A B)

end LeanCo.QuantumLatin
