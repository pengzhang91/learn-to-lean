import LeanCo.QuantumLatin.BiresolutionReindex
import LeanCo.QuantumLatin.EvenOrders
import LeanCo.QuantumLatin.OddOrders
import LeanCo.QuantumLatin.OrderEight

/-!
# Arithmetic availability predicates

These decidable predicates separate the finite arithmetic bookkeeping in the
main theorem from the mathematical constructions which realize each case.
-/

namespace LeanCo.QuantumLatin

/-- The unique order-one maximal RQLS. -/
def maximalRQLSOne : MaximalRQLS (Fin 1) where
  square := {
    entry := fun _ _ ↦ basis 0
    row_orthonormal := by
      intro i a b
      have hab : a = b := Subsingleton.elim _ _
      subst b
      simpa [basis] using dot_self_basis (0 : Fin 1)
    col_orthonormal := by
      intro j a b
      have hab : a = b := Subsingleton.elim _ _
      subst b
      simpa [basis] using dot_self_basis (0 : Fin 1) }
  resolution := {
    column := fun _ ↦ Equiv.refl _
    covers := by
      intro i
      constructor
      · intro a b _
        exact Subsingleton.elim _ _
      · intro j
        exact ⟨0, Subsingleton.elim _ _⟩
    orthonormal := by
      intro t a b
      have hab : a = b := Subsingleton.elim _ _
      subst b
      simpa [basis] using dot_self_basis (0 : Fin 1) }
  maximal := by
    intro i j i' j' h
    exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩

theorem existsMaximalRQLS_one : ExistsMaximalRQLS 1 := ⟨maximalRQLSOne⟩

/-- Orders for which this development has a direct biresolution certificate.
The generic branch uses cyclic slopes `1,2,3`; five finite certificates close
all small outer orders needed by the final arithmetic table. -/
def OuterOK (n : ℕ) : Prop :=
  (Nat.Coprime 2 n ∧ Nat.Coprime 3 n) ∨
    n = 9 ∨ n = 14 ∨ n = 15 ∨ n = 18 ∨ n = 21

instance (n : ℕ) : Decidable (OuterOK n) := by
  unfold OuterOK
  infer_instance

theorem exists_biresolution_fin_of_outerOK {n : ℕ} (hn : OuterOK n) :
    Nonempty (ClassicalBiresolution (Fin n)) := by
  rcases hn with hcyclic | hfinite
  · have hn0 : n ≠ 0 := by
      intro hn0
      subst n
      norm_num at hcyclic
    letI : NeZero n := ⟨hn0⟩
    let e : ZMod n ≃ Fin n := Fintype.equivOfCardEq (by simp [ZMod.card])
    exact ⟨(cyclicClassicalBiresolution n
      ((ZMod.isUnit_iff_coprime 2 n).2 hcyclic.1)
      ((ZMod.isUnit_iff_coprime 3 n).2 hcyclic.2)).reindex e⟩
  · rcases hfinite with rfl | rfl | rfl | rfl | rfl
    · exact biresolution_nine
    · exact biresolution_fourteen
    · exact biresolution_fifteen
    · exact biresolution_eighteen
    · exact biresolution_twentyOne

/-- Orders already supplied before applying the singular construction. -/
def SupportedOrder (h : ℕ) : Prop :=
  h = 1 ∨ h = 8 ∨ (7 ≤ h ∧ Odd h) ∨
    (12 ≤ h ∧ 4 ∣ h)

instance (h : ℕ) : Decidable (SupportedOrder h) := by
  unfold SupportedOrder
  infer_instance

theorem existsMaximalRQLS_of_supportedOrder {h : ℕ}
    (hh : SupportedOrder h) : ExistsMaximalRQLS h := by
  rcases hh with rfl | rfl | hh | ⟨hh12, ⟨k, rfl⟩⟩
  · exact existsMaximalRQLS_one
  · exact existsMaximalRQLS_eight
  · letI : NeZero h := ⟨by omega⟩
    obtain ⟨⟨μ, hμ⟩⟩ := exists_odd_cyclicCertificate h hh.1 hh.2
    exact existsMaximalRQLS_of_cyclicCertificate h μ hμ
  · exact existsMaximalRQLS_four_mul k (by omega)

end LeanCo.QuantumLatin
