import LeanCo.SizeRamsey.BLSConstantChoice
import LeanCo.SizeRamsey.BLSHostColoringAssembly
import LeanCo.SizeRamsey.BLSLargePathNumerics
import LeanCo.SizeRamsey.PathLowerQuantifierGlue

/-!
# From the Key Lemma to the complete path lower bound

This module closes every round, threshold, relabelling, and palette
quantifier in the Beke--Li--Sahasrabudhe argument.  Its sole input is the
locally formalized Key Lemma itself.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open SimpleGraph

noncomputable section

/-- The literal BLS-v1 Key Lemma implies the literal BLS-v1 path
size--Ramsey lower bound, including the bounded-colour cases. -/
theorem BLSPathLowerBoundV1_of_BLSKeyLemmaV1
    (hKey : BLSKeyLemmaV1) :
    BLSPathLowerBoundV1 := by
  obtain ⟨β₀, hβ₀, rKey, hExtractors⟩ :=
    exists_BLSRoundExtractors_of_BLSKeyLemmaV1 hKey
  let C : ℝ := blsLowerConstant β₀
  obtain ⟨hC, hCOne, hCsmall, hCβ, hCβHundred⟩ :
      0 < C ∧ C ≤ 1 ∧ 10000 * C ≤ 1 ∧
        20000 * C ≤ β₀ ∧ 100 * C ≤ β₀ := by
    simpa only [C] using blsLowerConstant_spec hβ₀.1 hβ₀.2
  obtain ⟨rTerminal, hTerminal⟩ :=
    exists_roundEdgeCap_schedule_terminal_threshold hC.le hCOne
  obtain ⟨rRate, hRate⟩ :=
    exists_blsExtractionRate_roundBeta_le_one_threshold hβ₀.1
  let R : ℕ := blsFinalThreshold
    (max 21 rKey) rTerminal rRate (50000 ^ 4) 2
  apply BLSPathLowerBoundV1_of_large hC
  intro r n hrLarge hn
  have hR : R ≤ r := (Nat.le_max_right 2 R).trans hrLarge
  have hcomponents := blsFinalThreshold_spec
    (max 21 rKey) rTerminal rRate (50000 ^ 4) 2
  have hrKey : max 21 rKey ≤ r := hcomponents.1.trans hR
  have hrTerminal : rTerminal ≤ r := hcomponents.2.1.trans hR
  have hrRate : rRate ≤ r := hcomponents.2.2.1.trans hR
  have hrPower : 50000 ^ 4 ≤ r := hcomponents.2.2.2.1.trans hR
  have hrTwo : 2 ≤ r := (Nat.le_max_left 2 R).trans hrLarge
  have hnTwelve : 12 ≤ n := twelve_le_of_hundred_log_le hrTwo hn
  intro M G hedge
  have hedgeCap : (edgeCount G : ℝ) ≤ roundEdgeCap C r n 0 :=
    edgeCount_le_initialRoundEdgeCap_of_lt_pathLowerScale
      G hC.le (by omega) hedge
  have hterminal :
      roundEdgeCap C r n (roundHorizon r) <
        10 * (Real.rpow (r : ℝ) (7 / 4 : ℝ) * n) := by
    simpa only [Real.rpow_eq_pow, mul_assoc] using
      (hTerminal (r := r) (n := n) hrTerminal (by omega))
  have hrate : ∀ i, i < roundHorizon r →
      blsExtractionRate r (roundBeta β₀ i) ≤ 1 := by
    intro i hi
    exact hRate hrRate hi
  have hextractor : ∀ (N : ℕ) (β : ℝ), β ≤ β₀ →
      ∃ pick : SimpleGraph (Fin N) → SimpleGraph (Fin N),
        (∀ Q, pick Q ≤ Q) ∧
        (∀ Q, (pathGraph n).Free (pick Q)) ∧
        (∀ Q,
          @BLSRoundAdmissible (Fin N) inferInstance Q
              (Classical.decRel _) r n β →
            BLSRoundGain r β Q (pick Q)) := by
    intro N β hβ
    exact hExtractors r hrKey n hn β hβ N
  exact exists_BLSHostPathAvoidingColoring
    hβ₀.1 hβ₀.2 hC hCOne hCsmall hCβ hrPower hnTwelve
      hterminal hrate hextractor G hedgeCap

end

end LeanCo.SizeRamsey
