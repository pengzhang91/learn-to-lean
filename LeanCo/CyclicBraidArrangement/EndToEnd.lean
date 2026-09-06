import LeanCo.CyclicBraidArrangement.CyclicCompatibility
import LeanCo.CyclicBraidArrangement.GapEnumeration
import LeanCo.CyclicBraidArrangement.WeakSum
import LeanCo.CyclicBraidArrangement.CycleFormula
import LeanCo.CyclicBraidArrangement.Uniform
import LeanCo.CyclicBraidArrangement.AdjacentSufficiency
import LeanCo.CyclicBraidArrangement.AdjacentPlacement
import LeanCo.CyclicBraidArrangement.Graphical
import LeanCo.CyclicBraidArrangement.WeakSumConverse
import LeanCo.CyclicBraidArrangement.WeakSumDirect
import LeanCo.CyclicBraidArrangement.AffineHullDirect
import LeanCo.CyclicBraidArrangement.FiniteFieldGaps
import LeanCo.CyclicBraidArrangement.FiniteFieldCount
import LeanCo.CyclicBraidArrangement.FiniteFieldPlacementCount
import LeanCo.CyclicBraidArrangement.ZModPlacement
import LeanCo.CyclicBraidArrangement.ArrangementCharacteristic
import LeanCo.CyclicBraidArrangement.ArrangementPaperDefinition
import LeanCo.CyclicBraidArrangement.ArrangementStability
import LeanCo.CyclicBraidArrangement.ArrangementFiniteField
import LeanCo.CyclicBraidArrangement.ArrangementOrbitBridge
import LeanCo.CyclicBraidArrangement.TransposeArrangement
import LeanCo.CyclicBraidArrangement.ArrangementMainTheorem
import LeanCo.CyclicBraidArrangement.CyclePolynomial
import LeanCo.CyclicBraidArrangement.CharacteristicBridge
import LeanCo.CyclicBraidArrangement.GaugeShift
import LeanCo.CyclicBraidArrangement.PartitionWeights
import LeanCo.CyclicBraidArrangement.FinpartitionBlockDecomposition
import LeanCo.CyclicBraidArrangement.ShiPartitionIdentityDirect
import LeanCo.CyclicBraidArrangement.PartitionIdentitiesDirect
import LeanCo.CyclicBraidArrangement.ShiPartitionBridge
import LeanCo.CyclicBraidArrangement.BraidPartitionIdentityDirect
import LeanCo.CyclicBraidArrangement.BraidPartitionBridge
import LeanCo.CyclicBraidArrangement.UniformEulerian
import LeanCo.CyclicBraidArrangement.CharacteristicCorollaries
import LeanCo.CyclicBraidArrangement.Applications
import LeanCo.CyclicBraidArrangement.SharpnessExample
import LeanCo.CyclicBraidArrangement.FerrersFactorizationDirect
import LeanCo.CyclicBraidArrangement.FerrersInsertionEquivalence
import LeanCo.CyclicBraidArrangement.FerrersRecurrenceAlgebra
import LeanCo.CyclicBraidArrangement.FerrersInsertionCardinality
import LeanCo.CyclicBraidArrangement.FerrersFactorizationTheorem
import LeanCo.CyclicBraidArrangement.PaperStatements

/-!
# End-to-end entry point for arXiv:2608.29203

The declarations below are canonical public aliases for both forms of the
paper's main theorem. The numbered interface remains in `PaperStatements`.
-/

namespace CyclicBraidArrangement

/-- Chen--Li--Wang, Theorem 1.2, full characteristic-polynomial form. -/
theorem chenLiWang_theorem_1_2_full {n : ℕ} [NeZero n]
    (M : DeformationMatrix n) (hM : M.CyclicallyCompatible) :
    M.whitneyCharacteristicPolynomial =
      Polynomial.X * cyclePolynomial M :=
  PaperStatements.theorem_one_two_full M hM

/-- Chen--Li--Wang, Theorem 1.2, reduced characteristic-polynomial form. -/
theorem chenLiWang_theorem_1_2_reduced {n : ℕ} [NeZero n]
    (M : DeformationMatrix n) (hM : M.CyclicallyCompatible) :
    M.whitneyReducedCharacteristicPolynomial = cyclePolynomial M :=
  PaperStatements.theorem_one_two_reduced M hM

end CyclicBraidArrangement
