import LeanCo.HypercubeTuran.AcyclicBridge
import LeanCo.HypercubeTuran.Alteration
import LeanCo.HypercubeTuran.ColoringAssembly
import LeanCo.HypercubeTuran.PoleConcentration
import LeanCo.HypercubeTuran.Subdivision
import LeanCo.HypercubeTuran.SubdivisionGirth

/-!
# Deterministic assembly of the main theorem

This module isolates the last deterministic implication.  Once the random
construction supplies an `IsAlterationSource`, its altered one-subdivision is
layered, has the requested girth, and has an explicit avoiding two-colouring
in every cube.  The final equivalence transports the finite vertex type to a
canonical `Fin m`, exactly as required by the theorem statement.
-/

open scoped SimpleGraph

namespace LeanCo.HypercubeTuran

open SimpleGraph

noncomputable section

/-- A combinatorial base contains precisely the four fields needed by the
parity-colouring argument. -/
def IsCombinatorialBase.toIsAvoidanceBase {V : Type} [Fintype V]
    [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
    (h : IsCombinatorialBase G d) : IsAvoidanceBase G where
  ten_le_card := h.ten_le_card
  connected := h.connected
  concentrated := h.hasPoleConcentration G
  small_independent := h.small_independent

/-- Avoiding two-colourings are invariant under relabelling the forbidden
graph by a graph isomorphism. -/
theorem hasAvoidingTwoColoring_congr {A B : Type} {H : SimpleGraph A}
    {H' : SimpleGraph B} (e : H ≃g H') {n : ℕ}
    (h : HasAvoidingTwoColoring H n) : HasAvoidingTwoColoring H' n := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun c => ?_⟩
  exact (SimpleGraph.free_congr_left e).mp (hC c)

/-- Layeredness is invariant under relabelling the graph. -/
theorem isLayered_congr {A B : Type} {H : SimpleGraph A}
    {H' : SimpleGraph B} (e : H ≃g H') (h : IsLayered H) :
    IsLayered H' := by
  obtain ⟨n, k, hcopy⟩ := h
  exact ⟨n, k, e.isContained'.trans hcopy⟩

/-- The complete deterministic conclusion produced from one alteration
source. -/
theorem witness_of_isAlterationSource
    {N d g : ℕ} {G : SimpleGraph (Fin N)} [DecidableRel G.Adj]
    (hsource : IsAlterationSource G d g) :
    ∃ (m : ℕ) (H : SimpleGraph (Fin m)),
      IsLayered H ∧ g ≤ H.girth ∧
        ∀ n : ℕ, HasAvoidingTwoColoring H n := by
  let B := deleteShortCycles G g
  have hbase : IsCombinatorialBase B d :=
    hsource.deleteShortCycles_isCombinatorialBase
  have havoid : IsAvoidanceBase B := hbase.toIsAvoidanceBase
  let H₀ := oneSubdivision B
  let e : SubdivisionVertex B ≃ Fin (Fintype.card (SubdivisionVertex B)) :=
    Fintype.equivFin _
  let H : SimpleGraph (Fin (Fintype.card (SubdivisionVertex B))) := H₀.map e
  let iso : H₀ ≃g H := SimpleGraph.Iso.map e H₀
  refine ⟨Fintype.card (SubdivisionVertex B), H, ?_, ?_, ?_⟩
  · exact isLayered_congr iso (oneSubdivision_isLayered B)
  · have hbaseGirth : g ≤ B.girth :=
      hbase.girth_ge (coe_le_egirth_deleteShortCycles G g)
    have hsubGirth : B.girth ≤ H₀.girth :=
      girth_le_oneSubdivision_girth B hbase.oneSubdivision_not_isAcyclic
    have hH₀ : g ≤ H₀.girth := hbaseGirth.trans hsubGirth
    rw [iso.girth_eq] at hH₀
    exact hH₀
  · intro n
    apply hasAvoidingTwoColoring_congr iso
    exact hasAvoidingTwoColoring_oneSubdivision_of_isAvoidanceBase havoid n

/-- The same source also yields the pointwise one-half cube Turán lower
bound before canonical relabelling. -/
theorem halfDensity_of_isAlterationSource
    {N d g : ℕ} {G : SimpleGraph (Fin N)} [DecidableRel G.Adj]
    (hsource : IsAlterationSource G d g) :
    HasCubeTuranLowerBound
      (oneSubdivision (deleteShortCycles G g)) (1 / 2 : ℝ) := by
  have hbase := hsource.deleteShortCycles_isCombinatorialBase
  exact hasCubeTuranLowerBound_half_oneSubdivision_of_isAvoidanceBase
    hbase.toIsAvoidanceBase

/-- The exact existence interface left to the probabilistic construction. -/
def HasAlterationSources : Prop :=
  ∀ g : ℕ, 3 ≤ g →
    ∃ (N d : ℕ) (G : SimpleGraph (Fin N)),
      ∃ _inst : DecidableRel G.Adj, IsAlterationSource G d g

/-- Once alteration sources exist in every requested girth, the literal
Ramsey statement of the paper follows. -/
theorem axenovichPejicRamseyStatement_of_hasAlterationSources
    (hsources : HasAlterationSources) : AxenovichPejicRamseyStatement := by
  intro g hg
  obtain ⟨N, d, G, inst, hsource⟩ := hsources g hg
  letI : DecidableRel G.Adj := inst
  exact witness_of_isAlterationSource hsource

end

end LeanCo.HypercubeTuran
