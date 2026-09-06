import LeanCo.HypercubeTuran.LocalSparseCycles
import LeanCo.HypercubeTuran.PaperStatement
import LeanCo.HypercubeTuran.RandomParameters
import LeanCo.HypercubeTuran.RandomSourceBridge

/-!
# End-to-end theorem

This file joins the probabilistic source construction to the deterministic
short-cycle alteration and the hypercube colouring argument.
-/

open scoped SimpleGraph

namespace LeanCo.HypercubeTuran

open SimpleGraph

noncomputable section

/-- The binomial construction supplies an alteration source at every target
girth. -/
theorem random_hasAlterationSources : HasAlterationSources := by
  intro g _hg
  obtain ⟨N, d, p, E, hN, hd, hgood⟩ :=
    RB.exists_isGoodSource_explicit_parameters g
  let G : SimpleGraph (Fin N) := graphOfEdges E
  let inst : DecidableRel G.Adj := Classical.decRel _
  refine ⟨N, d, G, inst, ?_⟩
  letI : DecidableRel G.Adj := inst
  apply hgood.toIsAlterationSource_of_shortCyclesVertexDisjoint hN hd
  simpa only [G] using hgood.shortCyclesVertexDisjoint

/-- End-to-end Ramsey/edge-colouring form of the Axenovich--Pejić theorem. -/
theorem axenovichPejicRamseyStatement : AxenovichPejicRamseyStatement :=
  axenovichPejicRamseyStatement_of_hasAlterationSources
    random_hasAlterationSources

/-- End-to-end cube Turán-density form: for every requested girth there is a
layered graph whose pointwise cube Turán lower bound is at least one half. -/
theorem axenovichPejicDensityStatement : AxenovichPejicDensityStatement :=
  axenovichPejicDensityStatement_of_hasAlterationSources
    random_hasAlterationSources

end

end LeanCo.HypercubeTuran
