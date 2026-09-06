import LeanCo.HypercubeTuran.DeterministicMain

/-!
# The density statement of Axenovich--Pejić

The construction actually gives a pointwise one-half lower bound in every
finite cube.  This is stronger than the corresponding asymptotic cube Turán
density assertion and avoids committing the theorem statement to a particular
encoding of a limit or limsup.
-/

open scoped SimpleGraph

namespace LeanCo.HypercubeTuran

open SimpleGraph

noncomputable section

/-- The main theorem in its cube Turán-density form, stated using the stronger
pointwise finite lower bound developed in `TuranWitness`. -/
def AxenovichPejicDensityStatement : Prop :=
  ∀ g : ℕ, 3 ≤ g →
    ∃ (m : ℕ) (H : SimpleGraph (Fin m)),
      IsLayered H ∧ g ≤ H.girth ∧
        HasCubeTuranLowerBound H (1 / 2 : ℝ)

/-- Alteration sources imply the paper's density theorem. -/
theorem axenovichPejicDensityStatement_of_hasAlterationSources
    (hsources : HasAlterationSources) : AxenovichPejicDensityStatement := by
  intro g hg
  obtain ⟨N, d, G, inst, hsource⟩ := hsources g hg
  letI : DecidableRel G.Adj := inst
  obtain ⟨m, H, hlayered, hgirth, havoid⟩ :=
    witness_of_isAlterationSource hsource
  exact ⟨m, H, hlayered, hgirth,
    hasCubeTuranLowerBound_half_of_avoiding H havoid⟩

end

end LeanCo.HypercubeTuran
