import LeanCo.PackingEdgeColoring.SectionFourExceptionalPatterns
import LeanCo.PackingEdgeColoring.FaceBoundaryMinimumDegree

/-!
# Closed discharging contradiction for the girth-sixteen theorem

This module assembles the facial-girth, exceptional-pattern, six-window, and
Euler-charge layers.  The only remaining embedding-side input is that every
dart is two-sided; the minimal-counterexample/planarity layer proves that
separately by excluding bridges and one-sided nonbridges.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open SimpleGraph

noncomputable section

variable {V : Type*} {G : SimpleGraph V}

namespace RotationSystem

variable (R : RotationSystem G)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Girth sixteen and two-sided facial boundaries turn the two local
reducibility conclusions into the global Euler-charge contradiction. -/
theorem no_spherical_map_of_girth16_forbidden_threads
    (hspherical : R.IsSpherical)
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (htwo : ∀ d : G.Dart, R.IsTwoSidedDart d)
    (hgirth : (16 : ℕ∞) ≤ G.egirth)
    (hno4 : ∀ {u v : V} (p : G.Walk u v), ¬ IsKChain G p 4)
    (hforbid : ∀ u, ¬ HasThreeAndLongThreadAt (G := G) u) : False := by
  apply R.no_spherical_map_of_girth16_face_density hspherical hdeg
  · intro f
    exact R.sixteen_le_faceLength_of_faceEdgeSimple f
      (R.faceEdgeSimple_of_isTwoSided f (fun d _ ↦ htwo d)) hgirth
  · intro f
    have hshort : R.FaceShortBoundaryPaths f :=
      R.faceShortBoundaryPaths_of_girth_sixteen_of_twoSided f
        (fun d _ ↦ htwo d) hgirth
    exact R.sixPathDensity_of_no_four_chain_and_no_long_thread_pair_closed
      f hshort hdeg hno4 hforbid

/-- Closed discharging contradiction with no global two-sidedness premise.
Minimum degree two supplies genuine cycles inside all facial boundaries and
makes every facial segment of at most four edges a path, even across bridge
excursions. -/
theorem no_spherical_map_of_girth16_forbidden_threads_of_minDegree
    (hspherical : R.IsSpherical)
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hgirth : (16 : ℕ∞) ≤ G.egirth)
    (hno4 : ∀ {u v : V} (p : G.Walk u v), ¬ IsKChain G p 4)
    (hforbid : ∀ u, ¬ HasThreeAndLongThreadAt (G := G) u) : False := by
  have hmindeg : ∀ v, 2 ≤ G.degree v := by
    intro v
    rcases hdeg v with h | h <;> omega
  apply R.no_spherical_map_of_girth16_face_density hspherical hdeg
  · intro f
    exact R.sixteen_le_faceLength_of_two_le_degree hmindeg hgirth f
  · intro f
    have hshort : R.FaceShortBoundaryPaths f :=
      R.faceShortBoundaryPaths_of_two_le_degree_of_girth_sixteen
        hmindeg hgirth f
    exact R.sixPathDensity_of_no_four_chain_and_no_long_thread_pair_closed
      f hshort hdeg hno4 hforbid

end Finite

end RotationSystem

end

end LeanCo.PackingEdgeColoring
