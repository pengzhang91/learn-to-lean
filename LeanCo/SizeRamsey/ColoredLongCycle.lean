import LeanCo.SizeRamsey.LongEvenCycle
import LeanCo.SizeRamsey.MonochromaticCore

/-!
# A monochromatic long even cycle

This module joins Claims 4.1 and 4.2.  It is the deterministic coloured-host
part of the upper-bound proof before the final cycle-length adjustment.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open Finset SimpleGraph

universe u

variable {V : Type u}

/-- Under the host edge-density and local-sparsity conclusions of Lemma 2.1,
every `k`-edge-colouring contains a monochromatic even cycle of length at
least `n+2`. -/
theorem exists_monochromatic_long_even_cycle
    (Gamma : SimpleGraph V) [Fintype V] [Nonempty V]
    [DecidableEq V] [DecidableRel Gamma.Adj]
    (hbip : Gamma.IsBipartite)
    {k n d edgeFactor : Nat}
    (hk : 0 < k) (hn : 0 < n) (hd : 2 ≤ d)
    (hdense : k * ((16 * d) * Fintype.card V) ≤ 2 * edgeCount Gamma)
    (hsparse : IsLocallySparse Gamma (3 * n) edgeFactor)
    (hfactor : 6 * edgeFactor < d)
    (lab : Gamma.EdgeLabeling (Fin k)) :
    ∃ color : Fin k, ∃ ell : Nat,
      Even ell ∧ n + 2 ≤ ell ∧
        ContainsCycleLength (lab.labelGraph color) ell := by
  classical
  obtain ⟨color, S, D, hDconn, hDavg, hDminNat,
      hDlabel, hDGamma⟩ :=
    exists_monochromatic_densityCore Gamma hk (by omega) hdense lab
  obtain ⟨copyDLabel⟩ := hDlabel
  obtain ⟨copyDGamma⟩ := hDGamma
  letI : Fintype D := Fintype.ofFinite D
  letI : DecidableEq D := Classical.decEq D
  letI : DecidableRel D.toSimpleGraph.Adj := Classical.decRel _
  obtain ⟨r, hr⟩ := D.nonempty_supp
  let root : D := ⟨r, hr⟩
  letI : Nonempty D := ⟨root⟩
  have hbipD : D.toSimpleGraph.IsBipartite :=
    isBipartite_of_copy hbip copyDGamma
  have hDmin : HasMinimumDegreeGreaterThan D.toSimpleGraph (8 * d) := by
    intro x
    have hx := hDminNat x
    rwa [natCard_neighborSet_eq_degree] at hx
  obtain ⟨q, i, hiOne, hiq, hqlog, hlong⟩ :=
    exists_localized_long_even_cycle Gamma D.toSimpleGraph copyDGamma
      hbipD hDconn root hn hd hDmin hsparse hfactor
  obtain ⟨T, C, hCconn, hCminNat, hCpair,
      x, c, hcycle, heven, hlength⟩ := hlong
  obtain ⟨copyCPair⟩ := hCpair
  let pairSet : Set D :=
    ((twoLevelFinset D.toSimpleGraph root i : Finset D) : Set D)
  let copyCD : C.toSimpleGraph.Copy D.toSimpleGraph :=
    (SimpleGraph.Copy.induce D.toSimpleGraph pairSet).comp copyCPair
  let copyCLabel : C.toSimpleGraph.Copy (lab.labelGraph color) :=
    copyDLabel.comp copyCD
  have hcontainsC : ContainsCycleLength C.toSimpleGraph c.length :=
    ⟨x, c, hcycle, rfl⟩
  have hcontainsLabel :
      ContainsCycleLength (lab.labelGraph color) c.length :=
    hcontainsC.map_copy copyCLabel
  exact ⟨color, c.length, heven, hlength, hcontainsLabel⟩

end LeanCo.SizeRamsey
