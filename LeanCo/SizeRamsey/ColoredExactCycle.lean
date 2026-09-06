import LeanCo.SizeRamsey.FinalUpperArithmetic
import LeanCo.SizeRamsey.HostNumerics
import LeanCo.SizeRamsey.LengthAdjustment
import LeanCo.SizeRamsey.LongEvenCycle
import LeanCo.SizeRamsey.MonochromaticCore
import LeanCo.SizeRamsey.TwoLevelCopy

/-!
# A monochromatic cycle of the exact target length

This module completes the deterministic part of the upper bound.  It keeps
the BFS depth and localized core produced by Claim 4.2, applies the full
length-adjustment lemma there, and then selects the target even length using
the paper's explicit depth estimate.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open Finset SimpleGraph

universe u

variable {V : Type u}

/-- Under the three host conclusions of Lemma 2.1, every `k`-edge-colouring
contains a monochromatic cycle of the exact admissible even length `n`. -/
theorem exists_monochromatic_exact_even_cycle_of_hostProperties
    (Gamma : SimpleGraph V) [Fintype V] [Nonempty V]
    [DecidableEq V] [DecidableRel Gamma.Adj]
    {k n : Nat} (hk : 2 ≤ k)
    (hn : 100 * Real.log (k : Real) ≤ n) (hnEven : Even n)
    (hcard : Fintype.card V = 2 * hostPartSize k n)
    (hbip : Gamma.IsBipartite)
    (hlower : hostProbability k n * (hostPartSize k n : Real) ^ 2 / 2 ≤
      (edgeCount Gamma : Real))
    (hsparse : IsLocallySparse Gamma (3 * n) (localSparsityFactor k))
    (lab : Gamma.EdgeLabeling (Fin k)) :
    ∃ color : Fin k,
      ContainsCycleLength (lab.labelGraph color) n := by
  classical
  have hnpos : 0 < n := by
    have hlog := log_natCast_pos hk
    have hnreal : (0 : Real) < n := by nlinarith
    exact_mod_cast hnreal
  let d := localDegreeThreshold k
  have hd : 2 ≤ d := two_le_localDegreeThreshold hk
  have hdense := claim_four_one_density_of_host_lower
    Gamma hk hnpos hcard hlower
  obtain ⟨color, S, D, hDconn, _hDavg, hDminNat,
      hDlabel, hDGamma⟩ :=
    exists_monochromatic_densityCore Gamma (by omega) (by omega)
      hdense lab
  obtain ⟨copyDLabel⟩ := hDlabel
  obtain ⟨copyDGamma⟩ := hDGamma
  letI : Fintype D := Fintype.ofFinite D
  letI : DecidableEq D := Classical.decEq D
  letI : DecidableRel D.toSimpleGraph.Adj := Classical.decRel _
  obtain ⟨rootValue, hrootValue⟩ := D.nonempty_supp
  let root : D := ⟨rootValue, hrootValue⟩
  letI : Nonempty D := ⟨root⟩
  have hbipD : D.toSimpleGraph.IsBipartite :=
    isBipartite_of_copy hbip copyDGamma
  have hDmin : HasMinimumDegreeGreaterThan D.toSimpleGraph (8 * d) := by
    intro x
    have hx := hDminNat x
    rwa [natCard_neighborSet_eq_degree] at hx
  obtain ⟨q, i, hiOne, hiq, hqlog, hlong⟩ :=
    exists_localized_long_even_cycle Gamma D.toSimpleGraph copyDGamma
      hbipD hDconn root hnpos hd hDmin hsparse
      (six_mul_localSparsityFactor_lt_localDegreeThreshold hk)
  obtain ⟨Tset, C, hCconn, hCminNat, hCpair,
      cycleRoot, c, hcycle, hcycleEven, hcycleLong⟩ := hlong
  obtain ⟨copyCPair⟩ := hCpair
  let pairSet : Set D :=
    ((twoLevelFinset D.toSimpleGraph root i : Finset D) : Set D)
  let copyCD : C.toSimpleGraph.Copy D.toSimpleGraph :=
    (SimpleGraph.Copy.induce D.toSimpleGraph pairSet).comp copyCPair
  letI : Fintype C := Fintype.ofFinite C
  letI : DecidableEq C := Classical.decEq C
  letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
  have hlevels : ∀ x : C,
      D.toSimpleGraph.dist root (copyCD x) = i ∨
        D.toSimpleGraph.dist root (copyCD x) = i + 1 := by
    have h := copy_induce_twoLevel_levels
      (G := D.toSimpleGraph) root i copyCPair
    simpa only [pairSet, copyCD] using h
  have hCmin : ∀ x : C, 3 ≤ C.toSimpleGraph.degree x := by
    intro x
    have hx := hCminNat x
    rw [natCard_neighborSet_eq_degree] at hx
    omega
  let bfsParents : BFSParentSystem D.toSimpleGraph root :=
    BFSParentSystem.ofConnected hDconn root
  obtain ⟨r, hr, hri, hfamily⟩ :=
    exists_cycleLength_interval hbipD hDconn hCconn copyCD root
      hlevels hCmin bfsParents c hcycle
  have hDcardGamma : Fintype.card D ≤ Fintype.card V :=
    Fintype.card_le_of_injective (fun x ↦ copyDGamma x)
      copyDGamma.injective
  have hDcard : Fintype.card D ≤ 2 * hostPartSize k n := by
    omega
  have htargetD : ContainsCycleLength D.toSimpleGraph n :=
    containsCycleLength_target_of_even_interval D.toSimpleGraph
      hk hn hnEven hDcard hiOne hiq hqlog hr hri
      hcycleEven hcycleLong hfamily
  exact ⟨color, htargetD.map_copy copyDLabel⟩

end LeanCo.SizeRamsey
