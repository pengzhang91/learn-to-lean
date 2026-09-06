import LeanCo.SizeRamsey.BFSLocalization
import LeanCo.SizeRamsey.Majority

/-!
# The monochromatic density core

This file formalizes Claim 4.1.  A majority colour inherits enough of the
host edge density, and a minimum-cardinality induced subgraph followed by a
connected-component selection yields the required connected core.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open Finset SimpleGraph

universe u

variable {V : Type u}

/-- A majority colour contains a connected core of minimum degree greater
than `8*d`, under the division-free host-density hypothesis used in Claim
4.1.  The result retains both its monochromatic containment and an explicit
copy into the host. -/
theorem exists_monochromatic_densityCore
    (Gamma : SimpleGraph V) [Fintype V] [Nonempty V]
    [DecidableEq V] [DecidableRel Gamma.Adj]
    {k d : Nat} (hk : 0 < k) (hd : 0 < d)
    (hdense : k * ((16 * d) * Fintype.card V) ≤ 2 * edgeCount Gamma)
    (lab : Gamma.EdgeLabeling (Fin k)) :
    ∃ color : Fin k,
      ∃ S : Finset V,
        ∃ C : ((lab.labelGraph color).induce (S : Set V)).ConnectedComponent,
          C.toSimpleGraph.Connected ∧
            HasAverageDegreeAtLeast C.toSimpleGraph (16 * d) ∧
            (∀ x : C, 8 * d < Nat.card (C.toSimpleGraph.neighborSet x)) ∧
            C.toSimpleGraph ⊑ lab.labelGraph color ∧
            C.toSimpleGraph ⊑ Gamma := by
  classical
  letI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  obtain ⟨color, hmajority⟩ := exists_majority_label lab
  let H := lab.labelGraph color
  have hmajority' : edgeCount Gamma ≤ k * edgeCount H := by
    simpa [H] using hmajority
  have hmul : k * ((16 * d) * Fintype.card V) ≤
      k * (2 * edgeCount H) := by
    calc
      k * ((16 * d) * Fintype.card V) ≤ 2 * edgeCount Gamma := hdense
      _ ≤ 2 * (k * edgeCount H) := Nat.mul_le_mul_left 2 hmajority'
      _ = k * (2 * edgeCount H) := by ring
  have hHavg : HasAverageDegreeAtLeast H (16 * d) := by
    unfold HasAverageDegreeAtLeast
    rw [Nat.card_eq_fintype_card]
    exact le_of_mul_le_mul_left hmul hk
  have hscale : 2 * (8 * d) = 16 * d := by ring
  have hHavg' : HasAverageDegreeAtLeast H (2 * (8 * d)) := by
    simpa only [hscale] using hHavg
  obtain ⟨S, hSne, hSavg, hSmindeg⟩ :=
    exists_minimalDegree_dense_induced_finset H (d := 8 * d)
      (Nat.mul_pos (by norm_num) hd) hHavg'
  let J := H.induce (S : Set V)
  letI : Nonempty S := Finset.nonempty_coe_sort.mpr hSne
  obtain ⟨C, hCavg⟩ :=
    exists_connectedComponent_hasAverageDegreeAtLeast J hSavg
  let copyCH : C.toSimpleGraph.Copy H :=
    (SimpleGraph.Copy.induce H (S : Set V)).comp
      (SimpleGraph.Copy.induce J C.supp)
  let copyHG : H.Copy Gamma :=
    SimpleGraph.Copy.ofLE H Gamma lab.labelGraph_le
  let copyCGamma : C.toSimpleGraph.Copy Gamma := copyHG.comp copyCH
  refine ⟨color, S, C, C.connected_toSimpleGraph, ?_, ?_, ⟨copyCH⟩,
    ⟨copyCGamma⟩⟩
  · simpa only [hscale] using hCavg
  · intro x
    calc
      8 * d < J.degree x.val := hSmindeg x.val
      _ = Nat.card (J.neighborSet x.val) :=
        (natCard_neighborSet_eq_degree J x.val).symm
      _ = Nat.card (C.toSimpleGraph.neighborSet x) :=
        (natCard_neighborSet_connectedComponent J C x).symm

end LeanCo.SizeRamsey
