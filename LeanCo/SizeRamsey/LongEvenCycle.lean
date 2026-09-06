import LeanCo.SizeRamsey.BFSLocalization
import LeanCo.SizeRamsey.CopyExpansion
import LeanCo.SizeRamsey.LongCycle
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

/-!
# A long even cycle in two consecutive levels

This file closes Claim 4.2 of Wang--Wang from the deterministic host
sparsity condition.  It combines BFS localisation, copy-invariant local
expansion, Krivelevich's long-cycle lemma, and bipartite parity.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open Finset SimpleGraph

universe u v

variable {V : Type u} {W : Type v}

/-- The two definitions of external neighbourhood used by the BFS/host and
long-cycle modules agree literally. -/
theorem externalNeighborhood_eq_externalNeighborFinset
    (F : SimpleGraph W) [Fintype W] [DecidableEq W] [DecidableRel F.Adj]
    (X : Finset W) :
    externalNeighborhood F X = externalNeighborFinset F X := by
  ext y
  rw [mem_externalNeighborhood, mem_externalNeighborFinset]

/-- A connected high-minimum-degree graph inside two consecutive levels,
together with a long even cycle in that graph.  Neighbour-set cardinalities
are stated using `Nat.card` so this dependent witness does not expose a
choice of `Fintype` instances. -/
def HasLocalizedLongEvenCycle (J : SimpleGraph W)
    [Fintype W] [DecidableEq W] [DecidableRel J.Adj]
    (root : W) (i d n : Nat) : Prop :=
  ∃ S : Finset ((twoLevelFinset J root i : Finset W) : Set W),
    ∃ C : ((J.induce ((twoLevelFinset J root i : Finset W) : Set W)).induce
        (S : Set ((twoLevelFinset J root i : Finset W) : Set W))).ConnectedComponent,
      C.toSimpleGraph.Connected ∧
        (∀ x : C, d < Nat.card (C.toSimpleGraph.neighborSet x)) ∧
        C.toSimpleGraph ⊑
          J.induce ((twoLevelFinset J root i : Finset W) : Set W) ∧
        ∃ x : C, ∃ c : C.toSimpleGraph.Walk x x,
          c.IsCycle ∧ Even c.length ∧ n + 2 ≤ c.length

/-- Claim 4.2: deterministic long-even-cycle conclusion from a locally
sparse host.

`J` may use a different vertex type from the host `Gamma`; the actual copy
certificate is threaded through every step. -/
theorem exists_localized_long_even_cycle
    (Gamma : SimpleGraph V) [Fintype V]
    (J : SimpleGraph W) [Fintype W] [DecidableEq W] [DecidableRel J.Adj]
    (hJGamma : J.Copy Gamma)
    (hbip : J.IsBipartite) (hJconn : J.Connected)
    (root : W) {n d edgeFactor : Nat}
    (hn : 0 < n) (hd : 2 ≤ d)
    (hJmin : HasMinimumDegreeGreaterThan J (8 * d))
    (hsparse : IsLocallySparse Gamma (3 * n) edgeFactor)
    (hfactor : 6 * edgeFactor < d) :
    ∃ q i : Nat,
      1 ≤ i ∧ i < q ∧
        (q : Real) < 1 + Real.logb 2 (Fintype.card W : Real) ∧
        HasLocalizedLongEvenCycle J root i d n := by
  classical
  obtain ⟨q, i, hiOne, hiq, hqlog, hcore⟩ :=
    bfs_localisation hbip hJconn root d hd hJmin
  obtain ⟨S, C, hCconn, hCminNat, hCpair⟩ := hcore
  obtain ⟨hCpairCopy⟩ := hCpair
  let pairSet : Set W :=
    ((twoLevelFinset J root i : Finset W) : Set W)
  let H := J.induce pairSet
  let K := H.induce
    (S : Set ((twoLevelFinset J root i : Finset W) : Set W))
  let hCJ : C.toSimpleGraph.Copy J :=
    (SimpleGraph.Copy.induce J pairSet).comp hCpairCopy
  let hCGamma : C.toSimpleGraph.Copy Gamma := hJGamma.comp hCJ
  letI : Fintype C := Fintype.ofFinite C
  letI : DecidableEq C := Classical.decEq C
  letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
  obtain ⟨r, hr⟩ := C.nonempty_supp
  letI : Nonempty C := ⟨⟨r, hr⟩⟩
  have hCmin : HasMinimumDegreeAtLeast C.toSimpleGraph d := by
    intro x
    have hx := hCminNat x
    rw [natCard_neighborSet_eq_degree] at hx
    exact hx.le
  have hlocal : HasLocalExpansion C.toSimpleGraph n 2 :=
    hasLocalExpansion_of_copy_localSparsity Gamma C.toSimpleGraph
      hCGamma hsparse hCmin hfactor
  have hCcard : n < Fintype.card C := by
    by_contra hnot
    have hle : Fintype.card C ≤ n := Nat.le_of_not_gt hnot
    have hexp := hlocal (Finset.univ : Finset C) Finset.univ_nonempty hle
    have hempty : externalNeighborFinset C.toSimpleGraph
        (Finset.univ : Finset C) = ∅ := by
      ext x
      simp [externalNeighborFinset]
    rw [hempty] at hexp
    simp at hexp
  have hexpand : ∀ X : Finset C,
      n ≤ 2 * X.card → X.card ≤ n →
        n + 1 ≤ (externalNeighborhood C.toSimpleGraph X).card := by
    intro X hlow hupp
    have hXne : X.Nonempty := by
      exact Finset.card_pos.mp (by omega)
    have h := hlocal X hXne hupp
    rw [externalNeighborhood_eq_externalNeighborFinset]
    omega
  obtain ⟨x, c, hcycle, hlength⟩ :=
    krivelevich_long_cycle C.toSimpleGraph (a := n) (t := n + 1)
      hn (by omega) hCcard hexpand
  have hbipC : C.toSimpleGraph.IsBipartite := isBipartite_of_copy hbip hCJ
  let cFin : C.toSimpleGraph.Coloring (Fin 2) := Classical.choice hbipC
  let cBool : C.toSimpleGraph.Coloring Bool :=
    recolorOfEquiv C.toSimpleGraph finTwoEquiv cFin
  have heven : Even c.length := by
    apply (cBool.even_length_iff_congr c).2
    rfl
  refine ⟨q, i, hiOne, hiq, hqlog, ?_⟩
  exact ⟨S, C, hCconn, hCminNat, ⟨hCpairCopy⟩,
    x, c, hcycle, heven, hlength⟩

end LeanCo.SizeRamsey
