import LeanCo.SizeRamsey.GraphBasics

/-!
# Local sparsity forces local expansion

This file formalizes the deterministic implication (2) -> (3) in Lemma 2.1
of Wang--Wang.  The key point is the actual edge count: if
`U = S ∪ N_F(S)`, every edge of `F` incident with `S` is spanned by `U`, so
the sum of the degrees on `S` is at most twice the number of edges spanned by
`U`.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open Finset SimpleGraph

universe u

variable {V : Type u}

/-- If `U` contains `S` and every `F`-neighbour of a vertex of `S`, then the
degree sum on `S` is at most twice the number of `F`-edges spanned by `U`.

The factor two is deliberately retained: an edge whose two endpoints both
belong to `S` occurs twice in the degree sum. -/
theorem sum_degrees_le_twice_spannedEdgeCount (F : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel F.Adj]
    (S U : Finset V) (hSU : S ⊆ U)
    (hclosed : ∀ v ∈ S, F.neighborSet v ⊆ (U : Set V)) :
    (∑ v ∈ S, F.degree v) <= 2 * spannedEdgeCount F (U : Set V) := by
  let D : Finset F.Dart := Finset.univ.filter fun a => a.fst ∈ S
  have hmaps : (D : Set F.Dart).MapsTo (fun a => a.fst) (S : Set V) := by
    intro a ha
    simpa [D] using ha
  have hcardD : #D = ∑ v ∈ S, F.degree v := by
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    apply Finset.sum_congr rfl
    intro v hv
    have hfiber : {a ∈ D | a.fst = v} =
        Finset.univ.filter (fun a : F.Dart => a.fst = v) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro hav
        refine ⟨?_, hav⟩
        change a ∈ Finset.univ.filter (fun b : F.Dart => b.fst ∈ S)
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hav ▸ hv⟩
    rw [hfiber]
    change #({a : F.Dart | a.fst = v} : Finset F.Dart) = F.degree v
    exact F.dart_fst_fiber_card_eq_degree v
  have hfstS (a : {a // a ∈ D}) : a.1.fst ∈ S := by
    have ha : a.1 ∈ Finset.univ.filter (fun b : F.Dart => b.fst ∈ S) := by
      exact a.2
    exact (Finset.mem_filter.mp ha).2
  have hfstU (a : {a // a ∈ D}) : a.1.fst ∈ U := hSU (hfstS a)
  have hsndU (a : {a // a ∈ D}) : a.1.snd ∈ U :=
    hclosed a.1.fst (hfstS a) ((F.mem_neighborSet a.1.fst a.1.snd).mpr a.1.adj)
  let dartEmb : {a // a ∈ D} ↪ (F.induce (U : Set V)).Dart :=
    { toFun := fun a =>
        ⟨(⟨a.1.fst, hfstU a⟩, ⟨a.1.snd, hsndU a⟩), a.1.adj⟩
      inj' := by
        intro a b hab
        apply Subtype.ext
        apply Dart.ext
        apply Prod.ext
        · exact congrArg
            (fun z : (F.induce (U : Set V)).Dart => z.fst.1) hab
        · exact congrArg
            (fun z : (F.induce (U : Set V)).Dart => z.snd.1) hab }
  have hcard_le : #D <= Fintype.card (F.induce (U : Set V)).Dart := by
    simpa only [Fintype.card_coe] using
      Fintype.card_le_of_injective dartEmb dartEmb.injective
  calc
    (∑ v ∈ S, F.degree v) = #D := hcardD.symm
    _ <= Fintype.card (F.induce (U : Set V)).Dart := hcard_le
    _ = 2 * #(F.induce (U : Set V)).edgeFinset :=
      (F.induce (U : Set V)).dart_card_eq_twice_card_edges
    _ = 2 * spannedEdgeCount F (U : Set V) := by
      rw [spannedEdgeCount, edgeCount_eq_card_edgeFinset]

/-- Deterministic part of Wang--Wang Lemma 2.1.

Suppose `F` is a subgraph of `Gamma`, every set of at most `3*n` vertices in
`Gamma` spans at most `edgeFactor` times its cardinality edges, every vertex
of `F` has degree at least `d`, and `6 * edgeFactor < d`.  Then each nonempty
set of at most `n` vertices has more than twice as many external neighbours
in `F`.

The hypothesis `6 * edgeFactor < d` is the division-free form of the strict
inequality `d / 6 > edgeFactor` used in the paper. -/
theorem hasLocalExpansion_of_localSparsity
    {Gamma F : SimpleGraph V}
    [Fintype V] [DecidableEq V]
    [DecidableRel Gamma.Adj] [DecidableRel F.Adj]
    {n edgeFactor d : Nat}
    (hFGamma : F <= Gamma)
    (hsparse : IsLocallySparse Gamma (3 * n) edgeFactor)
    (hmin : HasMinimumDegreeAtLeast F d)
    (hfactor : 6 * edgeFactor < d) :
    HasLocalExpansion F n 2 := by
  intro S hS hSn
  let N : Finset V := externalNeighborFinset F S
  let U : Finset V := S ∪ N
  have hSpos : 0 < #S := Finset.card_pos.mpr hS
  have hSU : S ⊆ U := by
    intro v hv
    simp [U, hv]
  have hclosed : ∀ v ∈ S, F.neighborSet v ⊆ (U : Set V) := by
    intro v hv w hvw
    by_cases hwS : w ∈ S
    · simpa [U, hwS]
    · have hwN : w ∈ N := by
        change w ∈ externalNeighborFinset F S
        rw [mem_externalNeighborFinset]
        exact ⟨hwS, v, hv, (F.mem_neighborSet v w).mp hvw⟩
      simpa [U, hwN]
  by_contra hnot
  have hNcard : #N <= 2 * #S := by
    change #(externalNeighborFinset F S) <= 2 * #S
    exact Nat.le_of_not_gt hnot
  have hUcardS : #U <= 3 * #S := by
    calc
      #U <= #S + #N := by
        simpa [U] using Finset.card_union_le S N
      _ <= #S + 2 * #S := Nat.add_le_add_left hNcard #S
      _ = 3 * #S := by omega
  have hUcard : #U <= 3 * n :=
    hUcardS.trans (Nat.mul_le_mul_left 3 hSn)
  have hsparseU : spannedEdgeCount Gamma (U : Set V) <= edgeFactor * #U :=
    hsparse U hUcard
  have hdegreeSum : d * #S <= ∑ v ∈ S, F.degree v := by
    calc
      d * #S = ∑ _v ∈ S, d := by simp [Nat.mul_comm]
      _ <= ∑ v ∈ S, F.degree v := by
        exact Finset.sum_le_sum fun v _ => hmin v
  have hdegreeEdges : d * #S <= 2 * spannedEdgeCount F (U : Set V) :=
    hdegreeSum.trans
      (sum_degrees_le_twice_spannedEdgeCount F S U hSU hclosed)
  have hgraphMono : spannedEdgeCount F (U : Set V) <=
      spannedEdgeCount Gamma (U : Set V) :=
    spannedEdgeCount_mono_graph hFGamma (U : Set V)
  have hedgeUpper : 2 * spannedEdgeCount F (U : Set V) <=
      6 * edgeFactor * #S := by
    calc
      2 * spannedEdgeCount F (U : Set V) <=
          2 * spannedEdgeCount Gamma (U : Set V) :=
        Nat.mul_le_mul_left 2 hgraphMono
      _ <= 2 * (edgeFactor * #U) := Nat.mul_le_mul_left 2 hsparseU
      _ <= 2 * (edgeFactor * (3 * #S)) := by
        exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left edgeFactor hUcardS)
      _ = 6 * edgeFactor * #S := by ring
  have hstrict : 6 * edgeFactor * #S < d * #S :=
    Nat.mul_lt_mul_of_pos_right hfactor hSpos
  exact (Nat.not_lt_of_ge (hdegreeEdges.trans hedgeUpper)) hstrict

end LeanCo.SizeRamsey
