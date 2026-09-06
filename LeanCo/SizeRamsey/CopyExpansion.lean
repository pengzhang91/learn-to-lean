import LeanCo.SizeRamsey.HostExpansion
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-!
# Local expansion transported along graph copies

The paper freely regards a contained graph as a subgraph of its host.  Lean's
`SimpleGraph.Copy` permits different vertex types, so this file proves the
copy-invariant form of the deterministic implication in Lemma 2.1.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open Finset SimpleGraph

universe u v

variable {W : Type u} {V : Type v}

/-- Bipartiteness pulls back along an injective graph homomorphism (in fact,
injectivity is not needed for the colouring pullback). -/
theorem isBipartite_of_copy {F : SimpleGraph W}
    {Gamma : SimpleGraph V} (hGamma : Gamma.IsBipartite)
    (f : F.Copy Gamma) : F.IsBipartite := by
  obtain ⟨c⟩ := hGamma
  exact ⟨c.comp f.toHom⟩

/-- Restrict a graph copy to a finite vertex set in the source and its image
in the target. -/
def induceFinsetCopy {F : SimpleGraph W} {Gamma : SimpleGraph V}
    (f : F.Copy Gamma) (U : Finset W) :
    (F.induce (U : Set W)).Copy
      (Gamma.induce ((U.map f.toEmbedding : Finset V) : Set V)) where
  toHom :=
    { toFun := fun x =>
        ⟨f x.val, Finset.mem_map.mpr ⟨x.val, x.prop, rfl⟩⟩
      map_rel' := fun hxy => f.toHom.map_adj hxy }
  injective' := by
    intro x y hxy
    apply Subtype.ext
    exact f.injective (congrArg Subtype.val hxy)

/-- A copy cannot create more edges on a finite source set than the host
spans on its image. -/
theorem spannedEdgeCount_le_copy_image {F : SimpleGraph W}
    {Gamma : SimpleGraph V} [Finite V] (f : F.Copy Gamma) (U : Finset W) :
    spannedEdgeCount F (U : Set W) ≤
      spannedEdgeCount Gamma ((U.map f.toEmbedding : Finset V) : Set V) := by
  exact edgeCount_le_of_copy (induceFinsetCopy f U)

/-- Copy-invariant deterministic part of Wang--Wang Lemma 2.1.

If `Gamma` is sparse on every set of at most `3*n` vertices, then every
contained finite graph `F` of minimum degree at least `d` expands every
nonempty set of at most `n` vertices by a factor greater than two, provided
`6 * edgeFactor < d`. -/
theorem hasLocalExpansion_of_copy_localSparsity
    (Gamma : SimpleGraph V) [Fintype V]
    (F : SimpleGraph W) [Fintype W] [DecidableEq W] [DecidableRel F.Adj]
    {n edgeFactor d : Nat}
    (f : F.Copy Gamma)
    (hsparse : IsLocallySparse Gamma (3 * n) edgeFactor)
    (hmin : HasMinimumDegreeAtLeast F d)
    (hfactor : 6 * edgeFactor < d) :
    HasLocalExpansion F n 2 := by
  intro S hS hSn
  let N : Finset W := externalNeighborFinset F S
  let U : Finset W := S ∪ N
  let Uimage : Finset V := U.map f.toEmbedding
  have hSpos : 0 < #S := Finset.card_pos.mpr hS
  have hSU : S ⊆ U := by
    intro x hx
    simp [U, hx]
  have hclosed : ∀ x ∈ S, F.neighborSet x ⊆ (U : Set W) := by
    intro x hx y hxy
    by_cases hyS : y ∈ S
    · simpa [U, hyS]
    · have hyN : y ∈ N := by
        change y ∈ externalNeighborFinset F S
        rw [mem_externalNeighborFinset]
        exact ⟨hyS, x, hx, (F.mem_neighborSet x y).mp hxy⟩
      simpa [U, hyN]
  by_contra hnot
  have hNcard : #N ≤ 2 * #S := by
    change #(externalNeighborFinset F S) ≤ 2 * #S
    exact Nat.le_of_not_gt hnot
  have hUcardS : #U ≤ 3 * #S := by
    calc
      #U ≤ #S + #N := by
        simpa [U] using Finset.card_union_le S N
      _ ≤ #S + 2 * #S := Nat.add_le_add_left hNcard #S
      _ = 3 * #S := by omega
  have hUcard : #U ≤ 3 * n :=
    hUcardS.trans (Nat.mul_le_mul_left 3 hSn)
  have hUimageCard : #Uimage = #U := by
    simp [Uimage]
  have hUimageBound : #Uimage ≤ 3 * n := by
    simpa [hUimageCard] using hUcard
  have hsparseImage :
      spannedEdgeCount Gamma (Uimage : Set V) ≤ edgeFactor * #Uimage :=
    hsparse Uimage hUimageBound
  have hdegreeSum : d * #S ≤ ∑ x ∈ S, F.degree x := by
    calc
      d * #S = ∑ _x ∈ S, d := by simp [Nat.mul_comm]
      _ ≤ ∑ x ∈ S, F.degree x :=
        Finset.sum_le_sum fun x _ => hmin x
  have hdegreeEdges : d * #S ≤ 2 * spannedEdgeCount F (U : Set W) :=
    hdegreeSum.trans
      (sum_degrees_le_twice_spannedEdgeCount F S U hSU hclosed)
  have hcopyEdges : spannedEdgeCount F (U : Set W) ≤
      spannedEdgeCount Gamma (Uimage : Set V) := by
    exact spannedEdgeCount_le_copy_image f U
  have hedgeUpper : 2 * spannedEdgeCount F (U : Set W) ≤
      6 * edgeFactor * #S := by
    calc
      2 * spannedEdgeCount F (U : Set W) ≤
          2 * spannedEdgeCount Gamma (Uimage : Set V) :=
        Nat.mul_le_mul_left 2 hcopyEdges
      _ ≤ 2 * (edgeFactor * #Uimage) :=
        Nat.mul_le_mul_left 2 hsparseImage
      _ = 2 * (edgeFactor * #U) := by rw [hUimageCard]
      _ ≤ 2 * (edgeFactor * (3 * #S)) := by
        exact Nat.mul_le_mul_left 2
          (Nat.mul_le_mul_left edgeFactor hUcardS)
      _ = 6 * edgeFactor * #S := by ring
  have hstrict : 6 * edgeFactor * #S < d * #S :=
    Nat.mul_lt_mul_of_pos_right hfactor hSpos
  exact (Nat.not_lt_of_ge (hdegreeEdges.trans hedgeUpper)) hstrict

end LeanCo.SizeRamsey
