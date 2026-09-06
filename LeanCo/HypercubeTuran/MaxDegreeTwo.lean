import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Large independent sets in graphs of maximum degree two

The local graph arising in the proof of the hypercube subdivision lemma has
maximum degree at most two.  The only consequence needed downstream is the
elementary bound `alpha(G[L]) >= |L| / 3`.

We prove it by taking an inclusion-maximal independent subset `I` of `L`.
Maximality says that the closed neighborhoods of vertices of `I` cover `L`,
and the degree hypothesis bounds each such neighborhood by three vertices.
-/

open Finset SimpleGraph

namespace LeanCo.HypercubeTuran

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- A finite vertex set on which every vertex has at most two neighbors
contains an independent subset of at least one third of its size. -/
theorem exists_indepSet_card_third (G : SimpleGraph V) [DecidableRel G.Adj]
    (L : Finset V)
    (hdeg : ∀ v ∈ L, #(G.neighborFinset v ∩ L) ≤ 2) :
    ∃ I : Finset V,
      I ⊆ L ∧ G.IsIndepSet (I : Set V) ∧ #L ≤ 3 * #I := by
  let P : Finset V → Prop := fun I ↦ I ⊆ L ∧ G.IsIndepSet (I : Set V)
  have h_empty : P ∅ := by
    simp [P, SimpleGraph.isIndepSet_iff]
  obtain ⟨I, -, hImax⟩ := Finite.exists_le_maximal h_empty
  have hI : I ⊆ L ∧ G.IsIndepSet (I : Set V) := hImax.prop
  have hcover : L ⊆ I.biUnion (fun i ↦ insert i (G.neighborFinset i ∩ L)) := by
    intro v hv
    by_cases hvI : v ∈ I
    · exact mem_biUnion.2 ⟨v, hvI, mem_insert_self v _⟩
    · have hadj : ∃ i ∈ I, G.Adj i v := by
        by_contra hnone
        have hno : ∀ i ∈ I, ¬G.Adj i v := by
          intro i hi hiv
          exact hnone ⟨i, hi, hiv⟩
        have hind_insert : G.IsIndepSet ((insert v I : Finset V) : Set V) := by
          rw [Finset.coe_insert]
          apply Set.Pairwise.insert hI.2
          intro i hi _hne
          exact ⟨fun hvi ↦ hno i hi hvi.symm, hno i hi⟩
        have hP_insert : P (insert v I) :=
          ⟨insert_subset hv hI.1, hind_insert⟩
        exact hImax.not_prop_of_gt (ssubset_insert hvI) hP_insert
      obtain ⟨i, hi, hiv⟩ := hadj
      exact mem_biUnion.2 ⟨i, hi, by simp [hiv, hv]⟩
  refine ⟨I, hI.1, hI.2, ?_⟩
  calc
    #L ≤ #(I.biUnion (fun i ↦ insert i (G.neighborFinset i ∩ L))) :=
      card_le_card hcover
    _ ≤ #I * 3 := card_biUnion_le_card_mul I
      (fun i ↦ insert i (G.neighborFinset i ∩ L)) 3 (by
        intro i hi
        have hiL : i ∈ L := hI.1 hi
        have hn := hdeg i hiL
        calc
          #(insert i (G.neighborFinset i ∩ L)) ≤
              #(G.neighborFinset i ∩ L) + 1 := card_insert_le _ _
          _ ≤ 3 := by omega)
    _ = 3 * #I := Nat.mul_comm _ _

end LeanCo.HypercubeTuran
