import LeanCo.PackingEdgeColoring.SectionFourLeafSwap

/-!
# Consolidated reduction for the Section 4 leaf lemma

All completed leaf branches are assembled here.  The theorem at the end
states the exact two local states still requiring palette repairs: both
nonleaf arms begin with two-vertices, or the matching arm begins with a
two-vertex, the other arm with a three-vertex, and the leaf edge has a
unique available induced colour.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open Finset SimpleGraph

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem leaf_three_extension_or_remaining_two_two_or_unique_two_three
    (hsub : IsSubcubic G) (hgirth : (16 : ℕ∞) ≤ G.egirth)
    {u v : V} (hu : G.degree u = 1) (huv : G.Adj u v)
    (hv : IsThreeVertex G v)
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 4)
    (hsmall : GoodFour (deleteLeafEdge G huv) small)
    (m : G.edgeSet)
    (hmD : m ∈ RetainedEdges (deleteLeafEdge G huv) G)
    (hm : leafBaseFour G huv small m = none)
    (hvm : v ∈ (m : Sym2 V)) :
    (∃ colour : G.edgeSet → OneTwoColor 4, GoodFour G colour) ∨
      ∃ (a b : V) (hva : G.Adj v a) (hvb : G.Adj v b)
          (beta : Fin 4),
        a ≠ b ∧ a ≠ u ∧ b ≠ u ∧
        G.neighborFinset v = {u, a, b} ∧
        IsTwoVertex G a ∧
        leafBaseFour G huv small
            (⟨s(v, a), hva⟩ : G.edgeSet) = none ∧
        leafBaseFour G huv small
            (⟨s(v, b), hvb⟩ : G.edgeSet) = some beta ∧
        (IsTwoVertex G b ∨
          (IsThreeVertex G b ∧
            ∃ i : Fin 4,
              ColorAvailableOn G
                (RetainedEdges (deleteLeafEdge G huv) G)
                (leafBaseFour G huv small)
                (⟨s(u, v), huv⟩ : G.edgeSet) (some i) ∧
              ∀ j : Fin 4,
                ColorAvailableOn G
                  (RetainedEdges (deleteLeafEdge G huv) G)
                  (leafBaseFour G huv small)
                  (⟨s(u, v), huv⟩ : G.edgeSet) (some j) → j = i)) := by
  rcases exists_goodFour_leaf_three_or_matching_two_normal_form G hsub hgirth
      hu huv hv small hsmall m hmD hm hvm with hgood | hnormal
  · exact Or.inl hgood
  · obtain ⟨a, b, hva, hvb, beta, hab, hau, hbu, hN, ha, hA, hB⟩ :=
      hnormal
    have hbPos : 0 < G.degree b := by
      rw [G.degree_pos_iff_exists_adj b]
      exact ⟨v, hvb.symm⟩
    have hbLe : G.degree b ≤ 3 := hsub b
    have hbCases : G.degree b = 1 ∨ G.degree b = 2 ∨ G.degree b = 3 := by
      omega
    rcases hbCases with hbOne | hbTwo | hbThree
    · left
      exact exists_goodFour_leaf_three_matching_two_other_leaf G hsub hu huv
        hv ha hbOne hva hvb hau hbu hab hN small hsmall beta hA hB
    · right
      exact ⟨a, b, hva, hvb, beta, hab, hau, hbu, hN, ha, hA, hB,
        Or.inl hbTwo⟩
    · rcases leaf_three_matching_two_other_three_unique_available_reduction
          G hsub hu huv hv ha hbThree hva hvb hau hbu hab hN small hsmall
          beta hA hB with hgood | hunique
      · exact Or.inl hgood
      · exact Or.inr ⟨a, b, hva, hvb, beta, hab, hau, hbu, hN, ha,
          hA, hB, Or.inr ⟨hbThree, hunique⟩⟩

end Finite

end

end LeanCo.PackingEdgeColoring
