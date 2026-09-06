import LeanCo.HypercubeTuran.BaseGraph

/-!
# Deterministic consequences of pole concentration

This file contains the integer-counting part of the avoidance argument.  It
turns a bound on the total Hamming distance from one pole into a large second
distance layer, and then combines that conclusion with the independent-set
extraction supplied by the local colouring argument.
-/

open scoped SimpleGraph symmDiff BigOperators

namespace LeanCo.HypercubeTuran

open Finset SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The poles at Hamming distance exactly two from `w`. -/
def secondPoleLayer {ι : Type*} [DecidableEq ι]
    (A : V → Finset ι) (w : V) : Finset V :=
  Finset.univ.filter fun v => #(A v ∆ A w) = 2

@[simp]
theorem mem_secondPoleLayer {ι : Type*} [DecidableEq ι]
    {A : V → Finset ι} {w v : V} :
    v ∈ secondPoleLayer A w ↔ #(A v ∆ A w) = 2 := by
  simp [secondPoleLayer]

@[simp]
theorem center_not_mem_secondPoleLayer {ι : Type*} [DecidableEq ι]
    (A : V → Finset ι) (w : V) :
    w ∉ secondPoleLayer A w := by
  simp [secondPoleLayer]

/-- Away from the centre and the distance-two layer, an injective placement
whose distances from the centre are even has distance at least four. -/
theorem four_le_poleDistance_of_not_mem_secondPoleLayer
    {ι : Type*} [DecidableEq ι] {A : V → Finset ι} {w v : V}
    (hinj : Function.Injective A) (heven : Even #(A v ∆ A w))
    (hvw : v ≠ w) (hvL : v ∉ secondPoleLayer A w) :
    4 ≤ #(A v ∆ A w) := by
  have hpos : 0 < #(A v ∆ A w) := by
    have hne : A v ≠ A w := fun h => hvw (hinj h)
    simpa [Finset.card_pos, Finset.symmDiff_nonempty] using hne
  have hne_two : #(A v ∆ A w) ≠ 2 := by
    simpa using hvL
  obtain ⟨k, hk⟩ := heven
  omega

/-- The complement of the centre and its second distance layer. -/
private def fartherPoles {ι : Type*} [DecidableEq ι]
    (A : V → Finset ι) (w : V) : Finset V :=
  (Finset.univ.erase w) \ secondPoleLayer A w

private theorem secondPoleLayer_disjoint_fartherPoles
    {ι : Type*} [DecidableEq ι] (A : V → Finset ι) (w : V) :
    Disjoint (secondPoleLayer A w) (fartherPoles A w) := by
  exact Finset.disjoint_sdiff

private theorem secondPoleLayer_union_fartherPoles
    {ι : Type*} [DecidableEq ι] (A : V → Finset ι) (w : V) :
    secondPoleLayer A w ∪ fartherPoles A w = Finset.univ.erase w := by
  apply Finset.Subset.antisymm
  · intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      exact ne_of_mem_of_not_mem hv (center_not_mem_secondPoleLayer A w)
    · exact (Finset.mem_sdiff.mp hv).1
  · intro v hv
    by_cases hvL : v ∈ secondPoleLayer A w
    · exact Finset.mem_union_left _ hvL
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hv, hvL⟩)

private theorem card_secondPoleLayer_add_card_fartherPoles
    {ι : Type*} [DecidableEq ι] (A : V → Finset ι) (w : V) :
    #(secondPoleLayer A w) + #(fartherPoles A w) + 1 = Fintype.card V := by
  letI : Nonempty V := ⟨w⟩
  have hw : w ∈ (Finset.univ : Finset V) := Finset.mem_univ w
  have hcardPos : 0 < Fintype.card V := Fintype.card_pos
  have hcardErase : #(Finset.univ.erase w) + 1 = Fintype.card V := by
    rw [Finset.card_erase_of_mem hw, Finset.card_univ]
    omega
  have hunion := congrArg Finset.card (secondPoleLayer_union_fartherPoles A w)
  rw [Finset.card_union_of_disjoint (secondPoleLayer_disjoint_fartherPoles A w)] at hunion
  omega

private theorem weighted_layer_card_le_distance_sum
    {ι : Type*} [DecidableEq ι] {A : V → Finset ι} {w : V}
    (hinj : Function.Injective A)
    (heven : ∀ v : V, Even #(A v ∆ A w)) :
    2 * #(secondPoleLayer A w) + 4 * #(fartherPoles A w) ≤
      ∑ v : V, #(A v ∆ A w) := by
  let L := secondPoleLayer A w
  let R := fartherPoles A w
  have hL : ∑ _v ∈ L, 2 ≤ ∑ v ∈ L, #(A v ∆ A w) := by
    apply Finset.sum_le_sum
    intro v hv
    exact Nat.le_of_eq (mem_secondPoleLayer.mp hv).symm
  have hR : ∑ _v ∈ R, 4 ≤ ∑ v ∈ R, #(A v ∆ A w) := by
    apply Finset.sum_le_sum
    intro v hv
    have hv' := Finset.mem_sdiff.mp hv
    exact four_le_poleDistance_of_not_mem_secondPoleLayer hinj (heven v)
      (Finset.ne_of_mem_erase hv'.1) hv'.2
  have hsub : L ∪ R ⊆ (Finset.univ : Finset V) := Finset.subset_univ _
  have hsumSubset :
      ∑ v ∈ L ∪ R, #(A v ∆ A w) ≤ ∑ v : V, #(A v ∆ A w) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (by simp)
  have hdis : Disjoint L R := secondPoleLayer_disjoint_fartherPoles A w
  rw [Finset.sum_union hdis] at hsumSubset
  simpa [L, R, Nat.mul_comm] using
    (Nat.add_le_add hL hR |>.trans hsumSubset)

/-- A concentrated injective even-distance pole placement has many poles in
its second distance layer.  The additive `28` is the cost of the centre pole
in the integer calculation. -/
theorem three_mul_card_le_secondPoleLayer
    {ι : Type*} [DecidableEq ι] {A : V → Finset ι} {w : V}
    (hinj : Function.Injective A)
    (heven : ∀ v : V, Even #(A v ∆ A w))
    (hconcentration :
      7 * (∑ v : V, #(A v ∆ A w)) ≤ 25 * Fintype.card V) :
    3 * Fintype.card V ≤ 14 * #(secondPoleLayer A w) + 28 := by
  have hweighted := weighted_layer_card_le_distance_sum hinj heven
  have hcard := card_secondPoleLayer_add_card_fartherPoles A w
  have hscaled :
      7 * (2 * #(secondPoleLayer A w) + 4 * #(fartherPoles A w)) ≤
        25 * Fintype.card V := by
    exact (Nat.mul_le_mul_left 7 hweighted).trans hconcentration
  omega

/-- The final deterministic contradiction: concentration forces the second
layer to be large, while a Lemma-2.2-style extraction places it under twelve
times the size of an independent set. -/
theorem false_of_concentration_and_independent_extraction
    (G : SimpleGraph V) {ι : Type*} [DecidableEq ι]
    {A : V → Finset ι} {w : V} (hinj : Function.Injective A)
    (heven : ∀ v : V, Even #(A v ∆ A w))
    (hconcentration :
      7 * (∑ v : V, #(A v ∆ A w)) ≤ 25 * Fintype.card V)
    (hten : 10 ≤ Fintype.card V) (hsmall : HasSmallIndependentSets G)
    (I : Finset V) (hI_subset : I ⊆ secondPoleLayer A w)
    (hI_independent : G.IsIndepSet (I : Set V))
    (hLayer_le : #(secondPoleLayer A w) ≤ 12 * #I) : False := by
  have hlarge := three_mul_card_le_secondPoleLayer hinj heven hconcentration
  have hI_small := hsmall I hI_independent
  have _ := hI_subset
  omega

/-- Bundled form used by the main avoidance theorem.  It consumes
`HasPoleConcentration` directly; the remaining hypothesis is precisely the
local independent-set extraction that comes from the parity colouring. -/
theorem false_of_hasPoleConcentration_and_extraction
    (G : SimpleGraph V) (hconcentrated : HasPoleConcentration G)
    (hten : 10 ≤ Fintype.card V) (hsmall : HasSmallIndependentSets G)
    {ι : Type u} [Fintype ι] [DecidableEq ι] (A : V → Finset ι)
    (hplacement : IsPolePlacement G A)
    (hextract : ∀ w : V, ∃ I : Finset V,
      I ⊆ secondPoleLayer A w ∧ G.IsIndepSet (I : Set V) ∧
        #(secondPoleLayer A w) ≤ 12 * #I) : False := by
  obtain ⟨w, hsum, heven⟩ :=
    hconcentrated ι inferInstance inferInstance A hplacement
  obtain ⟨I, hI_subset, hI_independent, hLayer_le⟩ := hextract w
  exact false_of_concentration_and_independent_extraction G hplacement.1
    heven hsum hten hsmall I hI_subset hI_independent hLayer_le

end LeanCo.HypercubeTuran
