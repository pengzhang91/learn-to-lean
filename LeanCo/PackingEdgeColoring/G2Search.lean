import LeanCo.PackingEdgeColoring.Counterexamples
import LeanCo.PackingEdgeColoring.VerifiedColorSearch

/-!
# Verified finite obstruction certificate for Figure 1(b)

The order below is chosen only to make the proved-complete backtracking search
prune early.  The final theorem is about the semantic packing-colouring
predicate, not about the implementation of the search.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring.Counterexamples

/-- Boolean compatibility with a partial indexed assignment. -/
def finitePairCompatibleWith {I C : Type*} [DecidableEq I]
    (compatible : I → I → C → C → Bool) (i : I) (c : C) :
    List (I × C) → Bool
  | [] => true
  | (j, d) :: rest =>
      (if j = i then true else compatible i j c d) &&
        finitePairCompatibleWith compatible i c rest

/-- Generic pruned search for a finite pairwise-constraint problem. -/
def finitePairColorSearch {I C : Type*} [DecidableEq I]
    (colors : List C) (compatible : I → I → C → C → Bool) :
    List I → List (I × C) → Bool
  | [], _ => true
  | i :: rest, assigned =>
      colors.any fun c ↦
        finitePairCompatibleWith compatible i c assigned &&
          finitePairColorSearch colors compatible rest ((i, c) :: assigned)

theorem finitePairCompatibleWith_eq_true_of_assignment
    {I C : Type*} [DecidableEq I]
    (compatible : I → I → C → C → Bool) (colour : I → C)
    (hcompatible : ∀ i j, i ≠ j →
      compatible i j (colour i) (colour j) = true)
    (i : I) (assigned : List (I × C))
    (hassigned : ∀ p ∈ assigned, p.2 = colour p.1) :
    finitePairCompatibleWith compatible i (colour i) assigned = true := by
  induction assigned with
  | nil => rfl
  | cons p rest ih =>
      simp only [finitePairCompatibleWith, Bool.and_eq_true]
      constructor
      · by_cases hpi : p.1 = i
        · simp [hpi]
        · rw [if_neg hpi, hassigned p (by simp)]
          exact hcompatible i p.1 (fun h ↦ hpi h.symm)
      · apply ih
        intro q hq
        exact hassigned q (by simp [hq])

theorem finitePairColorSearch_eq_true_of_assignment
    {I C : Type*} [DecidableEq I]
    (colors : List C) (compatible : I → I → C → C → Bool)
    (colour : I → C) (hcolors : ∀ i, colour i ∈ colors)
    (hcompatible : ∀ i j, i ≠ j →
      compatible i j (colour i) (colour j) = true)
    (indices : List I) (assigned : List (I × C))
    (hassigned : ∀ p ∈ assigned, p.2 = colour p.1) :
    finitePairColorSearch colors compatible indices assigned = true := by
  induction indices generalizing assigned with
  | nil => rfl
  | cons i rest ih =>
      simp only [finitePairColorSearch, List.any_eq_true]
      refine ⟨colour i, hcolors i, ?_⟩
      rw [Bool.and_eq_true]
      constructor
      · exact finitePairCompatibleWith_eq_true_of_assignment
          compatible colour hcompatible i assigned hassigned
      · apply ih ((i, colour i) :: assigned)
        intro p hp
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · rfl
        · exact hassigned p hp

/-- The paper's edge table, now indexed for fast reflected computation. -/
def G₂IndexedEdge : Fin 21 → G₂.edgeSet :=
  ![ ⟨s(0, 1), by decide⟩, ⟨s(1, 2), by decide⟩,
    ⟨s(2, 3), by decide⟩, ⟨s(3, 4), by decide⟩,
    ⟨s(4, 0), by decide⟩, ⟨s(5, 6), by decide⟩,
    ⟨s(6, 7), by decide⟩, ⟨s(7, 8), by decide⟩,
    ⟨s(8, 9), by decide⟩, ⟨s(9, 10), by decide⟩,
    ⟨s(10, 11), by decide⟩, ⟨s(11, 12), by decide⟩,
    ⟨s(12, 13), by decide⟩, ⟨s(13, 14), by decide⟩,
    ⟨s(14, 5), by decide⟩, ⟨s(0, 5), by decide⟩,
    ⟨s(1, 7), by decide⟩, ⟨s(2, 9), by decide⟩,
    ⟨s(3, 11), by decide⟩, ⟨s(4, 13), by decide⟩,
    ⟨s(8, 12), by decide⟩ ]

/-- Bit `j` records that indexed edges `i,j` cannot share the matching
colour. -/
def G₂MatchingConflictMask : Fin 21 → Nat :=
  ![98323, 196615, 393230, 786460, 557081, 49248, 65760,
    1114560, 1180544, 132864, 265728, 1317888, 1587200,
    552960, 57376, 49201, 65731, 131846, 265228, 536600, 1055104]

/-- Bit `j` records that indexed edges `i,j` cannot share an induced
colour. -/
def G₂InducedConflictMask : Fin 21 → Nat :=
  ![770303, 492511, 986911, 965663, 913471, 123121, 1163747,
    1252323, 1253318, 1445766, 1449740, 1851276, 1867160,
    1636408, 585841, 647291, 1278455, 1509263, 1973790,
    1898525, 2047936]

/-- Fast reflected compatibility table for `G₂`. -/
def G₂FastPairCompatible (i j : Fin 21)
    (a b : OneTwoColor 4) : Bool :=
  if a = b then
    match a with
    | none => !(G₂MatchingConflictMask i).testBit j
    | some _ => !(G₂InducedConflictMask i).testBit j
  else true

/-! ## A bucketed checker

The generic checker above compares a new edge with every already assigned
edge.  For the concrete obstruction there are only five colours, so it is
considerably cheaper for the kernel to retain one bucket per colour and only
inspect the bucket whose colour is being tried. -/

/-- Check a new index only against one fixed-colour bucket.  Repeated indices
are deliberately ignored, just as in `finitePairCompatibleWith`; this keeps
the completeness statement independent of the chosen search order. -/
def finiteClassCompatibleWith {I C : Type*} [DecidableEq I]
    (compatible : I → I → C → C → Bool) (i : I) (c : C) :
    List I → Bool
  | [] => true
  | j :: rest =>
      (if j = i then true else compatible i j c c) &&
        finiteClassCompatibleWith compatible i c rest

/-- Five-colour backtracking with one list per colour class. -/
def finiteFiveBucketColorSearch {I C : Type*} [DecidableEq I]
    (compatible : I → I → C → C → Bool)
    (c₀ c₁ c₂ c₃ c₄ : C) :
    List I → List I → List I → List I → List I → List I → Bool
  | [], _, _, _, _, _ => true
  | i :: rest, b₀, b₁, b₂, b₃, b₄ =>
      (finiteClassCompatibleWith compatible i c₀ b₀ &&
        finiteFiveBucketColorSearch compatible c₀ c₁ c₂ c₃ c₄
          rest (i :: b₀) b₁ b₂ b₃ b₄) ||
      (finiteClassCompatibleWith compatible i c₁ b₁ &&
        finiteFiveBucketColorSearch compatible c₀ c₁ c₂ c₃ c₄
          rest b₀ (i :: b₁) b₂ b₃ b₄) ||
      (finiteClassCompatibleWith compatible i c₂ b₂ &&
        finiteFiveBucketColorSearch compatible c₀ c₁ c₂ c₃ c₄
          rest b₀ b₁ (i :: b₂) b₃ b₄) ||
      (finiteClassCompatibleWith compatible i c₃ b₃ &&
        finiteFiveBucketColorSearch compatible c₀ c₁ c₂ c₃ c₄
          rest b₀ b₁ b₂ (i :: b₃) b₄) ||
      (finiteClassCompatibleWith compatible i c₄ b₄ &&
        finiteFiveBucketColorSearch compatible c₀ c₁ c₂ c₃ c₄
          rest b₀ b₁ b₂ b₃ (i :: b₄))

theorem finiteClassCompatibleWith_eq_true_of_assignment
    {I C : Type*} [DecidableEq I]
    (compatible : I → I → C → C → Bool) (colour : I → C)
    (hcompatible : ∀ i j, i ≠ j →
      compatible i j (colour i) (colour j) = true)
    (i : I) (c : C) (hi : colour i = c) (assigned : List I)
    (hassigned : ∀ j ∈ assigned, colour j = c) :
    finiteClassCompatibleWith compatible i c assigned = true := by
  induction assigned with
  | nil => rfl
  | cons j rest ih =>
      simp only [finiteClassCompatibleWith, Bool.and_eq_true]
      constructor
      · by_cases hji : j = i
        · simp [hji]
        · rw [if_neg hji]
          simpa [hi, hassigned j (by simp)] using
            hcompatible i j (fun h ↦ hji h.symm)
      · apply ih
        intro q hq
        exact hassigned q (by simp [hq])

/-- Semantic completeness of the bucketed five-colour checker. -/
theorem finiteFiveBucketColorSearch_eq_true_of_assignment
    {I C : Type*} [DecidableEq I]
    (compatible : I → I → C → C → Bool)
    (c₀ c₁ c₂ c₃ c₄ : C) (colour : I → C)
    (hcases : ∀ i, colour i = c₀ ∨ colour i = c₁ ∨ colour i = c₂ ∨
      colour i = c₃ ∨ colour i = c₄)
    (hcompatible : ∀ i j, i ≠ j →
      compatible i j (colour i) (colour j) = true)
    (indices b₀ b₁ b₂ b₃ b₄ : List I)
    (hb₀ : ∀ j ∈ b₀, colour j = c₀)
    (hb₁ : ∀ j ∈ b₁, colour j = c₁)
    (hb₂ : ∀ j ∈ b₂, colour j = c₂)
    (hb₃ : ∀ j ∈ b₃, colour j = c₃)
    (hb₄ : ∀ j ∈ b₄, colour j = c₄) :
    finiteFiveBucketColorSearch compatible c₀ c₁ c₂ c₃ c₄
      indices b₀ b₁ b₂ b₃ b₄ = true := by
  induction indices generalizing b₀ b₁ b₂ b₃ b₄ with
  | nil => rfl
  | cons i rest ih =>
      rcases hcases i with hi | hi | hi | hi | hi
      · have hc := finiteClassCompatibleWith_eq_true_of_assignment
          compatible colour hcompatible i c₀ hi b₀ hb₀
        have hr := ih (i :: b₀) b₁ b₂ b₃ b₄
          (by intro j hj; rcases List.mem_cons.mp hj with rfl | hj
              · exact hi
              · exact hb₀ j hj) hb₁ hb₂ hb₃ hb₄
        simp [finiteFiveBucketColorSearch, hc, hr]
      · have hc := finiteClassCompatibleWith_eq_true_of_assignment
          compatible colour hcompatible i c₁ hi b₁ hb₁
        have hr := ih b₀ (i :: b₁) b₂ b₃ b₄ hb₀
          (by intro j hj; rcases List.mem_cons.mp hj with rfl | hj
              · exact hi
              · exact hb₁ j hj) hb₂ hb₃ hb₄
        simp [finiteFiveBucketColorSearch, hc, hr]
      · have hc := finiteClassCompatibleWith_eq_true_of_assignment
          compatible colour hcompatible i c₂ hi b₂ hb₂
        have hr := ih b₀ b₁ (i :: b₂) b₃ b₄ hb₀ hb₁
          (by intro j hj; rcases List.mem_cons.mp hj with rfl | hj
              · exact hi
              · exact hb₂ j hj) hb₃ hb₄
        simp [finiteFiveBucketColorSearch, hc, hr]
      · have hc := finiteClassCompatibleWith_eq_true_of_assignment
          compatible colour hcompatible i c₃ hi b₃ hb₃
        have hr := ih b₀ b₁ b₂ (i :: b₃) b₄ hb₀ hb₁ hb₂
          (by intro j hj; rcases List.mem_cons.mp hj with rfl | hj
              · exact hi
              · exact hb₃ j hj) hb₄
        simp [finiteFiveBucketColorSearch, hc, hr]
      · have hc := finiteClassCompatibleWith_eq_true_of_assignment
          compatible colour hcompatible i c₄ hi b₄ hb₄
        have hr := ih b₀ b₁ b₂ b₃ (i :: b₄) hb₀ hb₁ hb₂ hb₃
          (by intro j hj; rcases List.mem_cons.mp hj with rfl | hj
              · exact hi
              · exact hb₄ j hj)
        simp [finiteFiveBucketColorSearch, hc, hr]

set_option maxHeartbeats 5000000 in
/-- The hand-written bit tables agree with the already proved generic Boolean
reflection.  This proposition mentions only equality of finite Booleans, so
its decision procedure has no proof-valued graph relation in its state. -/
theorem G₂FastPairCompatible_eq_pairCompatibleBool :
    ∀ i j a b, G₂FastPairCompatible i j a b =
      pairCompatibleBool G₂ (G₂IndexedEdge i) (G₂IndexedEdge j) a b := by
  decide

/-- The bit tables therefore agree exactly with the semantic graph
predicates. -/
theorem G₂FastPairCompatible_iff (i j : Fin 21) (a b : OneTwoColor 4) :
    G₂FastPairCompatible i j a b = true ↔
      PairCompatible G₂ (G₂IndexedEdge i) (G₂IndexedEdge j) a b := by
  rw [G₂FastPairCompatible_eq_pairCompatibleBool,
    pairCompatibleBool_eq_true_iff]

set_option maxHeartbeats 1000000 in
theorem G₂IndexedEdge_injective : Function.Injective G₂IndexedEdge := by
  decide

/-- Conflict-heavy variable order; this changes performance, not semantics. -/
def G₂SearchOrder : List (Fin 21) :=
  [0, 1, 2, 3, 4, 20, 7, 8, 11, 12, 16, 17, 18, 19, 15,
    6, 9, 10, 13, 5, 14]

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 1000000 in
/-- Kernel-reduced search certificate, checked by ordinary reduction. -/
theorem G₂_packingColorSearch_false :
    finiteFiveBucketColorSearch G₂FastPairCompatible
      none (some 0) (some 1) (some 2) (some 3)
      G₂SearchOrder [] [] [] [] [] = false := by
  decide

/-- Figure 1(b) has no `(1,2^4)` packing edge-colouring. -/
theorem G₂_not_hasOneTwoPackingEdgeColoring :
    ¬ HasOneTwoPackingEdgeColoring G₂ 4 := by
  rw [hasOneTwoPackingEdgeColoring_iff_exists_local]
  rintro ⟨colour, hcolour⟩
  let indexedColour : Fin 21 → OneTwoColor 4 :=
    fun i ↦ colour (G₂IndexedEdge i)
  have hsearch : finiteFiveBucketColorSearch G₂FastPairCompatible
      none (some 0) (some 1) (some 2) (some 3)
      G₂SearchOrder [] [] [] [] [] = true := by
    apply finiteFiveBucketColorSearch_eq_true_of_assignment
      (colour := indexedColour)
    · intro i
      cases h : indexedColour i with
      | none => simp
      | some c =>
          fin_cases c <;> simp
    · intro i j hij
      apply (G₂FastPairCompatible_iff i j (indexedColour i)
        (indexedColour j)).mpr
      exact hcolour (G₂IndexedEdge i) (by simp) (G₂IndexedEdge j) (by simp)
        (G₂IndexedEdge_injective.ne hij)
    all_goals simp
  rw [G₂_packingColorSearch_false] at hsearch
  contradiction

end LeanCo.PackingEdgeColoring.Counterexamples
