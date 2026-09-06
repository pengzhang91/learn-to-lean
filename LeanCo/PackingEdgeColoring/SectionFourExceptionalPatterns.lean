import LeanCo.PackingEdgeColoring.FaceBoundaryGirth

/-!
# Exceptional facial words produce honest thread pairs

This file closes the structural premise left abstract in
`SectionFourStructure`: under the short-boundary-path hypothesis and the
degree-two/degree-three partition, each exceptional six-letter facial word
really consists of two distinct thread arms at its unique degree-three
occurrence.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open SimpleGraph

noncomputable section

variable {V : Type*} {G : SimpleGraph V}

namespace RotationSystem

variable (R : RotationSystem G)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Definitional form of a facial vertex occurrence, exposed as a rewrite
lemma to avoid expensive dependent reduction in later pattern proofs. -/
theorem faceVertexAt_eq_boundaryPerm_pow (f : R.Face)
    (a : {a : G.Dart // a ∈ f.1.support}) (i : ℕ) :
    R.faceVertexAt f a i =
      (((R.faceBoundaryPerm f) ^ i) a).1.fst := rfl

/-- Iterating from a shifted facial occurrence adds the two offsets. -/
theorem faceVertexAt_pow_shift (f : R.Face)
    (a : {a : G.Dart // a ∈ f.1.support}) (m i : ℕ) :
    R.faceVertexAt f (((R.faceBoundaryPerm f) ^ m) a) i =
      R.faceVertexAt f a (m + i) := by
  unfold faceVertexAt
  congr 1
  rw [← Equiv.Perm.mul_apply]
  congr 1
  group

/-- Starting one occurrence earlier and taking `i+1` steps returns to the
same occurrence as taking `i` steps from the original base point. -/
theorem faceVertexAt_inv_shift_succ (f : R.Face)
    (a : {a : G.Dart // a ∈ f.1.support}) (i : ℕ) :
    R.faceVertexAt f ((R.faceBoundaryPerm f).symm a) (i + 1) =
      R.faceVertexAt f a i := by
  unfold faceVertexAt
  apply congrArg
    (fun x : {d : G.Dart // d ∈ f.1.support} ↦ x.1.fst)
  rw [← Equiv.Perm.mul_apply]
  congr 1
  change (R.faceBoundaryPerm f) ^ (i + 1) *
      (R.faceBoundaryPerm f)⁻¹ = (R.faceBoundaryPerm f) ^ i
  rw [pow_succ]
  group

/-- The analogous identity when the new base point is two occurrences
earlier. -/
theorem faceVertexAt_inv_sq_shift_add_two (f : R.Face)
    (a : {a : G.Dart // a ∈ f.1.support}) (i : ℕ) :
    R.faceVertexAt f
        ((R.faceBoundaryPerm f).symm
          ((R.faceBoundaryPerm f).symm a)) (i + 2) =
      R.faceVertexAt f a i := by
  unfold faceVertexAt
  apply congrArg
    (fun x : {d : G.Dart // d ∈ f.1.support} ↦ x.1.fst)
  rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply]
  congr 1
  change (R.faceBoundaryPerm f) ^ (i + 2) *
      (R.faceBoundaryPerm f)⁻¹ * (R.faceBoundaryPerm f)⁻¹ =
        (R.faceBoundaryPerm f) ^ i
  rw [show i + 2 = (i + 1) + 1 by omega, pow_succ, pow_succ]
  group

/-- Distinct indices on a certified short facial path give distinct ambient
vertices. -/
theorem faceVertexAt_ne_of_faceBoundaryPathAt
    (f : R.Face) (a : {a : G.Dart // a ∈ f.1.support}) (n i j : ℕ)
    (hpath : R.FaceBoundaryPathAt f a n)
    (hi : i ≤ n) (hj : j ≤ n) (hij : i ≠ j) :
    R.faceVertexAt f a i ≠ R.faceVertexAt f a j := by
  obtain ⟨v, p, hp, hlen, hverts⟩ := hpath
  intro heq
  apply hij
  apply hp.getVert_injOn
  · simpa only [Set.mem_setOf_eq, hlen] using hi
  · simpa only [Set.mem_setOf_eq, hlen] using hj
  · simpa only [hverts i hi, hverts j hj] using heq

/-- A four-window statement written directly in terms of ambient vertex
degrees and natural offsets from one facial occurrence. -/
theorem faceFourWindowHasThree_at
    (f : R.Face) (hfour : R.FaceFourWindowHasThree f)
    (a : {a : G.Dart // a ∈ f.1.support}) (m : ℕ) :
    G.degree (R.faceVertexAt f a m) = 3 ∨
      G.degree (R.faceVertexAt f a (m + 1)) = 3 ∨
      G.degree (R.faceVertexAt f a (m + 2)) = 3 ∨
      G.degree (R.faceVertexAt f a (m + 3)) = 3 := by
  have h := hfour (((R.faceBoundaryPerm f) ^ m) a)
  unfold faceThreeMarked at h
  rcases h with h | h | h | h
  · left
    change G.degree (((R.faceBoundaryPerm f) ^ m) a).1.fst = 3
    exact h
  · right; left
    rw [← R.faceVertexAt_pow_shift f a m 1]
    change G.degree
      ((R.faceBoundaryPerm f) (((R.faceBoundaryPerm f) ^ m) a)).1.fst = 3
    exact h
  · right; right; left
    rw [← R.faceVertexAt_pow_shift f a m 2]
    change G.degree
      (((R.faceBoundaryPerm f) ^ 2)
        (((R.faceBoundaryPerm f) ^ m) a)).1.fst = 3
    exact h
  · right; right; right
    rw [← R.faceVertexAt_pow_shift f a m 3]
    change G.degree
      (((R.faceBoundaryPerm f) ^ 3)
        (((R.faceBoundaryPerm f) ^ m) a)).1.fst = 3
    exact h

/-- The `2+3` exceptional word, expanded into ambient degree statements at
offsets zero through five. -/
theorem faceTwoThreePatternAt_degrees
    (f : R.Face) (a : {a : G.Dart // a ∈ f.1.support})
    (h : R.FaceTwoThreePatternAt f a) :
    (¬ G.degree (R.faceVertexAt f a 0) = 3) ∧
      (¬ G.degree (R.faceVertexAt f a 1) = 3) ∧
      G.degree (R.faceVertexAt f a 2) = 3 ∧
      (¬ G.degree (R.faceVertexAt f a 3) = 3) ∧
      (¬ G.degree (R.faceVertexAt f a 4) = 3) ∧
      (¬ G.degree (R.faceVertexAt f a 5) = 3) := by
  unfold FaceTwoThreePatternAt TwoThreePatternAt faceThreeMarked at h
  rcases h with ⟨h₀, h₁, h₂, h₃, h₄, h₅⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change ¬ G.degree (((R.faceBoundaryPerm f) ^ 0) a).1.fst = 3
    rw [show ((R.faceBoundaryPerm f) ^ 0) a = a by simp]
    exact h₀
  · change ¬ G.degree (((R.faceBoundaryPerm f) ^ 1) a).1.fst = 3
    rw [show ((R.faceBoundaryPerm f) ^ 1) a =
      (R.faceBoundaryPerm f) a by simp]
    exact h₁
  · exact h₂
  · exact h₃
  · exact h₄
  · exact h₅

/-- The reverse exceptional word, expanded into ambient degree statements. -/
theorem faceThreeTwoPatternAt_degrees
    (f : R.Face) (a : {a : G.Dart // a ∈ f.1.support})
    (h : R.FaceThreeTwoPatternAt f a) :
    (¬ G.degree (R.faceVertexAt f a 0) = 3) ∧
      (¬ G.degree (R.faceVertexAt f a 1) = 3) ∧
      (¬ G.degree (R.faceVertexAt f a 2) = 3) ∧
      G.degree (R.faceVertexAt f a 3) = 3 ∧
      (¬ G.degree (R.faceVertexAt f a 4) = 3) ∧
      (¬ G.degree (R.faceVertexAt f a 5) = 3) := by
  unfold FaceThreeTwoPatternAt ThreeTwoPatternAt faceThreeMarked at h
  rcases h with ⟨h₀, h₁, h₂, h₃, h₄, h₅⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change ¬ G.degree (((R.faceBoundaryPerm f) ^ 0) a).1.fst = 3
    rw [show ((R.faceBoundaryPerm f) ^ 0) a = a by simp]
    exact h₀
  · change ¬ G.degree (((R.faceBoundaryPerm f) ^ 1) a).1.fst = 3
    rw [show ((R.faceBoundaryPerm f) ^ 1) a =
      (R.faceBoundaryPerm f) a by simp]
    exact h₁
  · exact h₂
  · exact h₃
  · exact h₄
  · exact h₅

/-- Converse form used when an exceptional word is rebased by one facial
step. -/
theorem faceTwoThreePatternAt_of_degrees
    (f : R.Face) (a : {a : G.Dart // a ∈ f.1.support})
    (h₀ : ¬ G.degree (R.faceVertexAt f a 0) = 3)
    (h₁ : ¬ G.degree (R.faceVertexAt f a 1) = 3)
    (h₂ : G.degree (R.faceVertexAt f a 2) = 3)
    (h₃ : ¬ G.degree (R.faceVertexAt f a 3) = 3)
    (h₄ : ¬ G.degree (R.faceVertexAt f a 4) = 3)
    (h₅ : ¬ G.degree (R.faceVertexAt f a 5) = 3) :
    R.FaceTwoThreePatternAt f a := by
  rw [R.faceVertexAt_eq_boundaryPerm_pow] at h₀ h₁ h₂ h₃ h₄ h₅
  rw [show ((R.faceBoundaryPerm f) ^ 0) a = a by simp] at h₀
  rw [show ((R.faceBoundaryPerm f) ^ 1) a =
    (R.faceBoundaryPerm f) a by simp] at h₁
  unfold FaceTwoThreePatternAt TwoThreePatternAt faceThreeMarked
  exact ⟨h₀, h₁, h₂, h₃, h₄, h₅⟩

/-- In a `2+3` exceptional word, the three positions after the marked
occurrence extend (by the four-window property) to a genuine 3-thread. -/
theorem exists_forward_threeThread_of_faceTwoThreePatternAt
    (f : R.Face) (hshort : R.FaceShortBoundaryPaths f)
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hfour : R.FaceFourWindowHasThree f)
    (a : {a : G.Dart // a ∈ f.1.support})
    (hpattern : R.FaceTwoThreePatternAt f a) :
    ∃ (v : V) (p : G.Walk (R.faceVertexAt f a 2) v),
      IsKThread G p 3 ∧
        ∀ i, i ≤ 4 →
          p.getVert i = R.faceVertexAt f a (2 + i) := by
  rcases R.faceTwoThreePatternAt_degrees f a hpattern with
    ⟨h₀, h₁, h₂, h₃, h₄, h₅⟩
  have h₆ : G.degree (R.faceVertexAt f a 6) = 3 := by
    rcases R.faceFourWindowHasThree_at f hfour a 3 with
      h | h | h | h
    · exact (h₃ h).elim
    · exact (h₄ h).elim
    · exact (h₅ h).elim
    · simpa using h
  have htwo₃ : G.degree (R.faceVertexAt f a 3) = 2 :=
    (hdeg _).resolve_right h₃
  have htwo₄ : G.degree (R.faceVertexAt f a 4) = 2 :=
    (hdeg _).resolve_right h₄
  have htwo₅ : G.degree (R.faceVertexAt f a 5) = 2 :=
    (hdeg _).resolve_right h₅
  let b : {d : G.Dart // d ∈ f.1.support} :=
    ((R.faceBoundaryPerm f) ^ 2) a
  have hb₀ : R.faceVertexAt f b 0 = R.faceVertexAt f a 2 := by
    simpa only [b, Nat.add_zero] using
      R.faceVertexAt_pow_shift f a 2 0
  have hstart : G.degree (R.faceVertexAt f b 0) = 3 := by
    rw [hb₀]
    exact h₂
  have hend : G.degree (R.faceVertexAt f b (3 + 1)) = 3 := by
    rw [R.faceVertexAt_pow_shift f a 2 (3 + 1)]
    norm_num
    exact h₆
  have hint : ∀ i, 0 < i → i < 3 + 1 →
      G.degree (R.faceVertexAt f b i) = 2 := by
    intro i hi hil
    rw [R.faceVertexAt_pow_shift f a 2 i]
    interval_cases i
    · simpa using htwo₃
    · simpa using htwo₄
    · simpa using htwo₅
  have hex := R.exists_thread_of_faceBoundaryPathAt f b 3
    (hshort b 4 (by omega)) hstart hend hint
  rw [hb₀] at hex
  obtain ⟨v, p, hp, hverts⟩ := hex
  refine ⟨v, p, hp, ?_⟩
  intro i hi
  calc
    p.getVert i = R.faceVertexAt f b i := hverts i hi
    _ = R.faceVertexAt f a (2 + i) :=
      R.faceVertexAt_pow_shift f a 2 i

/-- The full graph-theoretic closure of the `2+3` exceptional word. -/
theorem longThreads_of_faceTwoThreePatternAt
    (f : R.Face) (hshort : R.FaceShortBoundaryPaths f)
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hfour : R.FaceFourWindowHasThree f)
    (a : {a : G.Dart // a ∈ f.1.support})
    (hpattern : R.FaceTwoThreePatternAt f a) :
    HasThreeAndLongThreadAt (G := G) (R.faceVertexAt f a 2) := by
  rcases R.faceTwoThreePatternAt_degrees f a hpattern with
    ⟨h₀, h₁, h₂, h₃, h₄, h₅⟩
  have htwo₀ : G.degree (R.faceVertexAt f a 0) = 2 :=
    (hdeg _).resolve_right h₀
  have htwo₁ : G.degree (R.faceVertexAt f a 1) = 2 :=
    (hdeg _).resolve_right h₁
  obtain ⟨vR, pR, hpR, hvertsR⟩ :=
    R.exists_forward_threeThread_of_faceTwoThreePatternAt
      f hshort hdeg hfour a hpattern
  have hpR₁ : pR.getVert 1 = R.faceVertexAt f a 3 := by
    simpa using hvertsR 1 (by omega)
  have hne₃₁ : R.faceVertexAt f a 3 ≠ R.faceVertexAt f a 1 :=
    R.faceVertexAt_ne_of_faceBoundaryPathAt f a 3 3 1
      (hshort a 3 (by omega)) (by omega) (by omega) (by omega)
  let b : {d : G.Dart // d ∈ f.1.support} :=
    (R.faceBoundaryPerm f).symm a
  have hb₁ : R.faceVertexAt f b 1 = R.faceVertexAt f a 0 := by
    simpa only [b, Nat.zero_add] using
      R.faceVertexAt_inv_shift_succ f a 0
  have hb₂ : R.faceVertexAt f b 2 = R.faceVertexAt f a 1 := by
    simpa only [b] using R.faceVertexAt_inv_shift_succ f a 1
  have hb₃ : R.faceVertexAt f b 3 = R.faceVertexAt f a 2 := by
    simpa only [b] using R.faceVertexAt_inv_shift_succ f a 2
  by_cases hprev : G.degree b.1.fst = 3
  · have hstart : G.degree (R.faceVertexAt f b 0) = 3 := by
      change G.degree (((R.faceBoundaryPerm f) ^ 0) b).1.fst = 3
      rw [show ((R.faceBoundaryPerm f) ^ 0) b = b by simp]
      exact hprev
    have hend : G.degree (R.faceVertexAt f b (2 + 1)) = 3 := by
      rw [hb₃]
      exact h₂
    have hint : ∀ i, 0 < i → i < 2 + 1 →
        G.degree (R.faceVertexAt f b i) = 2 := by
      intro i hi hil
      interval_cases i
      · rw [hb₁]
        exact htwo₀
      · rw [hb₂]
        exact htwo₁
    obtain ⟨vL, pL, hpL, hvertsL⟩ :=
      R.exists_thread_of_faceBoundaryPathAt f b 2
        (hshort b 3 (by omega)) hstart hend hint
    have hvL : vL = R.faceVertexAt f a 2 := by
      calc
        vL = pL.getVert pL.length := pL.getVert_length.symm
        _ = pL.getVert 3 := by rw [hpL.length]
        _ = R.faceVertexAt f b 3 := hvertsL 3 (by omega)
        _ = R.faceVertexAt f a 2 := hb₃
    subst vL
    have hpLrev₁ : pL.reverse.getVert 1 = R.faceVertexAt f a 1 := by
      calc
        pL.reverse.getVert 1 = pL.getVert (pL.length - 1) :=
          Walk.getVert_reverse pL 1
        _ = pL.getVert 2 := by rw [hpL.length]
        _ = R.faceVertexAt f b 2 := hvertsL 2 (by omega)
        _ = R.faceVertexAt f a 1 := hb₂
    left
    refine ⟨vR, R.faceVertexAt f b 0, pR, pL.reverse,
      hpR, hpL.reverse, ?_⟩
    rw [hpR₁, hpLrev₁]
    exact hne₃₁
  · have htwoPrev : G.degree (R.faceVertexAt f b 0) = 2 := by
      have hbzero : R.faceVertexAt f b 0 = b.1.fst := by
        change (((R.faceBoundaryPerm f) ^ 0) b).1.fst = b.1.fst
        rw [show ((R.faceBoundaryPerm f) ^ 0) b = b by simp]
      rw [hbzero]
      exact (hdeg _).resolve_right hprev
    let c : {d : G.Dart // d ∈ f.1.support} :=
      (R.faceBoundaryPerm f).symm b
    have hc₁ : R.faceVertexAt f c 1 = R.faceVertexAt f b 0 := by
      simpa only [c, Nat.zero_add] using
        R.faceVertexAt_inv_shift_succ f b 0
    have hc₂ : R.faceVertexAt f c 2 = R.faceVertexAt f a 0 := by
      simpa only [c, b, Nat.zero_add] using
        R.faceVertexAt_inv_sq_shift_add_two f a 0
    have hc₃ : R.faceVertexAt f c 3 = R.faceVertexAt f a 1 := by
      simpa only [c, b] using
        R.faceVertexAt_inv_sq_shift_add_two f a 1
    have hc₄ : R.faceVertexAt f c 4 = R.faceVertexAt f a 2 := by
      simpa only [c, b] using
        R.faceVertexAt_inv_sq_shift_add_two f a 2
    have hcMarked : G.degree (R.faceVertexAt f c 0) = 3 := by
      rcases R.faceFourWindowHasThree_at f hfour c 0 with
        h | h | h | h
      · simpa using h
      · norm_num at h
        rw [hc₁] at h
        omega
      · norm_num at h
        rw [hc₂] at h
        exact (h₀ h).elim
      · norm_num at h
        rw [hc₃] at h
        exact (h₁ h).elim
    have hstart : G.degree (R.faceVertexAt f c 0) = 3 := hcMarked
    have hend : G.degree (R.faceVertexAt f c (3 + 1)) = 3 := by
      rw [hc₄]
      exact h₂
    have hint : ∀ i, 0 < i → i < 3 + 1 →
        G.degree (R.faceVertexAt f c i) = 2 := by
      intro i hi hil
      interval_cases i
      · rw [hc₁]
        exact htwoPrev
      · rw [hc₂]
        exact htwo₀
      · rw [hc₃]
        exact htwo₁
    obtain ⟨vL, pL, hpL, hvertsL⟩ :=
      R.exists_thread_of_faceBoundaryPathAt f c 3
        (hshort c 4 (by omega)) hstart hend hint
    have hvL : vL = R.faceVertexAt f a 2 := by
      calc
        vL = pL.getVert pL.length := pL.getVert_length.symm
        _ = pL.getVert 4 := by rw [hpL.length]
        _ = R.faceVertexAt f c 4 := hvertsL 4 (by omega)
        _ = R.faceVertexAt f a 2 := hc₄
    subst vL
    have hpLrev₁ : pL.reverse.getVert 1 = R.faceVertexAt f a 1 := by
      calc
        pL.reverse.getVert 1 = pL.getVert (pL.length - 1) :=
          Walk.getVert_reverse pL 1
        _ = pL.getVert 3 := by rw [hpL.length]
        _ = R.faceVertexAt f c 3 := hvertsL 3 (by omega)
        _ = R.faceVertexAt f a 1 := hc₃
    right
    refine ⟨vR, R.faceVertexAt f c 0, pR, pL.reverse,
      hpR, hpL.reverse, ?_⟩
    rw [hpR₁, hpLrev₁]
    exact hne₃₁

/-- The reverse `3+2` exceptional word also closes to two distinct thread
arms.  If the next occurrence is unmarked, rebasing by one step reduces to
the preceding theorem; if it is marked, the two arms have lengths three and
two directly. -/
theorem longThreads_of_faceThreeTwoPatternAt
    (f : R.Face) (hshort : R.FaceShortBoundaryPaths f)
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hfour : R.FaceFourWindowHasThree f)
    (a : {a : G.Dart // a ∈ f.1.support})
    (hpattern : R.FaceThreeTwoPatternAt f a) :
    HasThreeAndLongThreadAt (G := G) (R.faceVertexAt f a 3) := by
  rcases R.faceThreeTwoPatternAt_degrees f a hpattern with
    ⟨h₀, h₁, h₂, h₃, h₄, h₅⟩
  have htwo₀ : G.degree (R.faceVertexAt f a 0) = 2 :=
    (hdeg _).resolve_right h₀
  have htwo₁ : G.degree (R.faceVertexAt f a 1) = 2 :=
    (hdeg _).resolve_right h₁
  have htwo₂ : G.degree (R.faceVertexAt f a 2) = 2 :=
    (hdeg _).resolve_right h₂
  have htwo₄ : G.degree (R.faceVertexAt f a 4) = 2 :=
    (hdeg _).resolve_right h₄
  have htwo₅ : G.degree (R.faceVertexAt f a 5) = 2 :=
    (hdeg _).resolve_right h₅
  by_cases h₆ : G.degree (R.faceVertexAt f a 6) = 3
  · let b : {d : G.Dart // d ∈ f.1.support} :=
      (R.faceBoundaryPerm f).symm a
    have hb₁ : R.faceVertexAt f b 1 = R.faceVertexAt f a 0 := by
      simpa only [b, Nat.zero_add] using
        R.faceVertexAt_inv_shift_succ f a 0
    have hb₂ : R.faceVertexAt f b 2 = R.faceVertexAt f a 1 := by
      simpa only [b] using R.faceVertexAt_inv_shift_succ f a 1
    have hb₃ : R.faceVertexAt f b 3 = R.faceVertexAt f a 2 := by
      simpa only [b] using R.faceVertexAt_inv_shift_succ f a 2
    have hb₄ : R.faceVertexAt f b 4 = R.faceVertexAt f a 3 := by
      simpa only [b] using R.faceVertexAt_inv_shift_succ f a 3
    have hbMarked : G.degree (R.faceVertexAt f b 0) = 3 := by
      rcases R.faceFourWindowHasThree_at f hfour b 0 with
        h | h | h | h
      · simpa using h
      · norm_num at h
        rw [hb₁] at h
        exact (h₀ h).elim
      · norm_num at h
        rw [hb₂] at h
        exact (h₁ h).elim
      · norm_num at h
        rw [hb₃] at h
        exact (h₂ h).elim
    have hleftStart : G.degree (R.faceVertexAt f b 0) = 3 := hbMarked
    have hleftEnd : G.degree (R.faceVertexAt f b (3 + 1)) = 3 := by
      rw [hb₄]
      exact h₃
    have hleftInternal : ∀ i, 0 < i → i < 3 + 1 →
        G.degree (R.faceVertexAt f b i) = 2 := by
      intro i hi hil
      interval_cases i
      · rw [hb₁]
        exact htwo₀
      · rw [hb₂]
        exact htwo₁
      · rw [hb₃]
        exact htwo₂
    obtain ⟨vL, pL, hpL, hvertsL⟩ :=
      R.exists_thread_of_faceBoundaryPathAt f b 3
        (hshort b 4 (by omega)) hleftStart hleftEnd hleftInternal
    have hvL : vL = R.faceVertexAt f a 3 := by
      calc
        vL = pL.getVert pL.length := pL.getVert_length.symm
        _ = pL.getVert 4 := by rw [hpL.length]
        _ = R.faceVertexAt f b 4 := hvertsL 4 (by omega)
        _ = R.faceVertexAt f a 3 := hb₄
    subst vL
    have hpLrev₁ : pL.reverse.getVert 1 = R.faceVertexAt f a 2 := by
      calc
        pL.reverse.getVert 1 = pL.getVert (pL.length - 1) :=
          Walk.getVert_reverse pL 1
        _ = pL.getVert 3 := by rw [hpL.length]
        _ = R.faceVertexAt f b 3 := hvertsL 3 (by omega)
        _ = R.faceVertexAt f a 2 := hb₃
    let d : {e : G.Dart // e ∈ f.1.support} :=
      ((R.faceBoundaryPerm f) ^ 3) a
    have hd₀ : R.faceVertexAt f d 0 = R.faceVertexAt f a 3 := by
      simpa only [d, Nat.add_zero] using
        R.faceVertexAt_pow_shift f a 3 0
    have hd₁ : R.faceVertexAt f d 1 = R.faceVertexAt f a 4 := by
      simpa only [d] using R.faceVertexAt_pow_shift f a 3 1
    have hd₂ : R.faceVertexAt f d 2 = R.faceVertexAt f a 5 := by
      simpa only [d] using R.faceVertexAt_pow_shift f a 3 2
    have hd₃ : R.faceVertexAt f d 3 = R.faceVertexAt f a 6 := by
      simpa only [d] using R.faceVertexAt_pow_shift f a 3 3
    have hrightStart : G.degree (R.faceVertexAt f d 0) = 3 := by
      rw [hd₀]
      exact h₃
    have hrightEnd : G.degree (R.faceVertexAt f d (2 + 1)) = 3 := by
      rw [hd₃]
      exact h₆
    have hrightInternal : ∀ i, 0 < i → i < 2 + 1 →
        G.degree (R.faceVertexAt f d i) = 2 := by
      intro i hi hil
      interval_cases i
      · rw [hd₁]
        exact htwo₄
      · rw [hd₂]
        exact htwo₅
    have hexR := R.exists_thread_of_faceBoundaryPathAt f d 2
      (hshort d 3 (by omega)) hrightStart hrightEnd hrightInternal
    rw [hd₀] at hexR
    obtain ⟨vR, pR, hpR, hvertsR⟩ := hexR
    have hpR₁ : pR.getVert 1 = R.faceVertexAt f a 4 := by
      calc
        pR.getVert 1 = R.faceVertexAt f d 1 := hvertsR 1 (by omega)
        _ = R.faceVertexAt f a 4 := hd₁
    have hne₂₄ : R.faceVertexAt f a 2 ≠ R.faceVertexAt f a 4 :=
      R.faceVertexAt_ne_of_faceBoundaryPathAt f a 4 2 4
        (hshort a 4 (by omega)) (by omega) (by omega) (by omega)
    left
    refine ⟨R.faceVertexAt f b 0, vR, pL.reverse, pR,
      hpL.reverse, hpR, ?_⟩
    rw [hpLrev₁, hpR₁]
    exact hne₂₄
  · let s : {d : G.Dart // d ∈ f.1.support} :=
      (R.faceBoundaryPerm f) a
    have hs₀ : R.faceVertexAt f s 0 = R.faceVertexAt f a 1 := by
      have h := R.faceVertexAt_pow_shift f a 1 0
      simpa only [s, pow_one, Nat.add_zero] using h
    have hs₁ : R.faceVertexAt f s 1 = R.faceVertexAt f a 2 := by
      have h := R.faceVertexAt_pow_shift f a 1 1
      simpa only [s, pow_one] using h
    have hs₂ : R.faceVertexAt f s 2 = R.faceVertexAt f a 3 := by
      have h := R.faceVertexAt_pow_shift f a 1 2
      simpa only [s, pow_one] using h
    have hs₃ : R.faceVertexAt f s 3 = R.faceVertexAt f a 4 := by
      have h := R.faceVertexAt_pow_shift f a 1 3
      simpa only [s, pow_one] using h
    have hs₄ : R.faceVertexAt f s 4 = R.faceVertexAt f a 5 := by
      have h := R.faceVertexAt_pow_shift f a 1 4
      simpa only [s, pow_one] using h
    have hs₅ : R.faceVertexAt f s 5 = R.faceVertexAt f a 6 := by
      have h := R.faceVertexAt_pow_shift f a 1 5
      simpa only [s, pow_one] using h
    have hshiftPattern : R.FaceTwoThreePatternAt f s := by
      apply R.faceTwoThreePatternAt_of_degrees f s
      · rw [hs₀]
        exact h₁
      · rw [hs₁]
        exact h₂
      · rw [hs₂]
        exact h₃
      · rw [hs₃]
        exact h₄
      · rw [hs₄]
        exact h₅
      · rw [hs₅]
        exact h₆
    have hlong := R.longThreads_of_faceTwoThreePatternAt
      f hshort hdeg hfour s hshiftPattern
    rw [hs₂] at hlong
    exact hlong

/-- Both exceptional facial patterns close to the honest forbidden thread
configurations; no additional embedding premise is needed. -/
theorem faceExceptionalPatternsFormLongThreads_of_short_paths
    (f : R.Face) (hshort : R.FaceShortBoundaryPaths f)
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hfour : R.FaceFourWindowHasThree f) :
    R.FaceExceptionalPatternsFormLongThreads f := by
  constructor
  · intro a hpattern
    exact R.longThreads_of_faceTwoThreePatternAt
      f hshort hdeg hfour a hpattern
  · intro a hpattern
    exact R.longThreads_of_faceThreeTwoPatternAt
      f hshort hdeg hfour a hpattern

/-- Closed structural-to-numerical interface for Section 4: short facial
paths, the degree partition, and the two graph-theoretic forbidden families
alone imply the six-window density bound. -/
theorem sixPathDensity_of_no_four_chain_and_no_long_thread_pair_closed
    (f : R.Face) (hshort : R.FaceShortBoundaryPaths f)
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hno4 : ∀ {u v : V} (p : G.Walk u v), ¬ IsKChain G p 4)
    (hforbid : ∀ u, ¬ HasThreeAndLongThreadAt (G := G) u) :
    2 * R.faceLength f ≤
      6 * (R.faceDegreeOccurrences f 3).card := by
  have hfour := R.faceFourWindowHasThree_of_no_four_chain
    f hshort hdeg hno4
  exact R.sixPathDensity_of_no_long_thread_pair f hfour
    (R.faceExceptionalPatternsFormLongThreads_of_short_paths
      f hshort hdeg hfour)
    hforbid

end Finite

end RotationSystem

end

end LeanCo.PackingEdgeColoring
