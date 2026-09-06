import LeanCo.InversionDescent.SetPartition

/-!
# Literal restricted-growth words and set partitions

This file replaces the minimum-representative encoding used internally in
`SetPartition` by the paper's consecutive-label restricted-growth words.  We
use zero-based labels: every nonzero entry is one more than an earlier entry.
Thus the paper's one-based largest label is `max + 1` here.
-/

open scoped BigOperators

namespace LeanCo.RestrictedGrowth

open LeanCo.SetPartition

variable {n : ℕ}

/-- The literal zero-based restricted-growth condition. -/
def IsLiteralRGW (w : Fin n → ℕ) : Prop :=
  ∀ i, w i = 0 ∨ ∃ j, j < i ∧ w i = w j + 1

/-- Literal restricted-growth words of length `n`; the predicate is intrinsic
and is not defined by a range or by a bundled partition certificate. -/
abbrev LiteralRGW (n : ℕ) := {w : Fin n → ℕ // IsLiteralRGW w}

namespace Rank

/-- Zero-based rank of `x` among the members of `s`. -/
def inFinset (s : Finset (Fin n)) (x : Fin n) : ℕ :=
  (s.filter fun y ↦ y < x).card

theorem lt_of_mem {s : Finset (Fin n)} {x y : Fin n}
    (hx : x ∈ s) (hy : y ∈ s) (hxy : x < y) :
    inFinset s x < inFinset s y := by
  classical
  unfold inFinset
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · intro z hz
    simp only [Finset.mem_filter] at hz ⊢
    exact ⟨hz.1, hz.2.trans hxy⟩
  · intro heq
    have hxnot : x ∉ s.filter (fun z ↦ z < x) := by simp
    have hxmem : x ∈ s.filter (fun z ↦ z < y) := by simp [hx, hxy]
    rw [heq] at hxnot
    exact hxnot hxmem

theorem injOn (s : Finset (Fin n)) : Set.InjOn (inFinset s) s := by
  intro x hx y hy heq
  rcases lt_trichotomy x y with hxy | hxy | hyx
  · exact False.elim ((lt_of_mem hx hy hxy).ne heq)
  · exact hxy
  · exact False.elim ((lt_of_mem hy hx hyx).ne heq.symm)

/-- A positive rank has an immediately preceding member of the finite ordered
set. -/
theorem exists_predecessor {s : Finset (Fin n)} {r : Fin n}
    (hr : r ∈ s) (hpos : inFinset s r ≠ 0) :
    ∃ p, p ∈ s ∧ p < r ∧ inFinset s r = inFinset s p + 1 := by
  classical
  let t : Finset (Fin n) := s.filter fun z ↦ z < r
  have ht : t.Nonempty := by
    rw [← Finset.card_pos]
    change 0 < inFinset s r
    omega
  let p : Fin n := t.max' ht
  have hp_t : p ∈ t := Finset.max'_mem t ht
  have hp : p ∈ s ∧ p < r := by
    simpa [t] using hp_t
  have hsplit : t = insert p (s.filter fun z ↦ z < p) := by
    ext z
    constructor
    · intro hz
      by_cases hzp : z = p
      · simp [hzp]
      · have hzp_le : z ≤ p := Finset.le_max' t z hz
        have hzp_lt : z < p := lt_of_le_of_ne hzp_le hzp
        have hzs : z ∈ s := (by simpa [t] using hz : z ∈ s ∧ z < r).1
        simp [hzs, hzp_lt]
    · intro hz
      simp only [Finset.mem_insert] at hz
      rcases hz with rfl | hz
      · exact hp_t
      · have hzs : z ∈ s := (Finset.mem_filter.1 hz).1
        have hzp : z < p := (Finset.mem_filter.1 hz).2
        simp [t, hzs, hzp.trans hp.2]
  refine ⟨p, hp.1, hp.2, ?_⟩
  have hpnot : p ∉ s.filter (fun z ↦ z < p) := by simp
  change t.card = (s.filter fun z ↦ z < p).card + 1
  rw [hsplit, Finset.card_insert_of_notMem hpnot]

end Rank

namespace Canonical

/-- Consecutive zero-based label of the block containing `x`: the number of
block representatives strictly below its least representative. -/
def blockLabel (A : CanonicalPartition n) (x : Fin n) : ℕ :=
  Rank.inFinset A.representatives (A.rep x)

theorem blockLabel_rep (A : CanonicalPartition n) (x : Fin n) :
    blockLabel A (A.rep x) = blockLabel A x := by
  simp [blockLabel, A.rep_idem]

theorem blockLabel_lt_iff (A : CanonicalPartition n) (x y : Fin n) :
    blockLabel A x < blockLabel A y ↔ A.rep x < A.rep y := by
  constructor
  · intro hlabel
    rcases lt_trichotomy (A.rep x) (A.rep y) with h | h | h
    · exact h
    · simp [blockLabel, h] at hlabel
    · have hrank := Rank.lt_of_mem (A.rep_mem_representatives y)
        (A.rep_mem_representatives x) h
      exact False.elim ((not_lt_of_ge hrank.le) hlabel)
  · intro h
    exact Rank.lt_of_mem (A.rep_mem_representatives x)
      (A.rep_mem_representatives y) h

theorem blockLabel_eq_iff (A : CanonicalPartition n) (x y : Fin n) :
    blockLabel A x = blockLabel A y ↔ A.rep x = A.rep y := by
  constructor
  · intro hlabel
    exact Rank.injOn A.representatives
      (A.rep_mem_representatives x) (A.rep_mem_representatives y) hlabel
  · intro h
    simp [blockLabel, h]

theorem blockLabel_isLiteralRGW (A : CanonicalPartition n) :
    IsLiteralRGW (blockLabel A) := by
  intro x
  by_cases hzero : blockLabel A x = 0
  · exact Or.inl hzero
  · right
    obtain ⟨p, hp, hpr, hrank⟩ := Rank.exists_predecessor
      (A.rep_mem_representatives x) hzero
    refine ⟨p, hpr.trans_le (A.rep_le x), ?_⟩
    have hprep : A.rep p = p := (A.mem_representatives p).1 hp
    simpa [blockLabel, hprep] using hrank

/-- Relabel a canonical partition by consecutive labels in order of first
appearance. -/
def toLiteralRGW (A : CanonicalPartition n) : LiteralRGW n :=
  ⟨blockLabel A, blockLabel_isLiteralRGW A⟩

end Canonical

namespace LiteralRGW

/-- Positions carrying the same label as `x`. -/
def fiber (w : LiteralRGW n) (x : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun y ↦ w.1 y = w.1 x

@[simp]
theorem mem_fiber (w : LiteralRGW n) (x y : Fin n) :
    y ∈ w.fiber x ↔ w.1 y = w.1 x := by
  simp [fiber]

theorem fiber_nonempty (w : LiteralRGW n) (x : Fin n) :
    (w.fiber x).Nonempty :=
  ⟨x, by simp⟩

/-- First occurrence of the label at `x`. -/
noncomputable def first (w : LiteralRGW n) (x : Fin n) : Fin n :=
  (w.fiber x).min' (w.fiber_nonempty x)

theorem first_mem (w : LiteralRGW n) (x : Fin n) :
    w.first x ∈ w.fiber x :=
  Finset.min'_mem _ _

theorem value_first (w : LiteralRGW n) (x : Fin n) :
    w.1 (w.first x) = w.1 x := by
  exact (w.mem_fiber x (w.first x)).1 (w.first_mem x)

theorem first_eq_of_value_eq (w : LiteralRGW n) {x y : Fin n}
    (h : w.1 x = w.1 y) : w.first x = w.first y := by
  unfold first
  congr 1
  ext z
  simp [h]

theorem first_le (w : LiteralRGW n) (x : Fin n) : w.first x ≤ x := by
  unfold first
  apply Finset.min'_le
  simp

theorem fiber_first (w : LiteralRGW n) (x : Fin n) :
    w.fiber (w.first x) = w.fiber x := by
  ext y
  simp [w.value_first x]

theorem first_idem (w : LiteralRGW n) (x : Fin n) :
    w.first (w.first x) = w.first x := by
  exact w.first_eq_of_value_eq (w.value_first x)

/-- Partition a literal word by equal labels, choosing the first position of
each fiber as its canonical representative. -/
noncomputable def toCanonical (w : LiteralRGW n) : CanonicalPartition n where
  rep := w.first
  rep_le := w.first_le
  rep_idem := w.first_idem

theorem no_same_before_first (w : LiteralRGW n) (x y : Fin n)
    (hyx : y < w.first x) : w.1 y ≠ w.1 x := by
  intro heq
  have hy_mem : y ∈ w.fiber x := (w.mem_fiber x y).2 heq
  have hle : w.first x ≤ y := by
    unfold first
    exact Finset.min'_le _ _ hy_mem
  exact (not_lt_of_ge hle) hyx

/-- Every smaller label has already occurred. -/
theorem exists_value_before_of_lt (w : LiteralRGW n) :
    ∀ m : ℕ, ∀ x : Fin n, w.1 x = m → ∀ k < m,
      ∃ y, y < x ∧ w.1 y = k := by
  intro m
  induction m with
  | zero =>
      intro x hx k hk
      omega
  | succ m ih =>
      intro x hx k hk
      rcases w.2 x with hzero | ⟨j, hjx, hstep⟩
      · rw [hx] at hzero
        omega
      · have hj : w.1 j = m := by omega
        by_cases hkm : k = m
        · exact ⟨j, hjx, hj.trans hkm.symm⟩
        · have hklt : k < m := by omega
          obtain ⟨y, hyj, hyval⟩ := ih j hj k hklt
          exact ⟨y, hyj.trans hjx, hyval⟩

theorem value_lt_of_first_lt (w : LiteralRGW n) {x y : Fin n}
    (hx : w.first x = x) (hy : w.first y = y) (hxy : x < y) :
    w.1 x < w.1 y := by
  by_contra hnot
  have hyxval : w.1 y ≤ w.1 x := le_of_not_gt hnot
  rcases hyxval.eq_or_lt with heq | hlt
  · have hfirst := w.first_eq_of_value_eq heq.symm
    rw [hx, hy] at hfirst
    exact hxy.ne hfirst
  · obtain ⟨z, hzy, hz⟩ := w.exists_value_before_of_lt
      (w.1 x) x rfl (w.1 y) hlt
    have hsame : w.1 z = w.1 y := hz
    have hfirst := w.first_eq_of_value_eq hsame
    have hzfirst : w.first z ≤ z := w.first_le z
    rw [hy] at hfirst
    have : y ≤ z := hfirst ▸ hzfirst
    exact (not_lt_of_ge this) (hzy.trans hxy)

end LiteralRGW

namespace Canonical

theorem first_blockLabel (A : CanonicalPartition n) (x : Fin n) :
    (toLiteralRGW A).first x = A.rep x := by
  unfold LiteralRGW.first
  rw [Finset.min'_eq_iff]
  constructor
  · rw [LiteralRGW.mem_fiber]
    exact blockLabel_rep A x
  · intro y hy
    rw [LiteralRGW.mem_fiber] at hy
    have hrep : A.rep y = A.rep x :=
      (blockLabel_eq_iff A y x).1 hy
    rw [← hrep]
    exact A.rep_le y

@[simp]
theorem toCanonical_toLiteralRGW (A : CanonicalPartition n) :
    (toLiteralRGW A).toCanonical = A := by
  apply CanonicalPartition.ext
  funext x
  exact first_blockLabel A x

end Canonical

namespace LiteralRGW

theorem blockLabel_toCanonical (w : LiteralRGW n) (x : Fin n) :
    Canonical.blockLabel w.toCanonical x = w.1 x := by
  unfold Canonical.blockLabel Rank.inFinset
  change ((w.toCanonical.representatives.filter
    fun r ↦ r < w.first x)).card = w.1 x
  calc
    ((w.toCanonical.representatives.filter fun r ↦ r < w.first x)).card =
        (Finset.range (w.1 x)).card := by
      classical
      refine Finset.card_bij (fun r _ ↦ w.1 r) ?_ ?_ ?_
      · intro r hr
        rw [Finset.mem_range]
        have hr' := Finset.mem_filter.1 hr
        have hrrep : w.first r = r := by
          exact (CanonicalPartition.mem_representatives w.toCanonical r).1 hr'.1
        have hxrep : w.first (w.first x) = w.first x := w.first_idem x
        have hlt := w.value_lt_of_first_lt (x := r) (y := w.first x)
          hrrep hxrep hr'.2
        simpa [w.value_first x] using hlt
      · intro r₁ hr₁ r₂ hr₂ heq
        have hfirst := w.first_eq_of_value_eq heq
        have hr₁rep : w.first r₁ = r₁ :=
          (CanonicalPartition.mem_representatives w.toCanonical r₁).1
            (Finset.mem_filter.1 hr₁).1
        have hr₂rep : w.first r₂ = r₂ :=
          (CanonicalPartition.mem_representatives w.toCanonical r₂).1
            (Finset.mem_filter.1 hr₂).1
        simpa [hr₁rep, hr₂rep] using hfirst
      · intro k hk
        have hklt : k < w.1 x := Finset.mem_range.1 hk
        obtain ⟨y, hy, hyval⟩ := w.exists_value_before_of_lt
          (w.1 x) (w.first x) (w.value_first x) k hklt
        refine ⟨w.first y, ?_, ?_⟩
        · rw [Finset.mem_filter]
          constructor
          · rw [CanonicalPartition.mem_representatives]
            exact w.first_idem y
          · exact (w.first_le y).trans_lt hy
        · exact (w.value_first y).trans hyval
    _ = w.1 x := Finset.card_range _

@[simp]
theorem toLiteralRGW_toCanonical (w : LiteralRGW n) :
    Canonical.toLiteralRGW w.toCanonical = w := by
  apply Subtype.ext
  funext x
  exact w.blockLabel_toCanonical x

end LiteralRGW

/-- Canonical set partitions are equivalent to literal consecutive-label
restricted-growth words.  Both directions are explicit. -/
noncomputable def canonicalEquivLiteralRGW (n : ℕ) :
    CanonicalPartition n ≃ LiteralRGW n where
  toFun := Canonical.toLiteralRGW
  invFun := LiteralRGW.toCanonical
  left_inv := Canonical.toCanonical_toLiteralRGW
  right_inv := LiteralRGW.toLiteralRGW_toCanonical

noncomputable instance instFintypeLiteralRGW : Fintype (LiteralRGW n) :=
  Fintype.ofEquiv (CanonicalPartition n) (canonicalEquivLiteralRGW n)

/-! ## Statistics under consecutive relabelling -/

/-- Ordinary inversions of a literal restricted-growth word. -/
def inversionPairs (w : LiteralRGW n) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun xy ↦ xy.1 < xy.2 ∧ w.1 xy.2 < w.1 xy.1

def inversionNumber (w : LiteralRGW n) : ℕ :=
  (inversionPairs w).card

theorem inversionPairs_toLiteralRGW (A : CanonicalPartition n) :
    inversionPairs (Canonical.toLiteralRGW A) = A.wordInversionPairs := by
  ext xy
  rcases xy with ⟨x, y⟩
  simp only [inversionPairs, CanonicalPartition.wordInversionPairs,
    Finset.mem_filter, Finset.mem_univ, true_and]
  exact and_congr Iff.rfl (Canonical.blockLabel_lt_iff A y x)

theorem inversionNumber_toLiteralRGW (A : CanonicalPartition n) :
    inversionNumber (Canonical.toLiteralRGW A) = A.wordInversions := by
  rw [inversionNumber, CanonicalPartition.wordInversions,
    inversionPairs_toLiteralRGW]

/-- A label appearing at two distinct positions. -/
def RepeatedLabel (w : LiteralRGW n) (k : ℕ) : Prop :=
  ∃ x y, x ≠ y ∧ w.1 x = k ∧ w.1 y = k

noncomputable def repeatedLabels (w : LiteralRGW n) : Finset ℕ := by
  classical
  exact (Finset.univ.image w.1).filter (RepeatedLabel w)

noncomputable def repeatedLabelNumber (w : LiteralRGW n) : ℕ :=
  (repeatedLabels w).card

theorem repeatedLabels_toLiteralRGW (A : CanonicalPartition n) :
    repeatedLabels (Canonical.toLiteralRGW A) =
      A.repeatedRepresentatives.image (Canonical.blockLabel A) := by
  classical
  ext k
  constructor
  · intro hk
    rw [repeatedLabels, Finset.mem_filter] at hk
    rcases hk with ⟨_, x, y, hxy, hxk, hyk⟩
    have hrepeq : A.rep x = A.rep y :=
      (Canonical.blockLabel_eq_iff A x y).1 (hxk.trans hyk.symm)
    have hrmem : A.rep x ∈ A.repeatedRepresentatives := by
      rw [CanonicalPartition.repeatedRepresentatives, Finset.mem_filter]
      refine ⟨A.rep_mem_representatives x, ?_⟩
      by_cases hxrep : x = A.rep x
      · refine ⟨y, ?_, hrepeq.symm⟩
        intro hyrep
        exact hxy (hxrep.trans hyrep.symm)
      · exact ⟨x, hxrep, rfl⟩
    rw [Finset.mem_image]
    refine ⟨A.rep x, hrmem, ?_⟩
    exact (Canonical.blockLabel_rep A x).trans hxk
  · intro hk
    rw [Finset.mem_image] at hk
    obtain ⟨r, hr, hrk⟩ := hk
    rw [repeatedLabels, Finset.mem_filter]
    have hr' := (Finset.mem_filter.1
      (show r ∈ A.representatives.filter
        (fun r ↦ ∃ x, x ≠ r ∧ A.rep x = r) by
          simpa [CanonicalPartition.repeatedRepresentatives] using hr))
    obtain ⟨x, hxr, hxrep⟩ := hr'.2
    have hrrep : A.rep r = r :=
      (CanonicalPartition.mem_representatives A r).1 hr'.1
    constructor
    · rw [Finset.mem_image]
      exact ⟨r, by simp, hrk⟩
    · refine ⟨r, x, hxr.symm, hrk, ?_⟩
      have hlabel : Canonical.blockLabel A x = Canonical.blockLabel A r :=
        (Canonical.blockLabel_eq_iff A x r).2 (hxrep.trans hrrep.symm)
      exact hlabel.trans hrk

theorem repeatedLabelNumber_toLiteralRGW (A : CanonicalPartition n) :
    repeatedLabelNumber (Canonical.toLiteralRGW A) =
      A.repeatedRepresentatives.card := by
  classical
  rw [repeatedLabelNumber, repeatedLabels_toLiteralRGW]
  apply Finset.card_image_of_injOn
  intro x hx y hy hxy
  have hxrep : A.rep x = x := by
    apply (CanonicalPartition.mem_representatives A x).1
    exact (Finset.mem_filter.1
      (show x ∈ A.representatives.filter
        (fun r ↦ ∃ z, z ≠ r ∧ A.rep z = r) by
          simpa [CanonicalPartition.repeatedRepresentatives] using hx)).1
  have hyrep : A.rep y = y := by
    apply (CanonicalPartition.mem_representatives A y).1
    exact (Finset.mem_filter.1
      (show y ∈ A.representatives.filter
        (fun r ↦ ∃ z, z ≠ r ∧ A.rep z = r) by
          simpa [CanonicalPartition.repeatedRepresentatives] using hy)).1
  have := (Canonical.blockLabel_eq_iff A x y).1 hxy
  simpa [hxrep, hyrep] using this

theorem repeatedLabelNumber_eq_rp (A : CanonicalPartition n) :
    repeatedLabelNumber (Canonical.toLiteralRGW A) =
      CanonicalPartition.rp A.restrictedGrowthWord := by
  rw [repeatedLabelNumber_toLiteralRGW, CanonicalPartition.rp,
    CanonicalPartition.repeatedValues_restrictedGrowthWord]

/-- Set of labels occurring in a literal word. -/
def valueSet (w : LiteralRGW n) : Finset ℕ :=
  Finset.univ.image w.1

/-- In zero-based convention, this is the paper's largest one-based label.
For a nonempty literal word it is proved below to equal `max + 1`. -/
def largestLabelPlusOne (w : LiteralRGW n) : ℕ :=
  (valueSet w).card

theorem valueSet_toLiteralRGW (A : CanonicalPartition n) :
    valueSet (Canonical.toLiteralRGW A) =
      A.representatives.image (Canonical.blockLabel A) := by
  classical
  ext k
  constructor
  · intro hk
    rw [valueSet, Finset.mem_image] at hk
    obtain ⟨x, _, hx⟩ := hk
    rw [Finset.mem_image]
    refine ⟨A.rep x, A.rep_mem_representatives x, ?_⟩
    exact (Canonical.blockLabel_rep A x).trans hx
  · intro hk
    rw [Finset.mem_image] at hk
    obtain ⟨r, hr, hrk⟩ := hk
    rw [valueSet, Finset.mem_image]
    exact ⟨r, by simp, hrk⟩

theorem largestLabelPlusOne_toLiteralRGW (A : CanonicalPartition n) :
    largestLabelPlusOne (Canonical.toLiteralRGW A) = A.blockCount := by
  classical
  rw [largestLabelPlusOne, valueSet_toLiteralRGW,
    CanonicalPartition.blockCount]
  apply Finset.card_image_of_injOn
  intro x hx y hy hxy
  have hxrep : A.rep x = x :=
    (CanonicalPartition.mem_representatives A x).1 hx
  have hyrep : A.rep y = y :=
    (CanonicalPartition.mem_representatives A y).1 hy
  have := (Canonical.blockLabel_eq_iff A x y).1 hxy
  simpa [hxrep, hyrep] using this

theorem valueSet_nonempty (w : LiteralRGW n) [Nonempty (Fin n)] :
    (valueSet w).Nonempty := by
  classical
  exact ⟨w.1 (Classical.choice inferInstance), by
    simp [valueSet]⟩

/-- The zero-based label count really is maximum label plus one. -/
theorem largestLabelPlusOne_eq_max_add_one
    (w : LiteralRGW n) [Nonempty (Fin n)] :
    largestLabelPlusOne w =
      (valueSet w).max' (valueSet_nonempty w) + 1 := by
  classical
  let M : ℕ := (valueSet w).max' (valueSet_nonempty w)
  have hM : M ∈ valueSet w := Finset.max'_mem _ _
  have hset : valueSet w = Finset.range (M + 1) := by
    ext k
    constructor
    · intro hk
      rw [Finset.mem_range]
      have hle : k ≤ M := Finset.le_max' (valueSet w) k hk
      omega
    · intro hk
      have hkM : k ≤ M := by
        rw [Finset.mem_range] at hk
        omega
      rw [valueSet, Finset.mem_image] at hM
      obtain ⟨x, _, hxM⟩ := hM
      rw [valueSet, Finset.mem_image]
      by_cases hkeq : k = M
      · exact ⟨x, by simp, hxM.trans hkeq.symm⟩
      · have hklt : k < w.1 x := by omega
        obtain ⟨y, _, hy⟩ := w.exists_value_before_of_lt
          (w.1 x) x rfl k hklt
        exact ⟨y, by simp, hy⟩
  change (valueSet w).card = M + 1
  rw [hset, Finset.card_range]

/-! ## Paper-numbered consequences on the literal model -/

/-- Lemma 4.3 after consecutive relabelling. -/
theorem lemma_4_3 (A : CanonicalPartition n) :
    LeanCo.Permutation.inversionNumber A.standardPermutation =
      inversionNumber (Canonical.toLiteralRGW A) + n -
        largestLabelPlusOne (Canonical.toLiteralRGW A) := by
  calc
    LeanCo.Permutation.inversionNumber A.standardPermutation =
        A.standardInversions :=
      CanonicalPartition.standardPermutation_inversionNumber A
    _ = A.wordInversions + n - A.blockCount :=
      CanonicalPartition.lemma_4_3 A
    _ = inversionNumber (Canonical.toLiteralRGW A) + n -
        largestLabelPlusOne (Canonical.toLiteralRGW A) := by
      rw [inversionNumber_toLiteralRGW, largestLabelPlusOne_toLiteralRGW]

/-- Lemma 4.4 after consecutive relabelling. -/
theorem lemma_4_4 (A : CanonicalPartition n) :
    LeanCo.Permutation.descentNumber A.standardPermutation =
      repeatedLabelNumber (Canonical.toLiteralRGW A) := by
  calc
    LeanCo.Permutation.descentNumber A.standardPermutation = A.descentNumber :=
      CanonicalPartition.standardPermutation_descentNumber A
    _ = CanonicalPartition.rp A.restrictedGrowthWord :=
      CanonicalPartition.lemma_4_4 A
    _ = repeatedLabelNumber (Canonical.toLiteralRGW A) :=
      (repeatedLabelNumber_eq_rp A).symm

noncomputable def restrictedGrowthWeight {R : Type*} [CommSemiring R]
    (q t : R) (w : LiteralRGW n) : R :=
  q ^ (inversionNumber w + n - largestLabelPlusOne w) *
    t ^ repeatedLabelNumber w

theorem restrictedGrowthWeight_toLiteralRGW
    {R : Type*} [CommSemiring R] (q t : R) (A : CanonicalPartition n) :
    restrictedGrowthWeight q t (Canonical.toLiteralRGW A) =
      CanonicalPartition.restrictedGrowthWeight q t A := by
  rw [restrictedGrowthWeight, CanonicalPartition.restrictedGrowthWeight,
    inversionNumber_toLiteralRGW, largestLabelPlusOne_toLiteralRGW,
    repeatedLabelNumber_eq_rp, CanonicalPartition.largestLabel]

/-- **Theorem 4.5**, now with the genuine literal restricted-growth-word
subtype on the right-hand side. -/
theorem theorem_4_5 {R : Type*} [CommSemiring R] (q t : R) :
    (∑ σ : {σ : Equiv.Perm (Fin n) // LeanCo.Permutation.Avoids32_1 σ},
      q ^ LeanCo.Permutation.inversionNumber σ.1 *
        t ^ LeanCo.Permutation.descentNumber σ.1) =
      ∑ w : LiteralRGW n, restrictedGrowthWeight q t w := by
  classical
  calc
    (∑ σ : {σ : Equiv.Perm (Fin n) // LeanCo.Permutation.Avoids32_1 σ},
        q ^ LeanCo.Permutation.inversionNumber σ.1 *
          t ^ LeanCo.Permutation.descentNumber σ.1) =
        ∑ A : CanonicalPartition n,
          CanonicalPartition.restrictedGrowthWeight q t A :=
      CanonicalPartition.theorem_4_5 q t
    _ = ∑ A : CanonicalPartition n,
        restrictedGrowthWeight q t (Canonical.toLiteralRGW A) := by
      apply Fintype.sum_congr
      intro A
      exact (restrictedGrowthWeight_toLiteralRGW q t A).symm
    _ = ∑ w : LiteralRGW n, restrictedGrowthWeight q t w := by
      exact (canonicalEquivLiteralRGW n).sum_comp
        (fun w : LiteralRGW n ↦ restrictedGrowthWeight q t w)

end LeanCo.RestrictedGrowth
