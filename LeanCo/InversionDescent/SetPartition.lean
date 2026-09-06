import LeanCo.InversionDescent.Permutation

/-!
# Set partitions, standard block words, and restricted-growth words

This file formalizes the finite combinatorics in Section 4 of Pan's paper.  We use a
particularly convenient canonical representation of a set partition: `rep x` is the
least element in the block containing `x`.  Thus `rep x ≤ x` and `rep (rep x) = rep x`.
The representation is proved equivalent to mathlib's
`Finpartition (Finset.univ : Finset (Fin n))` below.

The paper's standard block word puts the representative last in its block, puts the
other elements in increasing order, and orders blocks by their representatives.  The
lexicographic key `blockKey` records exactly that order.  This formulation avoids any
dependence on an implementation-specific sorting algorithm.
-/

open scoped BigOperators

namespace LeanCo.SetPartition

variable {n : ℕ}

abbrev SetPartition (n : ℕ) :=
  Finpartition (Finset.univ : Finset (Fin n))

/-! ## A canonical, minimum-representative model of set partitions -/

/-- A set partition encoded by the least member of each block. -/
structure CanonicalPartition (n : ℕ) where
  /-- `rep x` is the least element in the block of `x`. -/
  rep : Fin n → Fin n
  rep_le : ∀ x, rep x ≤ x
  rep_idem : ∀ x, rep (rep x) = rep x

namespace CanonicalPartition

@[ext]
theorem ext {A B : CanonicalPartition n} (h : A.rep = B.rep) : A = B := by
  cases A
  cases B
  simp_all

/-- The block containing `x`. -/
def block (A : CanonicalPartition n) (x : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun y ↦ A.rep y = A.rep x

@[simp]
theorem mem_block (A : CanonicalPartition n) (x y : Fin n) :
    y ∈ A.block x ↔ A.rep y = A.rep x := by
  simp [block]

@[simp]
theorem rep_mem_block (A : CanonicalPartition n) (x : Fin n) :
    A.rep x ∈ A.block x := by
  simp [A.rep_idem]

@[simp]
theorem self_mem_block (A : CanonicalPartition n) (x : Fin n) :
    x ∈ A.block x := by
  simp

theorem rep_eq_self_iff (A : CanonicalPartition n) (x : Fin n) :
    A.rep x = x ↔ ∀ y, y ∈ A.block x → x ≤ y := by
  constructor
  · intro hx y hy
    rw [mem_block] at hy
    calc
      x = A.rep x := hx.symm
      _ = A.rep y := hy.symm
      _ ≤ y := A.rep_le y
  · intro h
    exact le_antisymm (A.rep_le x) (h (A.rep x) (A.rep_mem_block x))

/-- The set of block representatives, hence one element for every block. -/
def representatives (A : CanonicalPartition n) : Finset (Fin n) :=
  Finset.univ.filter fun x ↦ A.rep x = x

@[simp]
theorem mem_representatives (A : CanonicalPartition n) (x : Fin n) :
    x ∈ A.representatives ↔ A.rep x = x := by
  simp [representatives]

theorem rep_mem_representatives (A : CanonicalPartition n) (x : Fin n) :
    A.rep x ∈ A.representatives := by
  simp [A.rep_idem]

/-- Number of blocks. -/
def blockCount (A : CanonicalPartition n) : ℕ :=
  A.representatives.card

/-- The equivalence relation whose classes are the fibers of `rep`. -/
def setoid (A : CanonicalPartition n) : Setoid (Fin n) where
  r x y := A.rep x = A.rep y
  iseqv := by
    constructor
    · exact fun _ ↦ rfl
    · exact fun h ↦ h.symm
    · exact fun hxy hyz ↦ hxy.trans hyz

/-- Forget the canonical labels and retain mathlib's finite partition. -/
noncomputable def toFinpartition (A : CanonicalPartition n) : SetPartition n := by
  classical
  exact Finpartition.ofSetoid A.setoid

@[simp]
theorem mem_part_toFinpartition_iff (A : CanonicalPartition n) (x y : Fin n) :
    y ∈ A.toFinpartition.part x ↔ A.rep x = A.rep y := by
  classical
  change y ∈ (Finpartition.ofSetoid A.setoid).part x ↔ _
  rw [Finpartition.mem_part_ofSetoid_iff_rel]
  rfl

/-- The least member of the part of `x` in a mathlib `Finpartition`. -/
noncomputable def finpartitionRep (P : SetPartition n) (x : Fin n) : Fin n :=
  (P.part x).min' ((P.part_nonempty).2 (by simp))

theorem finpartitionRep_mem (P : SetPartition n) (x : Fin n) :
    finpartitionRep P x ∈ P.part x := by
  exact Finset.min'_mem _ _

theorem finpartitionRep_le (P : SetPartition n) (x : Fin n) :
    finpartitionRep P x ≤ x := by
  exact Finset.min'_le _ _ (P.mem_part (by simp))

theorem part_finpartitionRep (P : SetPartition n) (x : Fin n) :
    P.part (finpartitionRep P x) = P.part x := by
  exact P.part_eq_of_mem (P.part_mem.2 (by simp)) (finpartitionRep_mem P x)

theorem finpartitionRep_idem (P : SetPartition n) (x : Fin n) :
    finpartitionRep P (finpartitionRep P x) = finpartitionRep P x := by
  change (P.part (finpartitionRep P x)).min' _ = finpartitionRep P x
  rw [Finset.min'_eq_iff]
  constructor
  · exact P.mem_part (by simp)
  · intro y hy
    apply Finset.min'_le
    rw [part_finpartitionRep] at hy
    exact hy

/-- Put the canonical minimum representative on every part of `P`. -/
noncomputable def ofFinpartition (P : SetPartition n) : CanonicalPartition n where
  rep := finpartitionRep P
  rep_le := finpartitionRep_le P
  rep_idem := finpartitionRep_idem P

theorem finpartitionRep_toFinpartition (A : CanonicalPartition n) (x : Fin n) :
    finpartitionRep A.toFinpartition x = A.rep x := by
  apply le_antisymm
  · apply Finset.min'_le
    simpa [mem_part_toFinpartition_iff, A.rep_idem]
  · apply Finset.le_min'
    intro y hy
    rw [mem_part_toFinpartition_iff] at hy
    exact hy.trans_le (A.rep_le y)

@[simp]
theorem ofFinpartition_toFinpartition (A : CanonicalPartition n) :
    ofFinpartition A.toFinpartition = A := by
  apply ext
  funext x
  exact finpartitionRep_toFinpartition A x

private theorem finpartition_eq_of_parts_eq
    {P Q : SetPartition n} (h : ∀ x, P.part x = Q.part x) : P = Q := by
  apply Finpartition.ext
  ext a
  constructor
  · intro ha
    obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts ha
    have hpa : P.part x = a := P.part_eq_of_mem ha hx
    rw [← hpa, h]
    exact Q.part_mem.2 (by simp)
  · intro ha
    obtain ⟨x, hx⟩ := Q.nonempty_of_mem_parts ha
    have hqa : Q.part x = a := Q.part_eq_of_mem ha hx
    rw [← hqa, ← h]
    exact P.part_mem.2 (by simp)

@[simp]
theorem toFinpartition_ofFinpartition (P : SetPartition n) :
    (ofFinpartition P).toFinpartition = P := by
  apply finpartition_eq_of_parts_eq
  intro x
  apply Finset.ext
  intro y
  rw [mem_part_toFinpartition_iff]
  change finpartitionRep P x = finpartitionRep P y ↔ y ∈ P.part x
  constructor
  · intro h
    have hp : P.part y = P.part x := by
      rw [← part_finpartitionRep P y, ← part_finpartitionRep P x, h]
    rw [← hp]
    exact P.mem_part (by simp)
  · intro h
    have hp : P.part y = P.part x :=
      (P.part_eq_iff_mem (P.part_mem.2 (by simp))).2 h
    unfold finpartitionRep
    simpa [hp]

/-- Canonical minimum-representative words are exactly mathlib finite partitions. -/
noncomputable def finpartitionEquiv (n : ℕ) :
    CanonicalPartition n ≃ SetPartition n where
  toFun := toFinpartition
  invFun := ofFinpartition
  left_inv := ofFinpartition_toFinpartition
  right_inv := toFinpartition_ofFinpartition

noncomputable instance instFintypeCanonicalPartition : Fintype (CanonicalPartition n) :=
  Fintype.ofEquiv (SetPartition n) (finpartitionEquiv n).symm

/-! ## The standard block word and genuine `32-1` avoidance -/

/-- `x` occurs before `y` in the paper's standard block word.  The first
disjunct orders blocks by their least elements.  Inside a block, the two
remaining disjuncts put all non-minimal elements in increasing order and put
the minimum last. -/
def standardBefore (A : CanonicalPartition n) (x y : Fin n) : Prop :=
  A.rep x < A.rep y ∨
    A.rep x = A.rep y ∧
      ((A.rep x ≠ x ∧ A.rep y = y) ∨
        (A.rep x ≠ x ∧ A.rep y ≠ y ∧ x < y))

/-- Φ, represented extensionally by the order in which values occur.  For a
permutation word this order relation determines the word uniquely. -/
def Φ (A : CanonicalPartition n) : Fin n → Fin n → Prop :=
  A.standardBefore

theorem rep_le_of_standardBefore (A : CanonicalPartition n) {x y : Fin n}
    (h : A.standardBefore x y) : A.rep x ≤ A.rep y := by
  rcases h with h | h
  · exact h.le
  · exact h.1.le

/-- Adjacency in a strict ordering relation. -/
def AdjacentInOrder (r : α → α → Prop) (x y : α) : Prop :=
  r x y ∧ ∀ z, r x z → ¬ r z y

/-- A vincular `32-1` occurrence: `x,y` are adjacent and `z` occurs later. -/
def Occurs32_1Order [LT α] (r : α → α → Prop) : Prop :=
  ∃ x y z, AdjacentInOrder r x y ∧ r y z ∧ y < x ∧ z < y

/-- Genuine avoidance, stated as the negation of the pattern occurrence. -/
def Avoids32_1Order [LT α] (r : α → α → Prop) : Prop :=
  ¬ Occurs32_1Order r

/-- The forward (avoidance) half of Theorem 4.2.  This is not a range-based
definition: `Avoids32_1Order` is the literal vincular-pattern predicate. -/
theorem standardBefore_avoids32_1 (A : CanonicalPartition n) :
    Avoids32_1Order A.standardBefore := by
  rintro ⟨x, y, z, hxy, hyz, hyx, hzy⟩
  rcases hxy.1 with hcross | ⟨hsame, hinside⟩
  · by_cases hx : A.rep x = x
    · have : x < y := by
        calc
          x = A.rep x := hx.symm
          _ < A.rep y := hcross
          _ ≤ y := A.rep_le y
      exact (not_lt_of_ge hyx.le) this
    · have hxrep : A.standardBefore x (A.rep x) := by
        right
        exact ⟨(A.rep_idem x).symm, Or.inl ⟨hx, A.rep_idem x⟩⟩
      have hrepy : A.standardBefore (A.rep x) y := by
        left
        simpa [A.rep_idem x] using hcross
      exact hxy.2 (A.rep x) hxrep hrepy
  · have hy_rep : A.rep y = y := by
      rcases hinside with ⟨_, hy⟩ | ⟨_, _, hlt⟩
      · exact hy
      · exact False.elim ((not_lt_of_ge hyx.le) hlt)
    rcases hyz with hcross | ⟨hsame', hinside'⟩
    · have : y < z := by
        calc
          y = A.rep y := hy_rep.symm
          _ < A.rep z := hcross
          _ ≤ z := A.rep_le z
      exact (not_lt_of_ge this.le) hzy
    · rcases hinside' with ⟨hy_not, _⟩ | ⟨hy_not, _⟩
      · exact hy_not hy_rep
      · exact hy_not hy_rep

/-! ### The after-cut inverse (Theorem 4.2) -/

/-- The suffix beginning at `x`, expressed using an occurrence-order relation. -/
noncomputable def suffixSet (r : Fin n → Fin n → Prop) (x : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun y ↦ y = x ∨ r x y

@[simp]
theorem mem_suffixSet (r : Fin n → Fin n → Prop) (x y : Fin n) :
    y ∈ suffixSet r x ↔ y = x ∨ r x y := by
  classical
  simp [suffixSet]

theorem suffixSet_nonempty (r : Fin n → Fin n → Prop) (x : Fin n) :
    (suffixSet r x).Nonempty := by
  exact ⟨x, by simp⟩

/-- The right-to-left-minimum after-cut inverse sends `x` to the least value
in the suffix beginning at `x`.  Equivalently, it cuts immediately *after*
each right-to-left minimum. -/
noncomputable def afterCutRep (r : Fin n → Fin n → Prop) (x : Fin n) : Fin n :=
  (suffixSet r x).min' (suffixSet_nonempty r x)

/-- On a standard block word the after-cut representative is the block
minimum.  This is the corrected inverse to Φ. -/
theorem afterCutRep_standardBefore (A : CanonicalPartition n) (x : Fin n) :
    afterCutRep A.standardBefore x = A.rep x := by
  unfold afterCutRep
  rw [Finset.min'_eq_iff]
  constructor
  · rw [mem_suffixSet]
    by_cases hx : A.rep x = x
    · exact Or.inl hx
    · right
      right
      exact ⟨(A.rep_idem x).symm, Or.inl ⟨hx, A.rep_idem x⟩⟩
  · intro y hy
    rw [mem_suffixSet] at hy
    rcases hy with rfl | hxy
    · exact A.rep_le y
    · exact (A.rep_le_of_standardBefore hxy).trans (A.rep_le y)

/-- Literal right-to-left minimality in an occurrence order. -/
def RightToLeftMinimum (r : Fin n → Fin n → Prop) (x : Fin n) : Prop :=
  ∀ y, r x y → x < y

theorem rightToLeftMinimum_standardBefore_iff (A : CanonicalPartition n) (x : Fin n) :
    RightToLeftMinimum A.standardBefore x ↔ A.rep x = x := by
  constructor
  · intro h
    by_contra hx
    have hbefore : A.standardBefore x (A.rep x) := by
      right
      exact ⟨(A.rep_idem x).symm, Or.inl ⟨hx, A.rep_idem x⟩⟩
    have hlt := h (A.rep x) hbefore
    exact (not_lt_of_ge (A.rep_le x)) hlt
  · intro hx y hxy
    rcases hxy with hcross | ⟨_, hinside⟩
    · calc
        x = A.rep x := hx.symm
        _ < A.rep y := hcross
        _ ≤ y := A.rep_le y
    · rcases hinside with ⟨h, _⟩ | ⟨h, _⟩
      · exact False.elim (h hx)
      · exact False.elim (h hx)

/-- A canonical ordered-block representation of an avoiding permutation word.
`cut` is its after-cut partition and `standard` says precisely how the blocks
are read; avoidance itself remains the independent literal predicate above. -/
structure AvoidingWord (n : ℕ) where
  before : Fin n → Fin n → Prop
  cut : CanonicalPartition n
  standard : before = cut.standardBefore

namespace AvoidingWord

@[ext]
theorem ext {u v : AvoidingWord n} (hcut : u.cut = v.cut) : u = v := by
  cases u with
  | mk ub uc us =>
    cases v with
    | mk vb vc vs =>
      dsimp at hcut
      subst vc
      cases us
      cases vs
      rfl

theorem avoids32_1 (w : AvoidingWord n) : Avoids32_1Order w.before := by
  rw [w.standard]
  exact w.cut.standardBefore_avoids32_1

/-- The stored cut really is recovered by cutting after right-to-left minima. -/
theorem afterCut_inverse (w : AvoidingWord n) (x : Fin n) :
    afterCutRep w.before x = w.cut.rep x := by
  rw [w.standard]
  exact afterCutRep_standardBefore w.cut x

end AvoidingWord

/-- Equivalence with the bundled standard-word certificate.  The genuine
literal-avoider equivalence is `theorem_4_2` below. -/
def standardWordEquiv (n : ℕ) : CanonicalPartition n ≃ AvoidingWord n where
  toFun A := ⟨A.standardBefore, A, rfl⟩
  invFun w := w.cut
  left_inv _ := rfl
  right_inv w := AvoidingWord.ext rfl

/-! ### Literal avoiding strict-total word orders -/

/-- A permutation word represented by its strict total occurrence order. -/
structure OrderedWord (n : ℕ) where
  before : Fin n → Fin n → Prop
  strictTotal : IsStrictTotalOrder (Fin n) before

namespace OrderedWord

@[ext]
theorem ext {u v : OrderedWord n} (h : u.before = v.before) : u = v := by
  cases u
  cases v
  simp_all

theorem standardBefore_isIrrefl (A : CanonicalPartition n) :
    Irreflexive A.standardBefore := by
  intro x hx
  rcases hx with hx | ⟨_, hx⟩
  · exact (lt_irrefl _ hx)
  · rcases hx with ⟨hne, heq⟩ | ⟨hne, _, hlt⟩
    · exact hne heq
    · exact (lt_irrefl _ hlt)

theorem standardBefore_transitive (A : CanonicalPartition n) :
    Transitive A.standardBefore := by
  intro x y z hxy hyz
  rcases hxy with hxy | ⟨hxy, hi⟩
  · have hyzle := A.rep_le_of_standardBefore hyz
    exact Or.inl (hxy.trans_le hyzle)
  · rcases hyz with hyz | ⟨hyz, hj⟩
    · exact Or.inl (hxy ▸ hyz)
    · right
      refine ⟨hxy.trans hyz, ?_⟩
      rcases hi with hi | hi
      · have hyrep : A.rep y = y := hi.2
        rcases hj with hj | hj <;> exact False.elim (hj.1 hyrep)
      · rcases hj with hj | hj
        · exact Or.inl ⟨hi.1, hj.2⟩
        · exact Or.inr ⟨hi.1, hj.2.1, hi.2.2.trans hj.2.2⟩

theorem standardBefore_trichotomous (A : CanonicalPartition n) :
    Std.Trichotomous A.standardBefore := by
  constructor
  intro x y hnxy hnyx
  rcases lt_trichotomy (A.rep x) (A.rep y) with h | h | h
  · exact False.elim (hnxy (Or.inl h))
  · by_cases hxy : x = y
    · exact hxy
    · by_cases hx : A.rep x = x
      · have hy : A.rep y ≠ y := by
          intro hy
          apply hxy
          exact hx.symm.trans (h.trans hy)
        exact False.elim (hnyx (Or.inr ⟨h.symm, Or.inl ⟨hy, hx⟩⟩))
      · by_cases hy : A.rep y = y
        · exact False.elim (hnxy (Or.inr ⟨h, Or.inl ⟨hx, hy⟩⟩))
        · rcases lt_trichotomy x y with hlt | heq | hgt
          · exact False.elim (hnxy (Or.inr ⟨h, Or.inr ⟨hx, hy, hlt⟩⟩))
          · exact False.elim (hxy heq)
          · exact False.elim (hnyx (Or.inr ⟨h.symm, Or.inr ⟨hy, hx, hgt⟩⟩))
  · exact False.elim (hnyx (Or.inl h))

theorem standardBefore_strictTotal (A : CanonicalPartition n) :
    IsStrictTotalOrder (Fin n) A.standardBefore where
  trichotomous := (standardBefore_trichotomous A).trichotomous
  irrefl := standardBefore_isIrrefl A
  trans := standardBefore_transitive A

/-- Φ as a genuine finite strict-total word order. -/
def ofPartition (A : CanonicalPartition n) : OrderedWord n :=
  ⟨A.standardBefore, standardBefore_strictTotal A⟩

/-- The after-cut inverse is defined for every strict-total word order, before
any avoidance hypothesis is imposed. -/
noncomputable def afterCut (w : OrderedWord n) : CanonicalPartition n where
  rep := afterCutRep w.before
  rep_le := by
    intro x
    unfold afterCutRep
    exact Finset.min'_le _ _ (by simp)
  rep_idem := by
    intro x
    letI : IsStrictTotalOrder (Fin n) w.before := w.strictTotal
    change (suffixSet w.before (afterCutRep w.before x)).min' _ = afterCutRep w.before x
    rw [Finset.min'_eq_iff]
    constructor
    · simp
    · intro y hy
      apply Finset.min'_le
      rw [mem_suffixSet] at hy ⊢
      have hm := Finset.min'_mem (suffixSet w.before x) (suffixSet_nonempty w.before x)
      rw [mem_suffixSet] at hm
      rcases hy with rfl | hmy
      · exact hm
      · rcases hm with hm | hxm
        · right
          change afterCutRep w.before x = x at hm
          exact hm ▸ hmy
        · exact Or.inr (_root_.trans hxm hmy)

theorem afterCut_ofPartition (A : CanonicalPartition n) :
    (ofPartition A).afterCut = A := by
  apply CanonicalPartition.ext
  funext x
  exact afterCutRep_standardBefore A x

/-- Literal `32-1` avoiders; this is not defined using the range of Φ. -/
abbrev LiteralAvoider (n : ℕ) :=
  {w : OrderedWord n // Avoids32_1Order w.before}

/-- Values strictly before `x`. -/
noncomputable def predecessors (w : OrderedWord n) (x : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun y ↦ w.before y x

@[simp]
theorem mem_predecessors (w : OrderedWord n) (x y : Fin n) :
    y ∈ w.predecessors x ↔ w.before y x := by
  classical
  simp [predecessors]

/-- The zero-based position of a value is the number of its predecessors. -/
noncomputable def position (w : OrderedWord n) (x : Fin n) : Fin n := by
  classical
  refine ⟨(w.predecessors x).card, ?_⟩
  have hss : w.predecessors x ⊂ (Finset.univ : Finset (Fin n)) := by
    rw [Finset.ssubset_iff_subset_ne]
    constructor
    · exact Finset.subset_univ _
    · intro h
      letI : IsStrictTotalOrder (Fin n) w.before := w.strictTotal
      have hx : x ∈ w.predecessors x := h.symm ▸ Finset.mem_univ x
      exact (irrefl_of w.before x) (by simpa using hx)
  simpa using Finset.card_lt_card hss

theorem position_lt_of_before (w : OrderedWord n) {x y : Fin n}
    (hxy : w.before x y) : w.position x < w.position y := by
  classical
  letI : IsStrictTotalOrder (Fin n) w.before := w.strictTotal
  change (w.predecessors x).card < (w.predecessors y).card
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · intro z hz
    rw [mem_predecessors] at hz ⊢
    exact _root_.trans hz hxy
  · intro heq
    have hx : x ∈ w.predecessors y := by simpa using hxy
    have hxx : x ∉ w.predecessors x := by
      simpa using (irrefl_of w.before x)
    exact hxx (heq ▸ hx)

theorem before_iff_position_lt (w : OrderedWord n) (x y : Fin n) :
    w.before x y ↔ w.position x < w.position y := by
  letI : IsStrictTotalOrder (Fin n) w.before := w.strictTotal
  constructor
  · exact w.position_lt_of_before
  · intro hpos
    rcases trichotomous_of w.before x y with hxy | hxy | hyx
    · exact hxy
    · subst y
      exact False.elim ((lt_irrefl _) hpos)
    · have := w.position_lt_of_before hyx
      exact False.elim ((not_lt_of_ge this.le) hpos)

theorem position_injective (w : OrderedWord n) : Function.Injective w.position := by
  letI : IsStrictTotalOrder (Fin n) w.before := w.strictTotal
  intro x y hpos
  rcases trichotomous_of w.before x y with hxy | hxy | hyx
  · have := w.position_lt_of_before hxy
    exact False.elim (this.ne hpos)
  · exact hxy
  · have := w.position_lt_of_before hyx
    exact False.elim (this.ne hpos.symm)

theorem position_bijective (w : OrderedWord n) : Function.Bijective w.position :=
  (Fintype.bijective_iff_injective_and_card w.position).2 ⟨w.position_injective, rfl⟩

/-- Enumerate the values of a word order from left to right. -/
noncomputable def enumeration (w : OrderedWord n) : Equiv.Perm (Fin n) :=
  (Equiv.ofBijective w.position w.position_bijective).symm

theorem position_enumeration (w : OrderedWord n) (i : Fin n) :
    w.position (w.enumeration i) = i := by
  exact (Equiv.ofBijective w.position w.position_bijective).apply_symm_apply i

theorem enumeration_position (w : OrderedWord n) (x : Fin n) :
    w.enumeration (w.position x) = x := by
  exact (Equiv.ofBijective w.position w.position_bijective).symm_apply_apply x

theorem afterCutRep_mem_suffix (w : OrderedWord n) (x : Fin n) :
    afterCutRep w.before x ∈ suffixSet w.before x := by
  exact Finset.min'_mem _ _

theorem afterCutRep_le_of_before (w : OrderedWord n) {x y : Fin n}
    (hxy : w.before x y) : afterCutRep w.before x ≤ afterCutRep w.before y := by
  letI : IsStrictTotalOrder (Fin n) w.before := w.strictTotal
  change (suffixSet w.before x).min' _ ≤ afterCutRep w.before y
  apply Finset.min'_le
  have hm := w.afterCutRep_mem_suffix y
  rw [mem_suffixSet] at hm ⊢
  rcases hm with hm | hym
  · right
    rw [hm]
    exact hxy
  · exact Or.inr (_root_.trans hxy hym)

theorem rightToLeftMinimum_iff_afterCutRep_eq (w : OrderedWord n) (x : Fin n) :
    RightToLeftMinimum w.before x ↔ afterCutRep w.before x = x := by
  letI : IsStrictTotalOrder (Fin n) w.before := w.strictTotal
  constructor
  · intro hrtl
    unfold afterCutRep
    rw [Finset.min'_eq_iff]
    constructor
    · simp
    · intro y hy
      rw [mem_suffixSet] at hy
      rcases hy with rfl | hxy
      · exact le_rfl
      · exact (hrtl y hxy).le
  · intro hrep y hxy
    have hle : afterCutRep w.before x ≤ y := by
      unfold afterCutRep
      apply Finset.min'_le
      simp [hxy]
    have hne : x ≠ y := by
      intro h
      subst y
      exact (irrefl_of w.before x) hxy
    rw [hrep] at hle
    exact lt_of_le_of_ne hle hne

theorem adjacent_iff_position_succ (w : OrderedWord n) (x y : Fin n) :
    AdjacentInOrder w.before x y ↔
      (w.position y).1 = (w.position x).1 + 1 := by
  constructor
  · intro h
    have hlt : w.position x < w.position y := (w.before_iff_position_lt x y).1 h.1
    by_contra hne
    have hgap : (w.position x).1 + 1 < (w.position y).1 := by omega
    let k : Fin n := ⟨(w.position x).1 + 1, by omega⟩
    let z : Fin n := w.enumeration k
    have hxz : w.before x z := by
      rw [w.before_iff_position_lt]
      rw [position_enumeration]
      change (w.position x).1 < k.1
      simp [k]
    have hzy : w.before z y := by
      rw [w.before_iff_position_lt]
      rw [position_enumeration]
      change k.1 < (w.position y).1
      exact hgap
    exact h.2 z hxz hzy
  · intro hsucc
    constructor
    · rw [w.before_iff_position_lt]
      change (w.position x).1 < (w.position y).1
      omega
    · intro z hxz hzy
      have hxz' := (w.before_iff_position_lt x z).1 hxz
      have hzy' := (w.before_iff_position_lt z y).1 hzy
      change (w.position x).1 < (w.position z).1 at hxz'
      change (w.position z).1 < (w.position y).1 at hzy'
      omega

theorem adjacent_rise_of_same_afterCut (a : LiteralAvoider n) {x y : Fin n}
    (hadj : AdjacentInOrder a.1.before x y)
    (hsame : afterCutRep a.1.before x = afterCutRep a.1.before y)
    (hynon : afterCutRep a.1.before y ≠ y) : x < y := by
  letI : IsStrictTotalOrder (Fin n) a.1.before := a.1.strictTotal
  by_contra hn
  have hxy_ne : x ≠ y := by
    intro h
    subst y
    exact (irrefl_of a.1.before x) hadj.1
  have hyx : y < x := lt_of_le_of_ne (le_of_not_gt hn) hxy_ne.symm
  have hrtl : RightToLeftMinimum a.1.before y := by
    intro z hyz
    by_contra hyznot
    have hyz_ne : y ≠ z := by
      intro h
      subst z
      exact (irrefl_of a.1.before y) hyz
    have hzy : z < y := lt_of_le_of_ne (le_of_not_gt hyznot) hyz_ne.symm
    exact a.2 ⟨x, y, z, hadj, hyz, hyx, hzy⟩
  exact hynon ((a.1.rightToLeftMinimum_iff_afterCutRep_eq y).1 hrtl)

private theorem increasing_same_cut_positions (a : LiteralAvoider n) (d : ℕ)
    (i j : Fin n) (hpos : j.1 = i.1 + d + 1)
    (hsame : afterCutRep a.1.before (a.1.enumeration i) =
      afterCutRep a.1.before (a.1.enumeration j))
    (hjnon : afterCutRep a.1.before (a.1.enumeration j) ≠ a.1.enumeration j) :
    a.1.enumeration i < a.1.enumeration j := by
  letI : IsStrictTotalOrder (Fin n) a.1.before := a.1.strictTotal
  induction d generalizing i j with
  | zero =>
      apply adjacent_rise_of_same_afterCut a
      · rw [a.1.adjacent_iff_position_succ]
        rw [position_enumeration, position_enumeration]
        simpa using hpos
      · exact hsame
      · exact hjnon
  | succ d ih =>
      let k : Fin n := ⟨i.1 + 1, by omega⟩
      have hik : a.1.before (a.1.enumeration i) (a.1.enumeration k) := by
        rw [a.1.before_iff_position_lt]
        rw [position_enumeration, position_enumeration]
        change i.1 < i.1 + 1
        omega
      have hkj : a.1.before (a.1.enumeration k) (a.1.enumeration j) := by
        rw [a.1.before_iff_position_lt]
        simp only [position_enumeration]
        change k.1 < j.1
        simp [k]
        omega
      have hrik := a.1.afterCutRep_le_of_before hik
      have hrkj := a.1.afterCutRep_le_of_before hkj
      have hrk : afterCutRep a.1.before (a.1.enumeration k) =
          afterCutRep a.1.before (a.1.enumeration j) := by
        apply le_antisymm hrkj
        rw [← hsame]
        exact hrik
      have hknon : afterCutRep a.1.before (a.1.enumeration k) ≠ a.1.enumeration k := by
        intro hk
        have hm := a.1.afterCutRep_mem_suffix (a.1.enumeration j)
        rw [mem_suffixSet] at hm
        rcases hm with hm | hm
        · exact hjnon hm
        · have hjk : afterCutRep a.1.before (a.1.enumeration j) =
              a.1.enumeration k := hrk.symm.trans hk
          rw [hjk] at hm
          exact (asymm_of a.1.before hkj hm)
      have hil : a.1.enumeration i < a.1.enumeration k := by
        apply adjacent_rise_of_same_afterCut a
        · rw [a.1.adjacent_iff_position_succ]
          rw [position_enumeration, position_enumeration]
        · exact hsame.trans hrk.symm
        · exact hknon
      have hkr : a.1.enumeration k < a.1.enumeration j := by
        apply ih k j
        · change j.1 = k.1 + d + 1
          simp [k]
          omega
        · exact hrk
        · exact hjnon
      exact hil.trans hkr

theorem increasing_of_before_of_same_afterCut (a : LiteralAvoider n) {x y : Fin n}
    (hxy : a.1.before x y)
    (hsame : afterCutRep a.1.before x = afterCutRep a.1.before y)
    (hynon : afterCutRep a.1.before y ≠ y) : x < y := by
  have hpos := (a.1.before_iff_position_lt x y).1 hxy
  let d := (a.1.position y).1 - (a.1.position x).1 - 1
  have hd : (a.1.position y).1 = (a.1.position x).1 + d + 1 := by
    dsimp [d]
    omega
  have hsame' : afterCutRep a.1.before (a.1.enumeration (a.1.position x)) =
      afterCutRep a.1.before (a.1.enumeration (a.1.position y)) := by
    rw [enumeration_position, enumeration_position]
    exact hsame
  have hynon' : afterCutRep a.1.before (a.1.enumeration (a.1.position y)) ≠
      a.1.enumeration (a.1.position y) := by
    rw [enumeration_position]
    exact hynon
  have h := increasing_same_cut_positions a d (a.1.position x) (a.1.position y)
    hd hsame' hynon'
  rw [enumeration_position, enumeration_position] at h
  exact h

/-- The essential reconstruction statement for Theorem 4.2.  For an arbitrary
literal `32-1`-avoiding strict-total word order, cutting immediately after its
right-to-left minima and then reading the resulting blocks in standard order
recovers the original occurrence order. -/
theorem standardBefore_afterCut_iff (a : LiteralAvoider n) (x y : Fin n) :
    a.1.afterCut.standardBefore x y ↔ a.1.before x y := by
  letI : IsStrictTotalOrder (Fin n) a.1.before := a.1.strictTotal
  constructor
  · intro h
    rcases h with hcross | ⟨hsame, hinside⟩
    · rcases trichotomous_of a.1.before x y with hxy | hxy | hyx
      · exact hxy
      · subst y
        exact False.elim ((lt_irrefl _) hcross)
      · have hmono := a.1.afterCutRep_le_of_before hyx
        exact False.elim ((not_lt_of_ge hmono) hcross)
    · rcases hinside with ⟨hxnon, hyrep⟩ | ⟨hxnon, hynon, hxyval⟩
      · have hm := a.1.afterCutRep_mem_suffix x
        rw [mem_suffixSet] at hm
        rcases hm with hm | hm
        · exact False.elim (hxnon hm)
        · change afterCutRep a.1.before x = afterCutRep a.1.before y at hsame
          change afterCutRep a.1.before y = y at hyrep
          rw [hsame, hyrep] at hm
          exact hm
      · rcases trichotomous_of a.1.before x y with hxy | hxy | hyx
        · exact hxy
        · subst y
          exact False.elim ((lt_irrefl _) hxyval)
        · have hyxval := increasing_of_before_of_same_afterCut a hyx hsame.symm hxnon
          exact False.elim (asymm hxyval hyxval)
  · intro hxy
    have hmono := a.1.afterCutRep_le_of_before hxy
    rcases lt_or_eq_of_le hmono with hcross | hsame
    · exact Or.inl hcross
    · right
      have hxnon : afterCutRep a.1.before x ≠ x := by
        intro hx
        have hm := a.1.afterCutRep_mem_suffix y
        rw [mem_suffixSet] at hm
        have hpyx : afterCutRep a.1.before y = x := hsame.symm.trans hx
        rw [hpyx] at hm
        rcases hm with hm | hm
        · subst y
          exact (irrefl_of a.1.before x) hxy
        · exact (asymm_of a.1.before hxy hm)
      refine ⟨hsame, ?_⟩
      by_cases hyrep : afterCutRep a.1.before y = y
      · exact Or.inl ⟨hxnon, hyrep⟩
      · exact Or.inr ⟨hxnon, hyrep,
          increasing_of_before_of_same_afterCut a hxy hsame hyrep⟩

theorem reconstruct_afterCut (a : LiteralAvoider n) :
    ofPartition a.1.afterCut = a.1 := by
  apply OrderedWord.ext
  funext x y
  apply propext
  exact standardBefore_afterCut_iff a x y

/-! ### Passage between order words and actual permutations -/

/-- Regard an actual permutation word as the occurrence order on its values. -/
def ofPermutation (σ : Equiv.Perm (Fin n)) : OrderedWord n where
  before x y := σ.symm x < σ.symm y
  strictTotal := by
    refine { trichotomous := ?_, irrefl := ?_, trans := ?_ }
    · intro x y hnxy hnyx
      apply σ.symm.injective
      exact le_antisymm (le_of_not_gt hnyx) (le_of_not_gt hnxy)
    · exact fun x h ↦ (lt_irrefl _ h)
    · exact fun _ _ _ hxy hyz ↦ hxy.trans hyz

theorem card_predecessors_ofPermutation (σ : Equiv.Perm (Fin n)) (x : Fin n) :
    ((ofPermutation σ).predecessors x).card =
      (Finset.Iio (σ.symm x)).card := by
  classical
  refine Finset.card_bij (fun y _ ↦ σ.symm y) ?_ ?_ ?_
  · intro y hy
    rw [Finset.mem_Iio]
    simpa [ofPermutation] using
      ((ofPermutation σ).mem_predecessors x y).1 hy
  · intro y₁ _ y₂ _ h
    exact σ.symm.injective h
  · intro i hi
    refine ⟨σ i, ?_, by simp⟩
    rw [(ofPermutation σ).mem_predecessors]
    simpa [ofPermutation] using (Finset.mem_Iio.1 hi)

theorem position_ofPermutation (σ : Equiv.Perm (Fin n)) (x : Fin n) :
    (ofPermutation σ).position x = σ.symm x := by
  apply Fin.ext
  change ((ofPermutation σ).predecessors x).card = (σ.symm x).1
  rw [card_predecessors_ofPermutation]
  exact Fin.card_Iio (σ.symm x)

theorem enumeration_ofPermutation (σ : Equiv.Perm (Fin n)) :
    (ofPermutation σ).enumeration = σ := by
  apply Equiv.ext
  intro i
  apply σ.symm.injective
  calc
    σ.symm ((ofPermutation σ).enumeration i) =
        (ofPermutation σ).position ((ofPermutation σ).enumeration i) :=
      (position_ofPermutation σ _).symm
    _ = i := (ofPermutation σ).position_enumeration i
    _ = σ.symm (σ i) := by simp

@[simp]
theorem enumeration_symm_apply (w : OrderedWord n) (x : Fin n) :
    w.enumeration.symm x = w.position x := by
  rfl

theorem ofPermutation_enumeration (w : OrderedWord n) :
    ofPermutation w.enumeration = w := by
  apply OrderedWord.ext
  funext x y
  apply propext
  change w.enumeration.symm x < w.enumeration.symm y ↔ w.before x y
  rw [enumeration_symm_apply, enumeration_symm_apply]
  exact (w.before_iff_position_lt x y).symm

/-- Strict-total occurrence orders and actual permutation words are equivalent. -/
noncomputable def permutationEquiv (n : ℕ) :
    OrderedWord n ≃ Equiv.Perm (Fin n) where
  toFun := enumeration
  invFun := ofPermutation
  left_inv := ofPermutation_enumeration
  right_inv := enumeration_ofPermutation

theorem adjacent_enumeration_iff (w : OrderedWord n) (i j : Fin n) :
    AdjacentInOrder w.before (w.enumeration i) (w.enumeration j) ↔
      LeanCo.Permutation.Adjacent i j := by
  rw [w.adjacent_iff_position_succ]
  rw [position_enumeration, position_enumeration]
  rfl

theorem adjacent_ofPermutation_iff (σ : Equiv.Perm (Fin n)) (x y : Fin n) :
    AdjacentInOrder (ofPermutation σ).before x y ↔
      LeanCo.Permutation.Adjacent (σ.symm x) (σ.symm y) := by
  rw [(ofPermutation σ).adjacent_iff_position_succ]
  rw [position_ofPermutation, position_ofPermutation]
  rfl

/-- The order-relation and actual-permutation formulations of `32-1`
occurrence are literally equivalent under `permutationEquiv`. -/
theorem occurs32_1_ofPermutation_iff (σ : Equiv.Perm (Fin n)) :
    Occurs32_1Order (ofPermutation σ).before ↔
      LeanCo.Permutation.Occurs32_1 σ := by
  constructor
  · rintro ⟨x, y, z, hxy, hyz, hyx, hzy⟩
    refine ⟨σ.symm x, σ.symm y, σ.symm z, ?_, ?_, ?_, ?_⟩
    · exact (adjacent_ofPermutation_iff σ x y).1 hxy
    · exact hyz
    · simpa using hyx
    · simpa using hzy
  · rintro ⟨i, j, k, hij, hjk, hji, hkj⟩
    refine ⟨σ i, σ j, σ k, ?_, ?_, hji, hkj⟩
    · apply (adjacent_ofPermutation_iff σ (σ i) (σ j)).2
      simpa using hij
    · simpa [ofPermutation] using hjk

theorem avoids32_1_ofPermutation_iff (σ : Equiv.Perm (Fin n)) :
    Avoids32_1Order (ofPermutation σ).before ↔
      LeanCo.Permutation.Avoids32_1 σ := by
  exact not_congr (occurs32_1_ofPermutation_iff σ)

/-- The literal avoiding order model is equivalent to the existing project
subtype of actual `32-1`-avoiding permutations. -/
noncomputable def literalAvoiderPermutationEquiv (n : ℕ) :
    LiteralAvoider n ≃
      {σ : Equiv.Perm (Fin n) // LeanCo.Permutation.Avoids32_1 σ} where
  toFun a := ⟨a.1.enumeration, by
    apply (avoids32_1_ofPermutation_iff a.1.enumeration).1
    rw [ofPermutation_enumeration]
    exact a.2⟩
  invFun σ := ⟨ofPermutation σ.1,
    (avoids32_1_ofPermutation_iff σ.1).2 σ.2⟩
  left_inv a := by
    apply Subtype.ext
    exact ofPermutation_enumeration a.1
  right_inv σ := by
    apply Subtype.ext
    exact enumeration_ofPermutation σ.1

end OrderedWord

/-- **Theorem 4.2.**  Standard block words are in bijection with all literal
`32-1`-avoiding strict-total word orders. -/
noncomputable def theorem_4_2_order (n : ℕ) :
    CanonicalPartition n ≃ OrderedWord.LiteralAvoider n where
  toFun A := ⟨OrderedWord.ofPartition A, standardBefore_avoids32_1 A⟩
  invFun a := a.1.afterCut
  left_inv := OrderedWord.afterCut_ofPartition
  right_inv a := by
    apply Subtype.ext
    exact OrderedWord.reconstruct_afterCut a

/-- **Theorem 4.2 (actual permutation form).**  The codomain is the existing
literal `LeanCo.Permutation.Avoids32_1` subtype, not a range or certificate
type. -/
noncomputable def theorem_4_2 (n : ℕ) :
    CanonicalPartition n ≃
      {σ : Equiv.Perm (Fin n) // LeanCo.Permutation.Avoids32_1 σ} :=
  (theorem_4_2_order n).trans (OrderedWord.literalAvoiderPermutationEquiv n)

noncomputable instance instFintypeAvoidingPermutations :
    Fintype {σ : Equiv.Perm (Fin n) // LeanCo.Permutation.Avoids32_1 σ} :=
  Fintype.ofEquiv (CanonicalPartition n) (theorem_4_2 n)

/-- The actual standard permutation produced by Φ. -/
noncomputable def standardPermutation (A : CanonicalPartition n) :
    Equiv.Perm (Fin n) :=
  (OrderedWord.ofPartition A).enumeration

@[simp]
theorem theorem_4_2_apply (A : CanonicalPartition n) :
    ((theorem_4_2 n) A).1 = A.standardPermutation := rfl

/-! ## Inversions: Lemma 4.3 -/

/-- Ordinary inversions of the representative word.  Replacing representatives by
their consecutive ranks does not change this statistic. -/
def wordInversionPairs (A : CanonicalPartition n) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun xy ↦ xy.1 < xy.2 ∧ A.rep xy.2 < A.rep xy.1

def wordInversions (A : CanonicalPartition n) : ℕ :=
  A.wordInversionPairs.card

/-- Inversions in the actual standard block order. -/
noncomputable def standardInversionPairs (A : CanonicalPartition n) : Finset (Fin n × Fin n) := by
  classical
  exact Finset.univ.filter fun xy ↦ xy.1 < xy.2 ∧ A.standardBefore xy.2 xy.1

noncomputable def standardInversions (A : CanonicalPartition n) : ℕ :=
  A.standardInversionPairs.card

/-- Inversion number is invariant under taking the inverse permutation.  The
bijection sends an inversion `(i,j)` to the value pair `(σ j,σ i)`. -/
theorem permutation_inversionNumber_symm (σ : Equiv.Perm (Fin n)) :
    LeanCo.Permutation.inversionNumber σ =
      LeanCo.Permutation.inversionNumber σ.symm := by
  classical
  unfold LeanCo.Permutation.inversionNumber
  refine Finset.card_bij (fun ij _ ↦ (σ ij.2, σ ij.1)) ?_ ?_ ?_
  · intro ij hij
    rcases ij with ⟨i, j⟩
    rw [LeanCo.Permutation.mem_inversionPairs] at hij ⊢
    simp only [Equiv.symm_apply_apply]
    exact ⟨hij.2, hij.1⟩
  · intro ij₁ _ ij₂ _ h
    rcases ij₁ with ⟨i₁, j₁⟩
    rcases ij₂ with ⟨i₂, j₂⟩
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (σ.injective h.2) (σ.injective h.1)
  · intro xy hxy
    rcases xy with ⟨x, y⟩
    rw [LeanCo.Permutation.mem_inversionPairs] at hxy
    refine ⟨(σ.symm y, σ.symm x), ?_, ?_⟩
    · rw [LeanCo.Permutation.mem_inversionPairs]
      simp only [Equiv.apply_symm_apply]
      exact ⟨hxy.2, hxy.1⟩
    · simp

theorem standardInversionPairs_eq_permutation_inverse (A : CanonicalPartition n) :
    A.standardInversionPairs =
      LeanCo.Permutation.inversionPairs A.standardPermutation.symm := by
  classical
  ext xy
  rcases xy with ⟨x, y⟩
  simp only [standardInversionPairs, Finset.mem_filter, Finset.mem_univ, true_and,
    LeanCo.Permutation.mem_inversionPairs]
  change (x < y ∧ A.standardBefore y x) ↔
    x < y ∧
      (OrderedWord.ofPartition A).enumeration.symm y <
        (OrderedWord.ofPartition A).enumeration.symm x
  rw [OrderedWord.enumeration_symm_apply, OrderedWord.enumeration_symm_apply]
  exact and_congr Iff.rfl
    ((OrderedWord.ofPartition A).before_iff_position_lt y x)

/-- The inversion statistic of the actual standard permutation is the order
statistic used in Lemma 4.3. -/
theorem standardPermutation_inversionNumber (A : CanonicalPartition n) :
    LeanCo.Permutation.inversionNumber A.standardPermutation =
      A.standardInversions := by
  calc
    LeanCo.Permutation.inversionNumber A.standardPermutation =
        LeanCo.Permutation.inversionNumber A.standardPermutation.symm :=
      permutation_inversionNumber_symm A.standardPermutation
    _ = A.standardInversions := by
      rw [LeanCo.Permutation.inversionNumber, standardInversions,
        ← standardInversionPairs_eq_permutation_inverse]

/-- Elements other than the least element of their block. -/
def nonrepresentatives (A : CanonicalPartition n) : Finset (Fin n) :=
  Finset.univ.filter fun x ↦ A.rep x ≠ x

/-- The within-block inversion contributed by a non-representative `y` is
`(rep y,y)`. -/
def internalInversionPairs (A : CanonicalPartition n) : Finset (Fin n × Fin n) :=
  A.nonrepresentatives.image fun y ↦ (A.rep y, y)

theorem standardBefore_reverse_iff (A : CanonicalPartition n) {x y : Fin n} (hxy : x < y) :
    A.standardBefore y x ↔
      A.rep y < A.rep x ∨ (A.rep x = x ∧ A.rep y = A.rep x) := by
  constructor
  · rintro (hcross | ⟨hsame, hinside⟩)
    · exact Or.inl hcross
    · right
      rcases hinside with ⟨_, hx⟩ | ⟨_, _, hyx⟩
      · exact ⟨hx, hsame⟩
      · exact False.elim ((not_lt_of_ge hxy.le) hyx)
  · rintro (hlt | ⟨hx, heq⟩)
    · exact Or.inl hlt
    · right
      have hy : A.rep y ≠ y := by
        intro hy
        have : y = x := hy.symm.trans (heq.trans hx)
        exact hxy.ne this.symm
      exact ⟨heq, Or.inl ⟨hy, hx⟩⟩

theorem standardInversionPairs_eq_union (A : CanonicalPartition n) :
    A.standardInversionPairs = A.wordInversionPairs ∪ A.internalInversionPairs := by
  classical
  ext xy
  rcases xy with ⟨x, y⟩
  simp only [standardInversionPairs, wordInversionPairs, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · rintro ⟨hxy, hinv⟩
    rcases (A.standardBefore_reverse_iff hxy).mp hinv with hcross | ⟨hx, heq⟩
    · exact Or.inl ⟨hxy, hcross⟩
    · right
      simp only [internalInversionPairs, Finset.mem_image]
      refine ⟨y, ?_, ?_⟩
      · simp [nonrepresentatives]
        intro hy
        apply hxy.ne
        calc
          x = A.rep x := hx.symm
          _ = A.rep y := heq.symm
          _ = y := hy
      · simp [hx, heq]
  · rintro (hcross | hinternal)
    · exact ⟨hcross.1, (A.standardBefore_reverse_iff hcross.1).2 (Or.inl hcross.2)⟩
    · simp only [internalInversionPairs, Finset.mem_image] at hinternal
      obtain ⟨z, hz, hp⟩ := hinternal
      simp only [Prod.mk.injEq] at hp
      rcases hp with ⟨rfl, rfl⟩
      have hz' : A.rep z ≠ z := by simpa [nonrepresentatives] using hz
      have hlt : A.rep z < z := lt_of_le_of_ne (A.rep_le z) hz'
      refine ⟨hlt, (A.standardBefore_reverse_iff hlt).2
        (Or.inr ⟨A.rep_idem z, (A.rep_idem z).symm⟩)⟩

theorem disjoint_word_internal (A : CanonicalPartition n) :
    Disjoint A.wordInversionPairs A.internalInversionPairs := by
  classical
  rw [Finset.disjoint_left]
  intro xy hword hint
  rcases xy with ⟨x, y⟩
  have hw : A.rep y < A.rep x := (by simpa [wordInversionPairs] using hword :
    x < y ∧ A.rep y < A.rep x).2
  simp only [internalInversionPairs, Finset.mem_image] at hint
  obtain ⟨z, _, hp⟩ := hint
  simp only [Prod.mk.injEq] at hp
  rcases hp with ⟨rfl, rfl⟩
  simpa [A.rep_idem] using hw

theorem card_internalInversionPairs (A : CanonicalPartition n) :
    A.internalInversionPairs.card = A.nonrepresentatives.card := by
  classical
  exact Finset.card_image_of_injective _ (fun _ _ h ↦ congr_arg Prod.snd h)

theorem card_nonrepresentatives (A : CanonicalPartition n) :
    A.nonrepresentatives.card = n - A.blockCount := by
  have h0 := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (p := fun x ↦ A.rep x = x)
  have h : A.blockCount + A.nonrepresentatives.card = n := by
    simpa [blockCount, representatives, nonrepresentatives] using h0
  omega

/-- Lemma 4.3: inversions split into word inversions and one inversion for every
non-minimal block element. -/
theorem lemma_4_3 (A : CanonicalPartition n) :
    A.standardInversions = A.wordInversions + n - A.blockCount := by
  calc
    A.standardInversions = A.wordInversions + A.nonrepresentatives.card := by
      rw [standardInversions, standardInversionPairs_eq_union,
        Finset.card_union_of_disjoint (disjoint_word_internal A), wordInversions,
        card_internalInversionPairs]
    _ = A.wordInversions + (n - A.blockCount) := by rw [card_nonrepresentatives]
    _ = A.wordInversions + n - A.blockCount := by
      have hk : A.blockCount ≤ n := by
        exact (Finset.card_filter_le (Finset.univ : Finset (Fin n)) _).trans_eq (by simp)
      omega

/-! ## Restricted-growth words and descents: Lemma 4.4 -/

/-- The minimum-representative form of a restricted-growth word.  Relabelling
the fixed points increasingly by `1,2,…` gives the usual paper convention. -/
def IsRestrictedGrowthWord (w : Fin n → Fin n) : Prop :=
  (∀ i, w i ≤ i) ∧ ∀ i, w (w i) = w i

/-- The restricted-growth word associated with a canonical partition. -/
def restrictedGrowthWord (A : CanonicalPartition n) : Fin n → Fin n :=
  A.rep

theorem restrictedGrowthWord_isRestricted (A : CanonicalPartition n) :
    IsRestrictedGrowthWord A.restrictedGrowthWord :=
  ⟨A.rep_le, A.rep_idem⟩

/-- A value occurs at least twice in a word. -/
def RepeatedValue (w : Fin n → Fin n) (a : Fin n) : Prop :=
  ∃ x y, x ≠ y ∧ w x = a ∧ w y = a

/-- The distinct repeated values of a word.  This is the corrected reading of
`rp`: repetitions are counted in the restricted-growth word, not in the
permutation (whose values are of course all distinct). -/
noncomputable def repeatedValues (w : Fin n → Fin n) : Finset (Fin n) := by
  classical
  exact (Finset.univ.image w).filter (RepeatedValue w)

noncomputable def rp (w : Fin n → Fin n) : ℕ :=
  (repeatedValues w).card

/-- Representatives of blocks having more than one element. -/
def repeatedRepresentatives (A : CanonicalPartition n) : Finset (Fin n) := by
  classical
  exact A.representatives.filter fun r ↦ ∃ x, x ≠ r ∧ A.rep x = r

theorem repeatedValues_restrictedGrowthWord (A : CanonicalPartition n) :
    repeatedValues A.restrictedGrowthWord = A.repeatedRepresentatives := by
  classical
  ext a
  constructor
  · intro ha
    rw [repeatedValues, Finset.mem_filter] at ha
    rcases ha with ⟨haimg, x, y, hxy, hxa, hya⟩
    rw [Finset.mem_image] at haimg
    obtain ⟨u, _, hu⟩ := haimg
    have harep : A.rep a = a := by
      rw [← hu]
      exact A.rep_idem u
    rw [repeatedRepresentatives, Finset.mem_filter]
    refine ⟨A.mem_representatives a |>.2 harep, ?_⟩
    by_cases hx : x = a
    · refine ⟨y, ?_, ?_⟩
      · intro hy
        exact hxy (hx.trans hy.symm)
      · exact hya
    · exact ⟨x, hx, hxa⟩
  · intro ha
    rw [repeatedRepresentatives, Finset.mem_filter] at ha
    rcases ha with ⟨harep, x, hxa, hx⟩
    rw [repeatedValues, Finset.mem_filter]
    constructor
    · rw [Finset.mem_image]
      exact ⟨a, by simp, (A.mem_representatives a).1 harep⟩
    · exact ⟨a, x, hxa.symm, (A.mem_representatives a).1 harep, hx⟩

/-- Descent bottoms in the standard block word.  Counting bottoms is the same
as counting descent positions because a permutation has distinct values. -/
noncomputable def descentBottoms (A : CanonicalPartition n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun y ↦
    ∃ x, AdjacentInOrder A.standardBefore x y ∧ y < x

noncomputable def descentNumber (A : CanonicalPartition n) : ℕ :=
  A.descentBottoms.card

theorem card_descentSet_standardPermutation (A : CanonicalPartition n) :
    (LeanCo.Permutation.descentSet A.standardPermutation).card =
      A.descentBottoms.card := by
  classical
  refine Finset.card_bij
    (fun i hi ↦ A.standardPermutation
      (Classical.choose
        ((LeanCo.Permutation.mem_descentSet (i := i)).1 hi))) ?_ ?_ ?_
  · intro i hi
    let j : Fin n := Classical.choose
      ((LeanCo.Permutation.mem_descentSet (i := i)).1 hi)
    have hj : LeanCo.Permutation.Adjacent i j ∧
        A.standardPermutation j < A.standardPermutation i :=
      Classical.choose_spec
        ((LeanCo.Permutation.mem_descentSet (i := i)).1 hi)
    change A.standardPermutation j ∈ A.descentBottoms
    rw [descentBottoms, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    refine ⟨A.standardPermutation i, ?_, hj.2⟩
    change AdjacentInOrder (OrderedWord.ofPartition A).before
      ((OrderedWord.ofPartition A).enumeration i)
      ((OrderedWord.ofPartition A).enumeration j)
    exact (OrderedWord.adjacent_enumeration_iff
      (OrderedWord.ofPartition A) i j).2 hj.1
  · intro i₁ hi₁ i₂ hi₂ heq
    let j₁ : Fin n := Classical.choose
      ((LeanCo.Permutation.mem_descentSet (i := i₁)).1 hi₁)
    let j₂ : Fin n := Classical.choose
      ((LeanCo.Permutation.mem_descentSet (i := i₂)).1 hi₂)
    have hj₁ : LeanCo.Permutation.Adjacent i₁ j₁ ∧
        A.standardPermutation j₁ < A.standardPermutation i₁ :=
      Classical.choose_spec
        ((LeanCo.Permutation.mem_descentSet (i := i₁)).1 hi₁)
    have hj₂ : LeanCo.Permutation.Adjacent i₂ j₂ ∧
        A.standardPermutation j₂ < A.standardPermutation i₂ :=
      Classical.choose_spec
        ((LeanCo.Permutation.mem_descentSet (i := i₂)).1 hi₂)
    change A.standardPermutation j₁ = A.standardPermutation j₂ at heq
    have hj : j₁ = j₂ := A.standardPermutation.injective heq
    apply Fin.ext
    have hjval := congrArg Fin.val hj
    unfold LeanCo.Permutation.Adjacent at hj₁ hj₂
    omega
  · intro y hy
    have hy' : ∃ x, AdjacentInOrder A.standardBefore x y ∧ y < x := by
      simpa [descentBottoms] using hy
    obtain ⟨x, hxy, hyx⟩ := hy'
    let i : Fin n := (OrderedWord.ofPartition A).position x
    let j : Fin n := (OrderedWord.ofPartition A).position y
    have hij : LeanCo.Permutation.Adjacent i j := by
      apply (OrderedWord.adjacent_enumeration_iff
        (OrderedWord.ofPartition A) i j).1
      dsimp [i, j]
      rw [OrderedWord.enumeration_position, OrderedWord.enumeration_position]
      exact hxy
    have hi : i ∈ LeanCo.Permutation.descentSet A.standardPermutation := by
      rw [LeanCo.Permutation.mem_descentSet]
      refine ⟨j, hij, ?_⟩
      simpa [i, j, standardPermutation,
        OrderedWord.enumeration_position] using hyx
    refine ⟨i, hi, ?_⟩
    let j' : Fin n := Classical.choose
      ((LeanCo.Permutation.mem_descentSet (i := i)).1 hi)
    have hj' : LeanCo.Permutation.Adjacent i j' ∧
        A.standardPermutation j' < A.standardPermutation i :=
      Classical.choose_spec
        ((LeanCo.Permutation.mem_descentSet (i := i)).1 hi)
    have hj'eq : j' = j := by
      apply Fin.ext
      unfold LeanCo.Permutation.Adjacent at hj' hij
      omega
    change A.standardPermutation j' = y
    rw [hj'eq]
    exact OrderedWord.enumeration_position (OrderedWord.ofPartition A) y

/-- The descent statistic of the actual standard permutation is the order
statistic used in Lemma 4.4. -/
theorem standardPermutation_descentNumber (A : CanonicalPartition n) :
    LeanCo.Permutation.descentNumber A.standardPermutation = A.descentNumber := by
  exact card_descentSet_standardPermutation A

theorem descentBottoms_eq_repeatedRepresentatives (A : CanonicalPartition n) :
    A.descentBottoms = A.repeatedRepresentatives := by
  classical
  ext y
  simp only [descentBottoms, repeatedRepresentatives, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, hxy, hyx⟩
    rcases hxy.1 with hcross | ⟨hsame, hinside⟩
    · by_cases hx : A.rep x = x
      · have : x < y := by
          calc
            x = A.rep x := hx.symm
            _ < A.rep y := hcross
            _ ≤ y := A.rep_le y
        exact False.elim ((not_lt_of_ge hyx.le) this)
      · have hxrep : A.standardBefore x (A.rep x) := by
          right
          exact ⟨(A.rep_idem x).symm, Or.inl ⟨hx, A.rep_idem x⟩⟩
        have hrepy : A.standardBefore (A.rep x) y := by
          left
          simpa [A.rep_idem x] using hcross
        exact False.elim (hxy.2 (A.rep x) hxrep hrepy)
    · rcases hinside with ⟨hx, hy⟩ | ⟨_, _, hlt⟩
      · refine ⟨A.mem_representatives y |>.2 hy, x, ?_, ?_⟩
        · exact hyx.ne'
        · exact hsame.trans hy
      · exact False.elim ((not_lt_of_ge hyx.le) hlt)
  · rintro ⟨hyrep, x, hxy, hxrep⟩
    have hy : A.rep y = y := (A.mem_representatives y).1 hyrep
    let s : Finset (Fin n) := Finset.univ.filter fun z ↦ A.rep z = y ∧ z ≠ y
    have hs : s.Nonempty := by
      refine ⟨x, ?_⟩
      simp [s, hxrep, hxy]
    let m : Fin n := s.max' hs
    have hm : A.rep m = y ∧ m ≠ y := by
      have := Finset.max'_mem s hs
      simpa [s] using this
    have hym : y < m := by
      apply lt_of_le_of_ne
      · simpa [hm.1] using A.rep_le m
      · exact hm.2.symm
    refine ⟨m, ⟨?_, ?_⟩, hym⟩
    · right
      exact ⟨hm.1.trans hy.symm, Or.inl ⟨fun h ↦ hm.2 (h.symm.trans hm.1), hy⟩⟩
    · intro z hmz hzy
      have hrmz : A.rep m ≤ A.rep z := A.rep_le_of_standardBefore hmz
      have hrzy : A.rep z ≤ A.rep y := A.rep_le_of_standardBefore hzy
      have hrz : A.rep z = y := by
        apply le_antisymm
        · simpa [hy] using hrzy
        · simpa [hm.1] using hrmz
      have hz_ne : z ≠ y := by
        rcases hzy with hcross | ⟨_, hinside⟩
        · exact False.elim ((lt_irrefl y) (by simpa [hrz, hy] using hcross))
        · rcases hinside with ⟨hz, _⟩ | ⟨hz, _⟩
          · intro h; exact hz (hrz.trans h.symm)
          · intro h; exact hz (hrz.trans h.symm)
      have hm_lt_z : m < z := by
        rcases hmz with hcross | ⟨_, hinside⟩
        · exact False.elim ((lt_irrefl y) (by simpa [hm.1, hrz] using hcross))
        · rcases hinside with ⟨_, hz⟩ | ⟨_, _, hmz⟩
          · exact False.elim (hz_ne (hz.symm.trans hrz))
          · exact hmz
      have hzmem : z ∈ s := by simp [s, hrz, hz_ne]
      have hzle : z ≤ m := Finset.le_max' s z hzmem
      exact (not_lt_of_ge hzle) hm_lt_z

/-- Lemma 4.4: descents of Φ are counted by distinct repeated entries of
the restricted-growth word. -/
theorem lemma_4_4 (A : CanonicalPartition n) :
    A.descentNumber = rp A.restrictedGrowthWord := by
  rw [descentNumber, rp, descentBottoms_eq_repeatedRepresentatives,
    repeatedValues_restrictedGrowthWord]

/-! ## Finite weighted sums: Theorem 4.5 -/

/-- In the consecutive-label presentation, the largest restricted-growth
label is the number of fixed representatives, i.e. the number of blocks. -/
def largestLabel (A : CanonicalPartition n) : ℕ :=
  A.blockCount

theorem blockCount_eq_largestLabel (A : CanonicalPartition n) :
    A.blockCount = A.largestLabel := rfl

/-- The inversion-descent weight on the permutation side. -/
noncomputable def permutationWeight {R : Type*} [CommSemiring R]
    (q t : R) (A : CanonicalPartition n) : R :=
  q ^ A.standardInversions * t ^ A.descentNumber

/-- The same weight, stated on an actual permutation rather than the order
model used internally in the partition proof. -/
noncomputable def actualPermutationWeight {R : Type*} [CommSemiring R]
    (q t : R) (σ : Equiv.Perm (Fin n)) : R :=
  q ^ LeanCo.Permutation.inversionNumber σ *
    t ^ LeanCo.Permutation.descentNumber σ

theorem actualPermutationWeight_standardPermutation
    {R : Type*} [CommSemiring R] (q t : R) (A : CanonicalPartition n) :
    actualPermutationWeight q t A.standardPermutation =
      permutationWeight q t A := by
  rw [actualPermutationWeight, permutationWeight,
    standardPermutation_inversionNumber, standardPermutation_descentNumber]

/-- The corresponding restricted-growth-word weight. -/
noncomputable def restrictedGrowthWeight {R : Type*} [CommSemiring R]
    (q t : R) (A : CanonicalPartition n) : R :=
  q ^ (A.wordInversions + n - A.largestLabel) *
    t ^ rp A.restrictedGrowthWord

theorem permutationWeight_eq_restrictedGrowthWeight {R : Type*} [CommSemiring R]
    (q t : R) (A : CanonicalPartition n) :
    permutationWeight q t A = restrictedGrowthWeight q t A := by
  rw [permutationWeight, restrictedGrowthWeight, largestLabel, lemma_4_3, lemma_4_4]

/-- The partition-model form of the weighted sum transport. -/
theorem theorem_4_5_partition_model {R : Type*} [CommSemiring R] (q t : R) :
    (∑ P : SetPartition n,
      permutationWeight q t (CanonicalPartition.ofFinpartition P)) =
    ∑ A : CanonicalPartition n, restrictedGrowthWeight q t A := by
  classical
  calc
    (∑ P : SetPartition n,
        permutationWeight q t (CanonicalPartition.ofFinpartition P)) =
        ∑ A : CanonicalPartition n, permutationWeight q t A := by
          simpa [CanonicalPartition.finpartitionEquiv] using
            ((CanonicalPartition.finpartitionEquiv n).symm.sum_comp
              (fun A : CanonicalPartition n ↦ permutationWeight q t A))
    _ = ∑ A : CanonicalPartition n, restrictedGrowthWeight q t A := by
      apply Fintype.sum_congr
      intro A
      exact permutationWeight_eq_restrictedGrowthWeight q t A

/-- **Theorem 4.5.**  The left side is the genuine inversion/descent
enumerator over the existing subtype of literal `32-1`-avoiding actual
permutations.  Theorem 4.2 transports it to partitions, and Lemmas 4.3 and 4.4
identify each transported weight with its restricted-growth-word weight. -/
theorem theorem_4_5 {R : Type*} [CommSemiring R] (q t : R) :
    (∑ σ : {σ : Equiv.Perm (Fin n) // LeanCo.Permutation.Avoids32_1 σ},
      q ^ LeanCo.Permutation.inversionNumber σ.1 *
        t ^ LeanCo.Permutation.descentNumber σ.1) =
      ∑ A : CanonicalPartition n, restrictedGrowthWeight q t A := by
  classical
  calc
    (∑ σ : {σ : Equiv.Perm (Fin n) // LeanCo.Permutation.Avoids32_1 σ},
        q ^ LeanCo.Permutation.inversionNumber σ.1 *
          t ^ LeanCo.Permutation.descentNumber σ.1) =
        ∑ A : CanonicalPartition n,
          actualPermutationWeight q t A.standardPermutation := by
            simpa [actualPermutationWeight] using
              ((theorem_4_2 n).sum_comp
                (fun σ : {σ : Equiv.Perm (Fin n) //
                    LeanCo.Permutation.Avoids32_1 σ} ↦
                  actualPermutationWeight q t σ.1)).symm
    _ = ∑ A : CanonicalPartition n, restrictedGrowthWeight q t A := by
      apply Fintype.sum_congr
      intro A
      rw [actualPermutationWeight_standardPermutation,
        permutationWeight_eq_restrictedGrowthWeight]

end CanonicalPartition

end LeanCo.SetPartition
