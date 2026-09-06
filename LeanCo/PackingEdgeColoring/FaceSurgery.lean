import LeanCo.PackingEdgeColoring.PlaneRestriction

/-!
# Surgery on facial permutations

This file proves the finite-permutation bookkeeping behind deletion of a
two-sided edge.  The generic operation first joins the two distinct cycles at
the two oriented darts, then splices both deleted darts out of the joined
cycle.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open SimpleGraph

noncomputable section

namespace PermRestriction

variable {alpha : Type*}

/-- Concatenating two disjoint nonempty cyclic lists joins their two cycles by
a transposition of the two chosen heads. -/
theorem formPerm_append_of_disjoint [DecidableEq alpha] :
    ∀ (a b : alpha) (l k : List alpha),
      (a :: l).Nodup → (b :: k).Nodup →
      List.Disjoint (a :: l) (b :: k) →
      List.formPerm ((a :: l) ++ (b :: k)) =
        Equiv.swap a b * List.formPerm (a :: l) *
          List.formPerm (b :: k)
  | a, b, [], k, _, _, _ => by simp
  | a, b, x :: l, k, ha, hb, hd => by
      have hxl : (x :: l).Nodup := ha.of_cons
      have hdis : List.Disjoint (x :: l) (b :: k) := by
        rw [List.disjoint_left] at hd ⊢
        intro z hz
        exact hd (List.mem_cons_of_mem a hz)
      have hab : a ≠ b := by
        intro h
        subst b
        exact (List.disjoint_left.mp hd (List.mem_cons_self)).elim
          (List.mem_cons_self)
      have hxb : x ≠ b := by
        intro h
        subst b
        exact (List.disjoint_left.mp hdis (List.mem_cons_self)).elim
          (List.mem_cons_self)
      change
        List.formPerm (a :: x :: (l ++ (b :: k))) =
          Equiv.swap a b * List.formPerm (a :: x :: l) *
            List.formPerm (b :: k)
      rw [List.formPerm_cons_cons a x (l ++ (b :: k))]
      have ih : List.formPerm (x :: (l ++ (b :: k))) =
          Equiv.swap x b * List.formPerm (x :: l) *
            List.formPerm (b :: k) := by
        exact formPerm_append_of_disjoint x b l k hxl hb hdis
      rw [ih, List.formPerm_cons_cons a x l]
      simp only [← mul_assoc]
      rw [Equiv.mul_swap_eq_swap_mul]
      rw [Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne hab.symm hxb.symm]

/-- Join the cycles through `a` and `b`, then splice both points out.  The
result is kept as a permutation of the ambient type, fixing `a` and `b`; its
restriction to their complement is the surviving facial permutation. -/
def crossErase [DecidableEq alpha] (f : Equiv.Perm alpha) (a b : alpha) :
    Equiv.Perm alpha :=
  erasePoint (erasePoint (Equiv.swap a b * f) a) b

/-- Splice two specified points from one cycle, retaining them as ambient
fixed points. -/
def erasePair [DecidableEq alpha] (f : Equiv.Perm alpha) (a b : alpha) :
    Equiv.Perm alpha :=
  erasePoint (erasePoint f a) b

/-- Away from the spliced point, `erasePoint` either bypasses that point or
agrees with the original permutation. -/
theorem erasePoint_apply_of_ne [DecidableEq alpha]
    (f : Equiv.Perm alpha) (a x : alpha) (hxa : x ≠ a) :
    erasePoint f a x = if f x = a then f a else f x := by
  simp [erasePoint, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
    f.injective.eq_iff, hxa]

theorem crossErase_eq_erasePair [DecidableEq alpha]
    (f : Equiv.Perm alpha) (a b : alpha) :
    crossErase f a b = erasePair (Equiv.swap a b * f) a b := rfl

theorem erasePoint_mul_of_apply_right_eq_self [DecidableEq alpha]
    (f r : Equiv.Perm alpha) (x : alpha) (hrx : r x = x) :
    erasePoint (f * r) x = erasePoint f x * r := by
  simp only [erasePoint, Equiv.Perm.mul_apply, hrx, mul_assoc]

theorem erasePair_mul_of_apply_right_eq_self [DecidableEq alpha]
    (f r : Equiv.Perm alpha) (a b : alpha)
    (hra : r a = a) (hrb : r b = b) :
    erasePair (f * r) a b = erasePair f a b * r := by
  rw [erasePair, erasePoint_mul_of_apply_right_eq_self f r a hra,
    erasePoint_mul_of_apply_right_eq_self (erasePoint f a) r b hrb,
    erasePair]

section Finite

variable [Fintype alpha] [DecidableEq alpha]

/-- Splicing one point from a cycle with at least three support points leaves
a nontrivial cycle. -/
theorem IsCycle.erasePoint_of_three_le {f : Equiv.Perm alpha}
    (hf : f.IsCycle) {x : alpha} (hx : x ∈ f.support)
    (hcard : 3 ≤ f.support.card) :
    (erasePoint f x).IsCycle := by
  have hfx : f x ≠ x := Equiv.Perm.mem_support.mp hx
  have hffx : f (f x) ≠ x := by
    intro htwo
    have heq := hf.eq_swap_of_apply_apply_eq_self hfx htwo
    have htwoCard : f.support.card = 2 := by
      rw [heq, Equiv.Perm.card_support_swap hfx.symm]
    omega
  exact hf.swap_mul hfx hffx

theorem support_erasePoint_le {f : Equiv.Perm alpha} {x : alpha}
    (hx : x ∈ f.support) : (erasePoint f x).support ⊆ f.support := by
  intro y hy
  have hy' := Equiv.Perm.support_mul_le (Equiv.swap x (f x)) f hy
  change y ∈ (Equiv.swap x (f x)).support ∪ f.support at hy'
  rw [Finset.mem_union] at hy'
  rcases hy' with hswap | hf
  · have hfx : f x ≠ x := Equiv.Perm.mem_support.mp hx
    rw [Equiv.Perm.support_swap hfx.symm] at hswap
    rcases Finset.mem_insert.mp hswap with rfl | h
    · exact hx
    · rw [Finset.mem_singleton] at h
      subst y
      exact Equiv.Perm.apply_mem_support.mpr hx
  · exact hf

theorem support_erasePoint_le_of_mem_of_support_le
    (f : Equiv.Perm alpha) (x : alpha) (s : Finset alpha)
    (hx : x ∈ s) (hf : f.support ⊆ s) :
    (erasePoint f x).support ⊆ s := by
  intro y hy
  have hy' := Equiv.Perm.support_mul_le (Equiv.swap x (f x)) f hy
  change y ∈ (Equiv.swap x (f x)).support ∪ f.support at hy'
  rcases Finset.mem_union.mp hy' with hswap | hfy
  · by_cases hfx : f x = x
    · rw [hfx] at hswap
      simp at hswap
    · rw [Equiv.Perm.support_swap (Ne.symm hfx)] at hswap
      rcases Finset.mem_insert.mp hswap with rfl | hyfx
      · exact hx
      · rw [Finset.mem_singleton] at hyfx
        subst y
        exact (Equiv.Perm.isInvariant_of_support_le hf x).mpr hx
  · exact hf hfy

/-- Splicing two distinct support points from a cycle of length at least four
leaves one nontrivial cycle on the surviving support. -/
theorem IsCycle.erasePair_of_four_le {f : Equiv.Perm alpha}
    (hf : f.IsCycle) {a b : alpha} (ha : a ∈ f.support)
    (hb : b ∈ f.support) (hab : a ≠ b)
    (hcard : 4 ≤ f.support.card) :
    (erasePair f a b).IsCycle := by
  have hfirst : (erasePoint f a).IsCycle :=
    IsCycle.erasePoint_of_three_le hf ha (by omega)
  have hfa : f (f a) ≠ a := by
    intro htwo
    have heq := hf.eq_swap_of_apply_apply_eq_self
      (Equiv.Perm.mem_support.mp ha) htwo
    have htwoCard : f.support.card = 2 := by
      rw [heq, Equiv.Perm.card_support_swap
        (Equiv.Perm.mem_support.mp ha).symm]
    omega
  have hsupp : (erasePoint f a).support = f.support.erase a := by
    rw [erasePoint, Equiv.Perm.support_swap_mul_eq f a hfa,
      Finset.sdiff_singleton_eq_erase]
  have hbfirst : b ∈ (erasePoint f a).support := by
    rw [hsupp, Finset.mem_erase]
    exact ⟨hab.symm, hb⟩
  have hcardFirst : 3 ≤ (erasePoint f a).support.card := by
    rw [hsupp, Finset.card_erase_of_mem ha]
    omega
  exact IsCycle.erasePoint_of_three_le hfirst hbfirst hcardFirst

end Finite

theorem not_sameCycle_ne {f : Equiv.Perm alpha} {a b : alpha}
    (h : ¬f.SameCycle a b) : a ≠ b := by
  intro hab
  subst b
  exact h (Equiv.Perm.SameCycle.refl f a)

theorem not_sameCycle_apply_ne_right {f : Equiv.Perm alpha} {a b : alpha}
    (h : ¬f.SameCycle a b) : f a ≠ b := by
  intro hab
  apply h
  exact ⟨1, by simpa only [zpow_one] using hab⟩

theorem not_sameCycle_apply_ne_left {f : Equiv.Perm alpha} {a b : alpha}
    (h : ¬f.SameCycle a b) : f b ≠ a := by
  intro hba
  apply h
  exact (Equiv.Perm.SameCycle.symm ⟨1, by simpa only [zpow_one] using hba⟩)

theorem not_sameCycle_apply_apply_ne_right {f : Equiv.Perm alpha}
    {a b : alpha} (h : ¬f.SameCycle a b) : f (f a) ≠ b := by
  intro htwo
  apply h
  refine ⟨2, ?_⟩
  simpa only [zpow_ofNat, pow_two, Equiv.Perm.mul_apply] using htwo

theorem not_sameCycle_apply_apply_ne_left {f : Equiv.Perm alpha}
    {a b : alpha} (h : ¬f.SameCycle a b) : f (f b) ≠ a := by
  intro htwo
  apply h
  exact Equiv.Perm.SameCycle.symm ⟨2, by
    simpa only [zpow_ofNat, pow_two, Equiv.Perm.mul_apply] using htwo⟩

@[simp]
theorem crossErase_apply_left [DecidableEq alpha] (f : Equiv.Perm alpha)
    {a b : alpha} (hab : ¬f.SameCycle a b) :
    crossErase f a b a = a := by
  let g := erasePoint (Equiv.swap a b * f) a
  have hab' : a ≠ b := not_sameCycle_ne hab
  have hga : g a = a := erasePoint_apply_self _ _
  have hgb : g b ≠ a := by
    intro h
    exact hab' ((g.injective (h.trans hga.symm)).symm)
  rw [crossErase]
  change erasePoint g b a = a
  rw [erasePoint, Equiv.Perm.mul_apply, hga]
  exact Equiv.swap_apply_of_ne_of_ne hab' hgb.symm

@[simp]
theorem crossErase_apply_right [DecidableEq alpha] (f : Equiv.Perm alpha)
    {a b : alpha} (_hab : ¬f.SameCycle a b) :
    crossErase f a b b = b := by
  exact erasePoint_apply_self _ _

theorem crossErase_apply_ne_left_iff [DecidableEq alpha]
    (f : Equiv.Perm alpha) {a b x : alpha} (hab : ¬f.SameCycle a b) :
    crossErase f a b x ≠ a ↔ x ≠ a := by
  constructor
  · intro h hxa
    subst x
    exact h (crossErase_apply_left f hab)
  · intro h hcross
    apply h
    apply (crossErase f a b).injective
    simpa only [crossErase_apply_left f hab] using hcross

theorem crossErase_apply_ne_right_iff [DecidableEq alpha]
    (f : Equiv.Perm alpha) {a b x : alpha} (hab : ¬f.SameCycle a b) :
    crossErase f a b x ≠ b ↔ x ≠ b := by
  constructor
  · intro h hxb
    subst x
    exact h (crossErase_apply_right f hab)
  · intro h hcross
    apply h
    apply (crossErase f a b).injective
    simpa only [crossErase_apply_right f hab] using hcross

/-- Restriction of `crossErase` to the points surviving deletion. -/
def crossEraseRestrict [DecidableEq alpha] (f : Equiv.Perm alpha)
    (a b : alpha) (hab : ¬f.SameCycle a b) :
    Equiv.Perm {x : alpha // x ≠ a ∧ x ≠ b} :=
  (crossErase f a b).subtypePerm fun x ↦ by
    rw [crossErase_apply_ne_left_iff f hab,
      crossErase_apply_ne_right_iff f hab]

@[simp]
theorem crossEraseRestrict_apply_coe [DecidableEq alpha]
    (f : Equiv.Perm alpha) (a b : alpha) (hab : ¬f.SameCycle a b)
    (x : {x : alpha // x ≠ a ∧ x ≠ b}) :
    (crossEraseRestrict f a b hab x : alpha) = crossErase f a b x :=
  rfl

/-- Explicit cross-splicing formula on a surviving point. -/
theorem crossErase_apply_of_ne [DecidableEq alpha]
    (f : Equiv.Perm alpha) (a b x : alpha)
    (hfix : ∀ y, f y ≠ y) (hab : ¬f.SameCycle a b)
    (hxa : x ≠ a) (hxb : x ≠ b) :
    crossErase f a b x =
      if f x = a then f b else if f x = b then f a else f x := by
  have hab' : a ≠ b := not_sameCycle_ne hab
  have hfaa : f a ≠ a := hfix a
  have hfbb : f b ≠ b := hfix b
  have hfab : f a ≠ b := not_sameCycle_apply_ne_right hab
  have hfba : f b ≠ a := not_sameCycle_apply_ne_left hab
  have hff : f a ≠ f b := f.injective.ne hab'
  let m : Equiv.Perm alpha := Equiv.swap a b * f
  let g : Equiv.Perm alpha := erasePoint m a
  have hma : m a = f a := by
    change Equiv.swap a b (f a) = f a
    exact Equiv.swap_apply_of_ne_of_ne hfaa hfab
  have hmb : m b = f b := by
    change Equiv.swap a b (f b) = f b
    exact Equiv.swap_apply_of_ne_of_ne hfba hfbb
  have hgb : g b = f b := by
    change Equiv.swap a (m a) (m b) = f b
    rw [hma, hmb]
    exact Equiv.swap_apply_of_ne_of_ne hfba hff.symm
  change erasePoint g b x = _
  by_cases hfxa : f x = a
  · rw [if_pos hfxa]
    have hmx : m x = b := by
      change Equiv.swap a b (f x) = b
      rw [hfxa, Equiv.swap_apply_left]
    have hgx : g x = b := by
      change Equiv.swap a (m a) (m x) = b
      rw [hma, hmx]
      exact Equiv.swap_apply_of_ne_of_ne hab'.symm hfab.symm
    rw [erasePoint, Equiv.Perm.mul_apply, hgx, hgb,
      Equiv.swap_apply_left]
  · by_cases hfxb : f x = b
    · rw [if_neg hfxa, if_pos hfxb]
      have hmx : m x = a := by
        change Equiv.swap a b (f x) = a
        rw [hfxb, Equiv.swap_apply_right]
      have hgx : g x = f a := by
        change Equiv.swap a (m a) (m x) = f a
        rw [hma, hmx, Equiv.swap_apply_left]
      rw [erasePoint, Equiv.Perm.mul_apply, hgx, hgb]
      exact Equiv.swap_apply_of_ne_of_ne hfab hff
    · have hfxfa : f x ≠ f a := fun h ↦ hxa (f.injective h)
      have hfxfb : f x ≠ f b := fun h ↦ hxb (f.injective h)
      rw [if_neg hfxa, if_neg hfxb]
      have hmx : m x = f x := by
        change Equiv.swap a b (f x) = f x
        exact Equiv.swap_apply_of_ne_of_ne hfxa hfxb
      have hgx : g x = f x := by
        change Equiv.swap a (m a) (m x) = f x
        rw [hma, hmx]
        exact Equiv.swap_apply_of_ne_of_ne hfxa hfxfa
      rw [erasePoint, Equiv.Perm.mul_apply, hgx, hgb]
      exact Equiv.swap_apply_of_ne_of_ne hfxb hfxfb

/-- Under the fixed-point-free hypothesis relevant to facial permutations,
`crossErase` fixes exactly the two deleted points. -/
theorem crossErase_ne_self_iff [DecidableEq alpha]
    (f : Equiv.Perm alpha) (a b x : alpha)
    (hfix : ∀ y, f y ≠ y) (hab : ¬f.SameCycle a b) :
    crossErase f a b x ≠ x ↔ x ≠ a ∧ x ≠ b := by
  constructor
  · intro hx
    constructor
    · intro hxa
      subst x
      exact hx (crossErase_apply_left f hab)
    · intro hxb
      subst x
      exact hx (crossErase_apply_right f hab)
  · rintro ⟨hxa, hxb⟩
    rw [crossErase_apply_of_ne f a b x hfix hab hxa hxb]
    split_ifs with hfxa hfxb
    · intro hfbx
      apply not_sameCycle_apply_apply_ne_left hab
      rw [hfbx, hfxa]
    · intro hfax
      apply not_sameCycle_apply_apply_ne_right hab
      rw [hfax, hfxb]
    · exact hfix x

theorem support_crossErase [Fintype alpha] [DecidableEq alpha]
    (f : Equiv.Perm alpha) (a b : alpha)
    (hfix : ∀ y, f y ≠ y) (hab : ¬f.SameCycle a b) :
    (crossErase f a b).support = (Finset.univ.erase a).erase b := by
  ext x
  rw [Equiv.Perm.mem_support, crossErase_ne_self_iff f a b x hfix hab]
  simp [and_comm]

/-- A transposition joining representatives of two distinct cycles turns the
two canonical cycle factors into one cycle. -/
theorem isCycle_join_cycleOf [Fintype alpha] [DecidableEq alpha]
    (f : Equiv.Perm alpha) (a b : alpha)
    (hfix : ∀ y, f y ≠ y) (hab : ¬f.SameCycle a b) :
    (Equiv.swap a b * f.cycleOf a * f.cycleOf b).IsCycle := by
  let la := f.toList a
  let lb := f.toList b
  have hsa : a ∈ f.support := Equiv.Perm.mem_support.mpr (hfix a)
  have hsb : b ∈ f.support := Equiv.Perm.mem_support.mpr (hfix b)
  have hla2 : 2 ≤ la.length := by
    exact Equiv.Perm.two_le_length_toList_iff_mem_support.mpr hsa
  have hlb2 : 2 ≤ lb.length := by
    exact Equiv.Perm.two_le_length_toList_iff_mem_support.mpr hsb
  have hla0 : la ≠ [] :=
    List.ne_nil_of_length_pos (Nat.zero_lt_two.trans_le hla2)
  have hlb0 : lb ≠ [] :=
    List.ne_nil_of_length_pos (Nat.zero_lt_two.trans_le hlb2)
  have hheada : la.head hla0 = a := by
    rw [List.head_eq_getElem]
    exact Equiv.Perm.toList_getElem_zero f a hsa
  have hheadb : lb.head hlb0 = b := by
    rw [List.head_eq_getElem]
    exact Equiv.Perm.toList_getElem_zero f b hsb
  have hla : a :: la.tail = la := by
    rw [← hheada]
    exact List.cons_head_tail hla0
  have hlb : b :: lb.tail = lb := by
    rw [← hheadb]
    exact List.cons_head_tail hlb0
  have hdis : List.Disjoint la lb := by
    rw [List.disjoint_left]
    intro x hxa hxb
    have hax := (Equiv.Perm.mem_toList_iff.mp hxa).1
    have hbx := (Equiv.Perm.mem_toList_iff.mp hxb).1
    exact hab (hax.trans hbx.symm)
  have hnoda : (a :: la.tail).Nodup := by
    rw [hla]
    exact Equiv.Perm.nodup_toList f a
  have hnodb : (b :: lb.tail).Nodup := by
    rw [hlb]
    exact Equiv.Perm.nodup_toList f b
  have hdis' : List.Disjoint (a :: la.tail) (b :: lb.tail) := by
    rw [hla, hlb]
    exact hdis
  have happNodup : (la ++ lb).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨Equiv.Perm.nodup_toList f a,
      Equiv.Perm.nodup_toList f b, ?_⟩
    intro x hxa y hyb hxy
    subst y
    exact (List.disjoint_left.mp hdis hxa) hyb
  have happLen : 2 ≤ (la ++ lb).length := by
    simp only [List.length_append]
    omega
  have hcycle : (la ++ lb).formPerm.IsCycle :=
    List.isCycle_formPerm happNodup happLen
  have heq := formPerm_append_of_disjoint a b la.tail lb.tail
    hnoda hnodb hdis'
  rw [hla, hlb, Equiv.Perm.formPerm_toList,
    Equiv.Perm.formPerm_toList] at heq
  rw [← heq]
  exact hcycle

/-- Concrete list description of the joined cycle. -/
theorem join_cycleOf_eq_formPerm_append [Fintype alpha]
    [DecidableEq alpha] (f : Equiv.Perm alpha) (a b : alpha)
    (hfix : ∀ y, f y ≠ y) (hab : ¬f.SameCycle a b) :
    Equiv.swap a b * f.cycleOf a * f.cycleOf b =
      (f.toList a ++ f.toList b).formPerm := by
  let la := f.toList a
  let lb := f.toList b
  have hsa : a ∈ f.support := Equiv.Perm.mem_support.mpr (hfix a)
  have hsb : b ∈ f.support := Equiv.Perm.mem_support.mpr (hfix b)
  have hla2 : 2 ≤ la.length :=
    Equiv.Perm.two_le_length_toList_iff_mem_support.mpr hsa
  have hlb2 : 2 ≤ lb.length :=
    Equiv.Perm.two_le_length_toList_iff_mem_support.mpr hsb
  have hla0 : la ≠ [] :=
    List.ne_nil_of_length_pos (Nat.zero_lt_two.trans_le hla2)
  have hlb0 : lb ≠ [] :=
    List.ne_nil_of_length_pos (Nat.zero_lt_two.trans_le hlb2)
  have hheada : la.head hla0 = a := by
    rw [List.head_eq_getElem]
    exact Equiv.Perm.toList_getElem_zero f a hsa
  have hheadb : lb.head hlb0 = b := by
    rw [List.head_eq_getElem]
    exact Equiv.Perm.toList_getElem_zero f b hsb
  have hla : a :: la.tail = la := by
    rw [← hheada]
    exact List.cons_head_tail hla0
  have hlb : b :: lb.tail = lb := by
    rw [← hheadb]
    exact List.cons_head_tail hlb0
  have hdis : List.Disjoint la lb := by
    rw [List.disjoint_left]
    intro x hxa hxb
    have hax := (Equiv.Perm.mem_toList_iff.mp hxa).1
    have hbx := (Equiv.Perm.mem_toList_iff.mp hxb).1
    exact hab (hax.trans hbx.symm)
  have hnoda : (a :: la.tail).Nodup := by
    rw [hla]
    exact Equiv.Perm.nodup_toList f a
  have hnodb : (b :: lb.tail).Nodup := by
    rw [hlb]
    exact Equiv.Perm.nodup_toList f b
  have hdis' : List.Disjoint (a :: la.tail) (b :: lb.tail) := by
    rw [hla, hlb]
    exact hdis
  have heq := formPerm_append_of_disjoint a b la.tail lb.tail
    hnoda hnodb hdis'
  rw [hla, hlb, Equiv.Perm.formPerm_toList,
    Equiv.Perm.formPerm_toList] at heq
  exact heq.symm

theorem four_le_card_support_join_cycleOf [Fintype alpha]
    [DecidableEq alpha] (f : Equiv.Perm alpha) (a b : alpha)
    (hfix : ∀ y, f y ≠ y) (hab : ¬f.SameCycle a b) :
    4 ≤ (Equiv.swap a b * f.cycleOf a * f.cycleOf b).support.card := by
  let l := f.toList a ++ f.toList b
  have hsa : a ∈ f.support := Equiv.Perm.mem_support.mpr (hfix a)
  have hsb : b ∈ f.support := Equiv.Perm.mem_support.mpr (hfix b)
  have hla2 : 2 ≤ (f.toList a).length :=
    Equiv.Perm.two_le_length_toList_iff_mem_support.mpr hsa
  have hlb2 : 2 ≤ (f.toList b).length :=
    Equiv.Perm.two_le_length_toList_iff_mem_support.mpr hsb
  have hdis : List.Disjoint (f.toList a) (f.toList b) := by
    rw [List.disjoint_left]
    intro x hxa hxb
    have hax := (Equiv.Perm.mem_toList_iff.mp hxa).1
    have hbx := (Equiv.Perm.mem_toList_iff.mp hxb).1
    exact hab (hax.trans hbx.symm)
  have hnodup : l.Nodup := by
    apply List.nodup_append.mpr
    refine ⟨Equiv.Perm.nodup_toList f a,
      Equiv.Perm.nodup_toList f b, ?_⟩
    intro x hxa y hyb hxy
    subst y
    exact (List.disjoint_left.mp hdis hxa) hyb
  have hlen : 4 ≤ l.length := by
    simp only [l, List.length_append]
    omega
  have hnonsingle : ∀ x : alpha, l ≠ [x] := by
    intro x hx
    have := congrArg List.length hx
    simp only [List.length_cons, List.length_nil] at this
    omega
  rw [join_cycleOf_eq_formPerm_append f a b hfix hab,
    List.support_formPerm_of_nodup l hnodup hnonsingle,
    List.toFinset_card_of_nodup hnodup]
  exact hlen

/-- After the two representatives are removed from the joined cycle, the
remaining affected points still form exactly one nontrivial cycle. -/
theorem isCycle_erasePair_join_cycleOf [Fintype alpha]
    [DecidableEq alpha] (f : Equiv.Perm alpha) (a b : alpha)
    (hfix : ∀ y, f y ≠ y) (hab : ¬f.SameCycle a b) :
    (erasePair (Equiv.swap a b * f.cycleOf a * f.cycleOf b) a b).IsCycle := by
  let j := Equiv.swap a b * f.cycleOf a * f.cycleOf b
  let l := f.toList a ++ f.toList b
  have hsa : a ∈ f.support := Equiv.Perm.mem_support.mpr (hfix a)
  have hsb : b ∈ f.support := Equiv.Perm.mem_support.mpr (hfix b)
  have hdis : List.Disjoint (f.toList a) (f.toList b) := by
    rw [List.disjoint_left]
    intro x hxa hxb
    have hax := (Equiv.Perm.mem_toList_iff.mp hxa).1
    have hbx := (Equiv.Perm.mem_toList_iff.mp hxb).1
    exact hab (hax.trans hbx.symm)
  have hnodup : l.Nodup := by
    apply List.nodup_append.mpr
    refine ⟨Equiv.Perm.nodup_toList f a,
      Equiv.Perm.nodup_toList f b, ?_⟩
    intro x hxa y hyb hxy
    subst y
    exact (List.disjoint_left.mp hdis hxa) hyb
  have hlen : 4 ≤ l.length := by
    simp only [l, List.length_append]
    have hla := Equiv.Perm.two_le_length_toList_iff_mem_support.mpr hsa
    have hlb := Equiv.Perm.two_le_length_toList_iff_mem_support.mpr hsb
    omega
  have hnonsingle : ∀ x : alpha, l ≠ [x] := by
    intro x hx
    have := congrArg List.length hx
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hjsupport : j.support = l.toFinset := by
    change (Equiv.swap a b * f.cycleOf a * f.cycleOf b).support =
      (f.toList a ++ f.toList b).toFinset
    rw [join_cycleOf_eq_formPerm_append f a b hfix hab]
    exact List.support_formPerm_of_nodup l hnodup hnonsingle
  have haj : a ∈ j.support := by
    rw [hjsupport, List.mem_toFinset]
    change a ∈ f.toList a ++ f.toList b
    rw [List.mem_append]
    left
    exact Equiv.Perm.mem_toList_iff.mpr
      ⟨Equiv.Perm.SameCycle.refl f a, hsa⟩
  have hbj : b ∈ j.support := by
    rw [hjsupport, List.mem_toFinset]
    change b ∈ f.toList a ++ f.toList b
    rw [List.mem_append]
    right
    exact Equiv.Perm.mem_toList_iff.mpr
      ⟨Equiv.Perm.SameCycle.refl f b, hsb⟩
  have hj : j.IsCycle := isCycle_join_cycleOf f a b hfix hab
  have hjcard : 4 ≤ j.support.card :=
    four_le_card_support_join_cycleOf f a b hfix hab
  exact IsCycle.erasePair_of_four_le hj haj hbj
    (not_sameCycle_ne hab) hjcard

theorem support_erasePair_join_cycleOf_le [Fintype alpha]
    [DecidableEq alpha] (f : Equiv.Perm alpha) (a b : alpha)
    (hfix : ∀ y, f y ≠ y) (hab : ¬f.SameCycle a b) :
    (erasePair (Equiv.swap a b * f.cycleOf a * f.cycleOf b) a b).support ⊆
      (f.cycleOf a).support ∪ (f.cycleOf b).support := by
  let ca := f.cycleOf a
  let cb := f.cycleOf b
  let u := ca.support ∪ cb.support
  let j := Equiv.swap a b * ca * cb
  have hab' : a ≠ b := not_sameCycle_ne hab
  have ha : a ∈ ca.support := by
    change a ∈ (f.cycleOf a).support
    rw [Equiv.Perm.mem_support, Equiv.Perm.cycleOf_apply_self]
    exact hfix a
  have hb : b ∈ cb.support := by
    change b ∈ (f.cycleOf b).support
    rw [Equiv.Perm.mem_support, Equiv.Perm.cycleOf_apply_self]
    exact hfix b
  have hau : a ∈ u := Finset.mem_union_left _ ha
  have hbu : b ∈ u := Finset.mem_union_right _ hb
  have hjle : j.support ⊆ u := by
    intro x hx
    have hx' := Equiv.Perm.support_mul_le (Equiv.swap a b * ca) cb hx
    change x ∈ (Equiv.swap a b * ca).support ∪ cb.support at hx'
    rcases Finset.mem_union.mp hx' with hleft | hcb
    · have hx'' := Equiv.Perm.support_mul_le (Equiv.swap a b) ca hleft
      change x ∈ (Equiv.swap a b).support ∪ ca.support at hx''
      rcases Finset.mem_union.mp hx'' with hswap | hca
      · rw [Equiv.Perm.support_swap hab'] at hswap
        rcases Finset.mem_insert.mp hswap with rfl | hxb
        · exact hau
        · rw [Finset.mem_singleton] at hxb
          subst x
          exact hbu
      · exact Finset.mem_union_left _ hca
    · exact Finset.mem_union_right _ hcb
  have hfirst : (erasePoint j a).support ⊆ u :=
    support_erasePoint_le_of_mem_of_support_le j a u hau hjle
  have hsecond : (erasePoint (erasePoint j a) b).support ⊆ u :=
    support_erasePoint_le_of_mem_of_support_le (erasePoint j a) b u hbu hfirst
  exact hsecond

/-- The untouched cycle factors after removing the factors through `a` and
`b`. -/
def remainingCycleFactors [Fintype alpha] [DecidableEq alpha]
    (f : Equiv.Perm alpha) (a b : alpha) : Finset (Equiv.Perm alpha) :=
  (f.cycleFactorsFinset.erase (f.cycleOf a)).erase (f.cycleOf b)

theorem remainingCycleFactors_pairwise_commute [Fintype alpha]
    [DecidableEq alpha] (f : Equiv.Perm alpha) (a b : alpha) :
    (remainingCycleFactors f a b : Set (Equiv.Perm alpha)).Pairwise Commute := by
  intro c hc d hd hcd
  exact Equiv.Perm.cycleFactorsFinset_mem_commute' f
    (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hc))
    (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hd))

theorem remainingCycleFactors_pairwise_disjoint [Fintype alpha]
    [DecidableEq alpha] (f : Equiv.Perm alpha) (a b : alpha) :
    (remainingCycleFactors f a b : Set (Equiv.Perm alpha)).Pairwise
      Equiv.Perm.Disjoint := by
  intro c hc d hd hcd
  apply Equiv.Perm.cycleFactorsFinset_pairwise_disjoint f
  · exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hc)
  · exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hd)
  · exact hcd

/-- Product of all cycle factors not meeting the two selected orbits. -/
def cycleRemainder [Fintype alpha] [DecidableEq alpha]
    (f : Equiv.Perm alpha) (a b : alpha) : Equiv.Perm alpha :=
  (f * (f.cycleOf a)⁻¹) * (f.cycleOf b)⁻¹

theorem cycleFactorsFinset_cycleRemainder [Fintype alpha]
    [DecidableEq alpha] (f : Equiv.Perm alpha) (a b : alpha)
    (hfix : ∀ y, f y ≠ y) (hab : ¬f.SameCycle a b) :
    (cycleRemainder f a b).cycleFactorsFinset = remainingCycleFactors f a b := by
  let ca := f.cycleOf a
  let cb := f.cycleOf b
  have hsa : a ∈ f.support := Equiv.Perm.mem_support.mpr (hfix a)
  have hsb : b ∈ f.support := Equiv.Perm.mem_support.mpr (hfix b)
  have hca : ca ∈ f.cycleFactorsFinset :=
    Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr hsa
  have hcb : cb ∈ f.cycleFactorsFinset :=
    Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr hsb
  have hne : ca ≠ cb := by
    intro h
    apply hab
    exact (Equiv.Perm.sameCycle_iff_cycleOf_eq_of_mem_support hsa hsb).mpr h
  have hcb' : cb ∈ (f * ca⁻¹).cycleFactorsFinset := by
    rw [Equiv.Perm.cycleFactorsFinset_mul_inv_mem_eq_sdiff hca]
    exact Finset.mem_sdiff.mpr ⟨hcb, by simpa using hne.symm⟩
  rw [cycleRemainder,
    Equiv.Perm.cycleFactorsFinset_mul_inv_mem_eq_sdiff hcb',
    Equiv.Perm.cycleFactorsFinset_mul_inv_mem_eq_sdiff hca]
  simp only [remainingCycleFactors, ca, cb,
    Finset.sdiff_singleton_eq_erase]

/-- The original permutation is the product of the two selected cycle
factors and the untouched remainder. -/
theorem cycleOf_mul_cycleOf_mul_cycleRemainder [Fintype alpha]
    [DecidableEq alpha] (f : Equiv.Perm alpha) (a b : alpha)
    (hfix : ∀ y, f y ≠ y) (hab : ¬f.SameCycle a b) :
    f.cycleOf a * f.cycleOf b * cycleRemainder f a b = f := by
  let S := f.cycleFactorsFinset
  let ca := f.cycleOf a
  let cb := f.cycleOf b
  let S₁ := S.erase ca
  let T := S₁.erase cb
  have hsa : a ∈ f.support := Equiv.Perm.mem_support.mpr (hfix a)
  have hsb : b ∈ f.support := Equiv.Perm.mem_support.mpr (hfix b)
  have hca : ca ∈ S := by
    exact Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr hsa
  have hcb : cb ∈ S := by
    exact Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr hsb
  have hne : ca ≠ cb := by
    intro h
    apply hab
    exact (Equiv.Perm.sameCycle_iff_cycleOf_eq_of_mem_support hsa hsb).mpr h
  have hcaf : Commute ca f := Equiv.Perm.self_mem_cycle_factors_commute hca
  have hcbf : Commute cb f := Equiv.Perm.self_mem_cycle_factors_commute hcb
  have hcab : Commute ca cb :=
    Equiv.Perm.cycleFactorsFinset_mem_commute' f hca hcb
  change ca * cb * cycleRemainder f a b = f
  change ca * cb * ((f * ca⁻¹) * cb⁻¹) = f
  calc
    ca * cb * ((f * ca⁻¹) * cb⁻¹) =
        ca * cb * ((ca⁻¹ * f) * cb⁻¹) := by
      rw [hcaf.inv_left.eq]
    _ = ca * (cb * ca⁻¹) * f * cb⁻¹ := by
      simp only [mul_assoc]
    _ = ca * (ca⁻¹ * cb) * f * cb⁻¹ := by
      rw [hcab.inv_left.eq]
    _ = cb * f * cb⁻¹ := by simp only [mul_assoc, mul_inv_cancel_left]
    _ = f * cb * cb⁻¹ := by rw [hcbf.eq]
    _ = f := by simp

theorem cycleRemainder_apply_left [Fintype alpha] [DecidableEq alpha]
    (f : Equiv.Perm alpha) (a b : alpha)
    (hfix : ∀ y, f y ≠ y) (hab : ¬f.SameCycle a b) :
    cycleRemainder f a b a = a := by
  rw [← Equiv.Perm.notMem_support]
  intro har
  obtain ⟨c, hcR, hac⟩ :=
    Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset.mp har
  rw [cycleFactorsFinset_cycleRemainder f a b hfix hab] at hcR
  rcases Finset.mem_erase.mp hcR with ⟨hcneB, hcR⟩
  rcases Finset.mem_erase.mp hcR with ⟨hcneA, hcS⟩
  have ha : a ∈ (f.cycleOf a).support := by
    rw [Equiv.Perm.mem_support, Equiv.Perm.cycleOf_apply_self]
    exact hfix a
  have hca : f.cycleOf a ∈ f.cycleFactorsFinset :=
    Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr
      (Equiv.Perm.mem_support.mpr (hfix a))
  have hd := Equiv.Perm.cycleFactorsFinset_pairwise_disjoint f
    hcS hca hcneA
  exact (hd.mem_imp hac) ha

theorem cycleRemainder_apply_right [Fintype alpha] [DecidableEq alpha]
    (f : Equiv.Perm alpha) (a b : alpha)
    (hfix : ∀ y, f y ≠ y) (hab : ¬f.SameCycle a b) :
    cycleRemainder f a b b = b := by
  rw [← Equiv.Perm.notMem_support]
  intro hbr
  obtain ⟨c, hcR, hbc⟩ :=
    Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset.mp hbr
  rw [cycleFactorsFinset_cycleRemainder f a b hfix hab] at hcR
  rcases Finset.mem_erase.mp hcR with ⟨hcneB, hcR⟩
  rcases Finset.mem_erase.mp hcR with ⟨hcneA, hcS⟩
  have hb : b ∈ (f.cycleOf b).support := by
    rw [Equiv.Perm.mem_support, Equiv.Perm.cycleOf_apply_self]
    exact hfix b
  have hcb : f.cycleOf b ∈ f.cycleFactorsFinset :=
    Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr
      (Equiv.Perm.mem_support.mpr (hfix b))
  have hd := Equiv.Perm.cycleFactorsFinset_pairwise_disjoint f
    hcS hcb hcneB
  exact (hd.mem_imp hbc) hb

theorem erasePair_join_disjoint_cycleRemainder [Fintype alpha]
    [DecidableEq alpha] (f : Equiv.Perm alpha) (a b : alpha)
    (hfix : ∀ y, f y ≠ y) (hab : ¬f.SameCycle a b) :
    Equiv.Perm.Disjoint
      (erasePair (Equiv.swap a b * f.cycleOf a * f.cycleOf b) a b)
      (cycleRemainder f a b) := by
  rw [Equiv.Perm.disjoint_iff_disjoint_support, Finset.disjoint_left]
  intro x hxm hxr
  have hxu := support_erasePair_join_cycleOf_le f a b hfix hab hxm
  obtain ⟨c, hcR, hxc⟩ :=
    Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset.mp hxr
  rw [cycleFactorsFinset_cycleRemainder f a b hfix hab] at hcR
  rcases Finset.mem_erase.mp hcR with ⟨hcneB, hcR⟩
  rcases Finset.mem_erase.mp hcR with ⟨hcneA, hcS⟩
  rcases Finset.mem_union.mp hxu with hxa | hxb
  · have hca : f.cycleOf a ∈ f.cycleFactorsFinset :=
      Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr
        (Equiv.Perm.mem_support.mpr (hfix a))
    have hd := Equiv.Perm.cycleFactorsFinset_pairwise_disjoint f
      hcS hca hcneA
    exact (hd.mem_imp hxc) hxa
  · have hcb : f.cycleOf b ∈ f.cycleFactorsFinset :=
      Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr
        (Equiv.Perm.mem_support.mpr (hfix b))
    have hd := Equiv.Perm.cycleFactorsFinset_pairwise_disjoint f
      hcS hcb hcneB
    exact (hd.mem_imp hxc) hxb

theorem crossErase_eq_join_mul_remainder [Fintype alpha]
    [DecidableEq alpha] (f : Equiv.Perm alpha) (a b : alpha)
    (hfix : ∀ y, f y ≠ y) (hab : ¬f.SameCycle a b) :
    crossErase f a b =
      erasePair (Equiv.swap a b * f.cycleOf a * f.cycleOf b) a b *
        cycleRemainder f a b := by
  have hfac := cycleOf_mul_cycleOf_mul_cycleRemainder f a b hfix hab
  calc
    crossErase f a b = erasePair (Equiv.swap a b * f) a b := rfl
    _ = erasePair
        (Equiv.swap a b *
          (f.cycleOf a * f.cycleOf b * cycleRemainder f a b)) a b := by
      rw [hfac]
    _ = erasePair
        ((Equiv.swap a b * f.cycleOf a * f.cycleOf b) *
          cycleRemainder f a b) a b := by
      simp only [mul_assoc]
    _ = erasePair (Equiv.swap a b * f.cycleOf a * f.cycleOf b) a b *
        cycleRemainder f a b :=
      erasePair_mul_of_apply_right_eq_self _ _ _ _
        (cycleRemainder_apply_left f a b hfix hab)
        (cycleRemainder_apply_right f a b hfix hab)

theorem cycleFactorsFinset_crossErase [Fintype alpha]
    [DecidableEq alpha] (f : Equiv.Perm alpha) (a b : alpha)
    (hfix : ∀ y, f y ≠ y) (hab : ¬f.SameCycle a b) :
    (crossErase f a b).cycleFactorsFinset =
      {erasePair (Equiv.swap a b * f.cycleOf a * f.cycleOf b) a b} ∪
        remainingCycleFactors f a b := by
  let m := erasePair (Equiv.swap a b * f.cycleOf a * f.cycleOf b) a b
  let r := cycleRemainder f a b
  have hm : m.IsCycle := isCycle_erasePair_join_cycleOf f a b hfix hab
  have hd : Equiv.Perm.Disjoint m r :=
    erasePair_join_disjoint_cycleRemainder f a b hfix hab
  rw [crossErase_eq_join_mul_remainder f a b hfix hab,
    hd.cycleFactorsFinset_mul_eq_union,
    hm.cycleFactorsFinset_eq_singleton,
    cycleFactorsFinset_cycleRemainder f a b hfix hab]

theorem card_cycleFactorsFinset_crossErase_add_one [Fintype alpha]
    [DecidableEq alpha] (f : Equiv.Perm alpha) (a b : alpha)
    (hfix : ∀ y, f y ≠ y) (hab : ¬f.SameCycle a b) :
    (crossErase f a b).cycleFactorsFinset.card + 1 =
      f.cycleFactorsFinset.card := by
  let ca := f.cycleOf a
  let cb := f.cycleOf b
  let m := erasePair (Equiv.swap a b * ca * cb) a b
  let T := remainingCycleFactors f a b
  have hsa : a ∈ f.support := Equiv.Perm.mem_support.mpr (hfix a)
  have hsb : b ∈ f.support := Equiv.Perm.mem_support.mpr (hfix b)
  have hca : ca ∈ f.cycleFactorsFinset :=
    Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr hsa
  have hcb : cb ∈ f.cycleFactorsFinset :=
    Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr hsb
  have hne : ca ≠ cb := by
    intro h
    apply hab
    exact (Equiv.Perm.sameCycle_iff_cycleOf_eq_of_mem_support hsa hsb).mpr h
  have hcbErase : cb ∈ f.cycleFactorsFinset.erase ca :=
    Finset.mem_erase.mpr ⟨hne.symm, hcb⟩
  have hcardA : (f.cycleFactorsFinset.erase ca).card + 1 =
      f.cycleFactorsFinset.card := Finset.card_erase_add_one hca
  have hcardB : ((f.cycleFactorsFinset.erase ca).erase cb).card + 1 =
      (f.cycleFactorsFinset.erase ca).card :=
    Finset.card_erase_add_one hcbErase
  have hm : m.IsCycle := isCycle_erasePair_join_cycleOf f a b hfix hab
  have hd : Equiv.Perm.Disjoint m (cycleRemainder f a b) :=
    erasePair_join_disjoint_cycleRemainder f a b hfix hab
  have hfactorDisjoint := hd.disjoint_cycleFactorsFinset
  rw [hm.cycleFactorsFinset_eq_singleton,
    cycleFactorsFinset_cycleRemainder f a b hfix hab] at hfactorDisjoint
  rw [cycleFactorsFinset_crossErase f a b hfix hab,
    Finset.card_union_of_disjoint hfactorDisjoint]
  simp only [Finset.card_singleton]
  change 1 + ((f.cycleFactorsFinset.erase ca).erase cb).card + 1 =
    f.cycleFactorsFinset.card
  omega

/-- Extending the surviving-point restriction back by the identity recovers
the ambient cross-spliced permutation. -/
theorem ofSubtype_crossEraseRestrict [Fintype alpha]
    [DecidableEq alpha] (f : Equiv.Perm alpha) (a b : alpha)
    (hfix : ∀ y, f y ≠ y) (hab : ¬f.SameCycle a b) :
    Equiv.Perm.ofSubtype (crossEraseRestrict f a b hab) =
      crossErase f a b := by
  exact Equiv.Perm.ofSubtype_subtypePerm
    (fun x ↦ by
      rw [crossErase_apply_ne_left_iff f hab,
        crossErase_apply_ne_right_iff f hab])
    (fun x hx ↦ (crossErase_ne_self_iff f a b x hfix hab).mp hx)

/-- The number of nontrivial cycle factors is the cardinality of the cycle
type multiset. -/
theorem card_cycleFactorsFinset_eq_card_cycleType [Fintype alpha]
    [DecidableEq alpha] (f : Equiv.Perm alpha) :
    f.cycleFactorsFinset.card = f.cycleType.card := by
  rw [Equiv.Perm.cycleType_def, Multiset.card_map]
  rfl

/-- Relabelling a finite permutation across an equivalence preserves its
cycle type. -/
theorem cycleType_permCongr {beta : Type*} [Fintype alpha]
    [DecidableEq alpha] [Fintype beta] [DecidableEq beta]
    (e : alpha ≃ beta) (f : Equiv.Perm alpha) :
    (e.permCongr f).cycleType = f.cycleType := by
  let eu : alpha ≃ (Set.univ : Set beta) :=
    e.trans (Equiv.Set.univ beta).symm
  have hext : f.extendDomain eu = e.permCongr f := by
    apply Equiv.ext
    intro y
    rw [Equiv.Perm.extendDomain_apply_subtype f eu (Set.mem_univ y),
      Equiv.permCongr_apply]
    rfl
  rw [← hext]
  exact Equiv.Perm.cycleType_extendDomain eu

/-- Relabelling a finite permutation preserves the number of nontrivial
cycle factors. -/
theorem card_cycleFactorsFinset_permCongr {beta : Type*}
    [Fintype alpha] [DecidableEq alpha] [Fintype beta] [DecidableEq beta]
    (e : alpha ≃ beta) (f : Equiv.Perm alpha) :
    (e.permCongr f).cycleFactorsFinset.card =
      f.cycleFactorsFinset.card := by
  rw [card_cycleFactorsFinset_eq_card_cycleType,
    card_cycleFactorsFinset_eq_card_cycleType,
    cycleType_permCongr]

/-- Restricting `crossErase` to the surviving points preserves its nontrivial
cycle count. -/
theorem card_cycleFactorsFinset_crossEraseRestrict [Fintype alpha]
    [DecidableEq alpha] (f : Equiv.Perm alpha) (a b : alpha)
    (hfix : ∀ y, f y ≠ y) (hab : ¬f.SameCycle a b) :
    (crossEraseRestrict f a b hab).cycleFactorsFinset.card =
      (crossErase f a b).cycleFactorsFinset.card := by
  rw [card_cycleFactorsFinset_eq_card_cycleType,
    card_cycleFactorsFinset_eq_card_cycleType]
  rw [← Equiv.Perm.cycleType_ofSubtype,
    ofSubtype_crossEraseRestrict f a b hfix hab]

/-- The surviving facial permutation has exactly one fewer nontrivial cycle
than the original fixed-point-free permutation when the deleted points lie on
different cycles. -/
theorem card_cycleFactorsFinset_crossEraseRestrict_add_one [Fintype alpha]
    [DecidableEq alpha] (f : Equiv.Perm alpha) (a b : alpha)
    (hfix : ∀ y, f y ≠ y) (hab : ¬f.SameCycle a b) :
    (crossEraseRestrict f a b hab).cycleFactorsFinset.card + 1 =
      f.cycleFactorsFinset.card := by
  rw [card_cycleFactorsFinset_crossEraseRestrict f a b hfix hab]
  exact card_cycleFactorsFinset_crossErase_add_one f a b hfix hab

end PermRestriction

variable {V : Type*} {G : SimpleGraph V}

/-- Darts after deleting the edge represented by `a` are exactly the ambient
darts other than its two orientations. -/
def dartDeleteEdgeEquiv (e : Sym2 V) (a : G.Dart) (ha : a.edge = e) :
    (G.deleteEdges {e}).Dart ≃
      {d : G.Dart // d ≠ a ∧ d ≠ a.symm} where
  toFun d := ⟨dartEmbeddingOfLE (G.deleteEdges_le {e}) d, by
    constructor
    · intro hda
      have hnot := (SimpleGraph.deleteEdges_adj.mp d.adj).2
      apply hnot
      simp only [Set.mem_singleton_iff]
      change (dartEmbeddingOfLE (G.deleteEdges_le {e}) d).edge = e
      rw [hda, ha]
    · intro hda
      have hnot := (SimpleGraph.deleteEdges_adj.mp d.adj).2
      apply hnot
      simp only [Set.mem_singleton_iff]
      change (dartEmbeddingOfLE (G.deleteEdges_le {e}) d).edge = e
      rw [hda, Dart.edge_symm, ha]⟩
  invFun d := by
    have hedge : d.1.edge ≠ e := by
      intro hde
      have heq : d.1.edge = a.edge := hde.trans ha.symm
      rcases (dart_edge_eq_iff d.1 a).mp heq with hsame | hsymm
      · exact d.2.1 hsame
      · exact d.2.2 hsymm
    exact ⟨d.1.toProd, SimpleGraph.deleteEdges_adj.mpr
      ⟨d.1.adj, by
        simp only [Set.mem_singleton_iff]
        simpa only [Dart.edge] using hedge⟩⟩
  left_inv d := by
    apply Dart.ext
    rfl
  right_inv d := by
    apply Subtype.ext
    apply Dart.ext
    rfl

@[simp]
theorem dartDeleteEdgeEquiv_apply_coe
    (e : Sym2 V) (a : G.Dart) (ha : a.edge = e)
    (d : (G.deleteEdges {e}).Dart) :
    ((dartDeleteEdgeEquiv e a ha d :
      {d : G.Dart // d ≠ a ∧ d ≠ a.symm}) : G.Dart) =
      dartEmbeddingOfLE (G.deleteEdges_le {e}) d := rfl

@[simp]
theorem dartDeleteEdgeEquiv_symm_coe
    (e : Sym2 V) (a : G.Dart) (ha : a.edge = e)
    (d : {d : G.Dart // d ≠ a ∧ d ≠ a.symm}) :
    dartEmbeddingOfLE (G.deleteEdges_le {e})
      ((dartDeleteEdgeEquiv e a ha).symm d) = d.1 := by
  exact congrArg Subtype.val ((dartDeleteEdgeEquiv e a ha).apply_symm_apply d)

namespace RotationSystem

variable (R : RotationSystem G)

/-- Evaluate an assembled global rotation through any chosen proof of the
initial vertex.  Packaging the equality in the sigma type avoids dependent
casts between outgoing-dart fibres. -/
theorem ofVertexPermutations_rotation_apply_eq
    (ρ : ∀ v : V, Equiv.Perm (OutDart G v))
    (hρ : ∀ v, (ρ v).IsCycleOn Set.univ)
    (d : G.Dart) (v : V) (hv : d.fst = v) :
    (ofVertexPermutations ρ hρ).rotation d = (ρ v ⟨d, hv⟩).1 := by
  subst v
  rfl

/-- Splicing inside one outgoing-dart fibre agrees, after forgetting the
fibre proof, with splicing the global rotation at the same dart. -/
@[simp]
theorem erasePoint_atVertex_apply_coe [DecidableEq V]
    [DecidableRel G.Adj] (a : G.Dart) (d : OutDart G a.fst) :
    (PermRestriction.erasePoint (R.atVertex a.fst) (outDartSelf a) d).1 =
      PermRestriction.erasePoint R.rotation a d.1 := by
  simp [PermRestriction.erasePoint, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def, atVertex, outDartSelf, Subtype.ext_iff]
  split_ifs <;> rfl

@[simp]
theorem outDartEmbeddingOfLE_coe {H : SimpleGraph V} (h : H ≤ G)
    (v : V) (d : OutDart H v) :
    (outDartEmbeddingOfLE h v d).1 = dartEmbeddingOfLE h d.1 := rfl

@[simp]
theorem deleteEdge_rotation_apply [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (e : Sym2 V) (a : G.Dart) (ha : a.edge = e)
    (d : (G.deleteEdges {e}).Dart) :
    (R.deleteEdge e a ha).rotation d =
      (R.deleteEdgeVertexPerm e a ha d.fst ⟨d, rfl⟩).1 := rfl

/-- At the first endpoint, the deleted rotation is the first-return
permutation obtained by splicing out `a`. -/
theorem deleteEdgeVertexPerm_apply_fst [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (e : Sym2 V) (a : G.Dart) (ha : a.edge = e)
    (d : OutDart (G.deleteEdges {e}) a.fst) :
    outDartEmbeddingOfLE (G.deleteEdges_le {e}) a.fst
        (R.deleteEdgeVertexPerm e a ha a.fst d) =
      PermRestriction.erasePoint (R.atVertex a.fst) (outDartSelf a)
        (outDartEmbeddingOfLE (G.deleteEdges_le {e}) a.fst d) := by
  classical
  unfold deleteEdgeVertexPerm
  rw [dif_pos rfl]
  rw [Equiv.permCongr_apply]
  rfl

/-- At the second endpoint, the deleted rotation is the first-return
permutation obtained by splicing out `a.symm`. -/
theorem deleteEdgeVertexPerm_apply_snd [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (e : Sym2 V) (a : G.Dart) (ha : a.edge = e)
    (d : OutDart (G.deleteEdges {e}) a.symm.fst) :
    outDartEmbeddingOfLE (G.deleteEdges_le {e}) a.symm.fst
        (R.deleteEdgeVertexPerm e a ha a.symm.fst d) =
      PermRestriction.erasePoint (R.atVertex a.symm.fst) (outDartSelf a.symm)
        (outDartEmbeddingOfLE (G.deleteEdges_le {e}) a.symm.fst d) := by
  rcases a with ⟨⟨u, v⟩, hadj⟩
  classical
  simp only [Dart.symm, Prod.swap] at d ⊢
  have hne : v ≠ u := hadj.ne'
  unfold deleteEdgeVertexPerm
  rw [dif_neg hne, dif_pos rfl]
  simp only [Dart.symm, Prod.swap]
  apply Subtype.ext
  apply Dart.ext
  rfl

/-- Away from both endpoints, deleting the edge merely transports the old
vertex rotation. -/
theorem deleteEdgeVertexPerm_apply_of_ne [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (e : Sym2 V) (a : G.Dart) (ha : a.edge = e)
    (v : V) (hv₁ : v ≠ a.fst) (hv₂ : v ≠ a.snd)
    (d : OutDart (G.deleteEdges {e}) v) :
    outDartEmbeddingOfLE (G.deleteEdges_le {e}) v
        (R.deleteEdgeVertexPerm e a ha v d) =
      R.atVertex v
        (outDartEmbeddingOfLE (G.deleteEdges_le {e}) v d) := by
  classical
  unfold deleteEdgeVertexPerm
  rw [dif_neg hv₁, dif_neg hv₂]
  rw [Equiv.permCongr_apply]
  rfl

/-- Ambient form of the endpoint splice at `a.fst`. -/
theorem deleteEdge_rotation_embedding_of_fst_eq [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj]
    (e : Sym2 V) (a : G.Dart) (ha : a.edge = e)
    (d : (G.deleteEdges {e}).Dart) (hv : d.fst = a.fst) :
    dartEmbeddingOfLE (G.deleteEdges_le {e})
        ((R.deleteEdge e a ha).rotation d) =
      PermRestriction.erasePoint R.rotation a
        (dartEmbeddingOfLE (G.deleteEdges_le {e}) d) := by
  let d' : OutDart (G.deleteEdges {e}) a.fst := ⟨d, hv⟩
  have hglobal : (R.deleteEdge e a ha).rotation d =
      (R.deleteEdgeVertexPerm e a ha a.fst d').1 := by
    exact ofVertexPermutations_rotation_apply_eq
      (R.deleteEdgeVertexPerm e a ha)
      (R.deleteEdgeVertexPerm_isCycleOn e a ha) d a.fst hv
  have hlocal := congrArg Subtype.val
    (R.deleteEdgeVertexPerm_apply_fst e a ha d')
  rw [hglobal]
  simpa only [outDartEmbeddingOfLE_coe,
    erasePoint_atVertex_apply_coe, d'] using hlocal

/-- Ambient form of the endpoint splice at `a.symm.fst`. -/
theorem deleteEdge_rotation_embedding_of_symm_fst_eq [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj]
    (e : Sym2 V) (a : G.Dart) (ha : a.edge = e)
    (d : (G.deleteEdges {e}).Dart) (hv : d.fst = a.symm.fst) :
    dartEmbeddingOfLE (G.deleteEdges_le {e})
        ((R.deleteEdge e a ha).rotation d) =
      PermRestriction.erasePoint R.rotation a.symm
        (dartEmbeddingOfLE (G.deleteEdges_le {e}) d) := by
  let d' : OutDart (G.deleteEdges {e}) a.symm.fst := ⟨d, hv⟩
  have hglobal : (R.deleteEdge e a ha).rotation d =
      (R.deleteEdgeVertexPerm e a ha a.symm.fst d').1 := by
    exact ofVertexPermutations_rotation_apply_eq
      (R.deleteEdgeVertexPerm e a ha)
      (R.deleteEdgeVertexPerm_isCycleOn e a ha) d a.symm.fst hv
  have hlocal := congrArg Subtype.val
    (R.deleteEdgeVertexPerm_apply_snd e a ha d')
  rw [hglobal]
  simpa only [outDartEmbeddingOfLE_coe,
    erasePoint_atVertex_apply_coe, d'] using hlocal

@[simp]
theorem atVertex_apply_coe (v : V) (d : OutDart G v) :
    (R.atVertex v d).1 = R.rotation d.1 := rfl

/-- Ambient form of the unchanged rotation away from the two endpoints. -/
theorem deleteEdge_rotation_embedding_of_ne [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj]
    (e : Sym2 V) (a : G.Dart) (ha : a.edge = e)
    (d : (G.deleteEdges {e}).Dart)
    (hv₁ : d.fst ≠ a.fst) (hv₂ : d.fst ≠ a.snd) :
    dartEmbeddingOfLE (G.deleteEdges_le {e})
        ((R.deleteEdge e a ha).rotation d) =
      R.rotation (dartEmbeddingOfLE (G.deleteEdges_le {e}) d) := by
  let d' : OutDart (G.deleteEdges {e}) d.fst := ⟨d, rfl⟩
  have hglobal : (R.deleteEdge e a ha).rotation d =
      (R.deleteEdgeVertexPerm e a ha d.fst d').1 := by
    exact ofVertexPermutations_rotation_apply_eq
      (R.deleteEdgeVertexPerm e a ha)
      (R.deleteEdgeVertexPerm_isCycleOn e a ha) d d.fst rfl
  have hlocal := congrArg Subtype.val
    (R.deleteEdgeVertexPerm_apply_of_ne e a ha d.fst hv₁ hv₂ d')
  rw [hglobal]
  simpa only [outDartEmbeddingOfLE_coe, atVertex_apply_coe, d'] using hlocal

/-- The facial permutation after deleting a two-sided edge is the
cross-splice of the two old face cycles, restricted to the surviving darts. -/
theorem deleteEdge_faceStep_embedding [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj]
    (e : Sym2 V) (a : G.Dart) (ha : a.edge = e)
    (htwo : R.IsTwoSidedDart a)
    (d : (G.deleteEdges {e}).Dart) :
    dartEmbeddingOfLE (G.deleteEdges_le {e})
        ((R.deleteEdge e a ha).faceStep d) =
      PermRestriction.crossErase R.faceStep a a.symm
        (dartEmbeddingOfLE (G.deleteEdges_le {e}) d) := by
  let x : G.Dart := dartEmbeddingOfLE (G.deleteEdges_le {e}) d
  have hx : x ≠ a ∧ x ≠ a.symm :=
    (dartDeleteEdgeEquiv e a ha d).2
  have hab : ¬R.faceStep.SameCycle a a.symm :=
    (R.isTwoSidedDart_iff_not_sameCycle a).mp htwo
  have hfix : ∀ y, R.faceStep y ≠ y := R.faceStep_ne_self
  have hxsymm_a : x.symm ≠ a := by
    intro h
    apply hx.2
    calc
      x = x.symm.symm := (Dart.symm_symm x).symm
      _ = a.symm := congrArg Dart.symm h
  have hxsymm_asymm : x.symm ≠ a.symm := by
    intro h
    apply hx.1
    calc
      x = x.symm.symm := (Dart.symm_symm x).symm
      _ = a.symm.symm := congrArg Dart.symm h
      _ = a := Dart.symm_symm a
  change dartEmbeddingOfLE (G.deleteEdges_le {e})
      ((R.deleteEdge e a ha).rotation d.symm) =
    PermRestriction.crossErase R.faceStep a a.symm x
  have hembSymm :
      dartEmbeddingOfLE (G.deleteEdges_le {e}) d.symm = x.symm := by
    rfl
  by_cases hv₁ : x.symm.fst = a.fst
  · have hdv : d.symm.fst = a.fst := by
      rw [← hv₁]
      exact congrArg (fun q : G.Dart ↦ q.fst) hembSymm
    have hnotb : R.faceStep x ≠ a.symm := by
      intro h
      apply a.fst_ne_snd
      calc
        a.fst = x.symm.fst := hv₁.symm
        _ = (R.faceStep x).fst := (R.rotation_fst x.symm).symm
        _ = a.symm.fst := congrArg (fun q : G.Dart ↦ q.fst) h
        _ = a.snd := rfl
    rw [R.deleteEdge_rotation_embedding_of_fst_eq e a ha d.symm hdv,
      hembSymm,
      PermRestriction.erasePoint_apply_of_ne R.rotation a x.symm hxsymm_a,
      PermRestriction.crossErase_apply_of_ne R.faceStep a a.symm x
        hfix hab hx.1 hx.2]
    simp only [faceStep_apply] at hnotb
    simp only [faceStep_apply, Dart.symm_symm, hnotb, ↓reduceIte]
  · by_cases hv₂ : x.symm.fst = a.symm.fst
    · have hdv : d.symm.fst = a.symm.fst := by
        rw [← hv₂]
        exact congrArg (fun q : G.Dart ↦ q.fst) hembSymm
      have hnota : R.faceStep x ≠ a := by
        intro h
        apply a.snd_ne_fst
        calc
          a.snd = a.symm.fst := rfl
          _ = x.symm.fst := hv₂.symm
          _ = (R.faceStep x).fst := (R.rotation_fst x.symm).symm
          _ = a.fst := congrArg (fun q : G.Dart ↦ q.fst) h
      rw [R.deleteEdge_rotation_embedding_of_symm_fst_eq e a ha d.symm hdv,
        hembSymm,
        PermRestriction.erasePoint_apply_of_ne R.rotation a.symm x.symm
          hxsymm_asymm,
        PermRestriction.crossErase_apply_of_ne R.faceStep a a.symm x
          hfix hab hx.1 hx.2]
      simp only [faceStep_apply] at hnota
      simp only [faceStep_apply, hnota, ↓reduceIte]
    · have hdv₁ : d.symm.fst ≠ a.fst := by
        intro h
        apply hv₁
        calc
          x.symm.fst = d.symm.fst :=
            congrArg (fun q : G.Dart ↦ q.fst) hembSymm.symm
          _ = a.fst := h
      have hdv₂ : d.symm.fst ≠ a.snd := by
        intro h
        apply hv₂
        calc
          x.symm.fst = d.symm.fst :=
            congrArg (fun q : G.Dart ↦ q.fst) hembSymm.symm
          _ = a.snd := h
          _ = a.symm.fst := rfl
      have hnota : R.faceStep x ≠ a := by
        intro h
        apply hv₁
        calc
          x.symm.fst = (R.faceStep x).fst :=
            (R.rotation_fst x.symm).symm
          _ = a.fst := congrArg (fun q : G.Dart ↦ q.fst) h
      have hnotb : R.faceStep x ≠ a.symm := by
        intro h
        apply hv₂
        calc
          x.symm.fst = (R.faceStep x).fst :=
            (R.rotation_fst x.symm).symm
          _ = a.symm.fst := congrArg (fun q : G.Dart ↦ q.fst) h
      rw [R.deleteEdge_rotation_embedding_of_ne e a ha d.symm hdv₁ hdv₂,
        hembSymm,
        PermRestriction.crossErase_apply_of_ne R.faceStep a a.symm x
          hfix hab hx.1 hx.2]
      simp only [faceStep_apply] at hnota hnotb
      simp only [faceStep_apply, hnota, hnotb, ↓reduceIte]

/-- Conjugating the deleted facial permutation by the explicit dart
equivalence gives exactly the surviving-point `crossErase` restriction. -/
theorem deleteEdge_faceStep_permCongr [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj]
    (e : Sym2 V) (a : G.Dart) (ha : a.edge = e)
    (htwo : R.IsTwoSidedDart a) :
    (dartDeleteEdgeEquiv e a ha).permCongr
        (R.deleteEdge e a ha).faceStep =
      PermRestriction.crossEraseRestrict R.faceStep a a.symm
        ((R.isTwoSidedDart_iff_not_sameCycle a).mp htwo) := by
  apply Equiv.ext
  intro x
  apply Subtype.ext
  rw [Equiv.permCongr_apply,
    PermRestriction.crossEraseRestrict_apply_coe]
  change dartEmbeddingOfLE (G.deleteEdges_le {e})
      ((R.deleteEdge e a ha).faceStep
        ((dartDeleteEdgeEquiv e a ha).symm x)) = _
  rw [R.deleteEdge_faceStep_embedding e a ha htwo]
  rw [dartDeleteEdgeEquiv_symm_coe]

/-- Deleting a two-sided edge merges its two incident facial cycles and hence
lowers the face count by exactly one. -/
theorem deleteEdge_faceCount_add_one_of_isTwoSidedDart [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj]
    (e : Sym2 V) (a : G.Dart) (ha : a.edge = e)
    (htwo : R.IsTwoSidedDart a) :
    (R.deleteEdge e a ha).faceCount + 1 = R.faceCount := by
  let E := dartDeleteEdgeEquiv e a ha
  have hab : ¬R.faceStep.SameCycle a a.symm :=
    (R.isTwoSidedDart_iff_not_sameCycle a).mp htwo
  change (R.deleteEdge e a ha).faceStep.cycleFactorsFinset.card + 1 =
    R.faceStep.cycleFactorsFinset.card
  rw [← PermRestriction.card_cycleFactorsFinset_permCongr E
    (R.deleteEdge e a ha).faceStep]
  rw [R.deleteEdge_faceStep_permCongr e a ha htwo]
  exact PermRestriction.card_cycleFactorsFinset_crossEraseRestrict_add_one
    R.faceStep a a.symm R.faceStep_ne_self hab

/-- The explicit deletion rotation remains spherical whenever the deleted
edge is two-sided. -/
theorem deleteEdge_isSpherical_of_isTwoSidedDart [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj]
    (e : Sym2 V) (a : G.Dart) (ha : a.edge = e)
    (hR : R.IsSpherical) (htwo : R.IsTwoSidedDart a) :
    (R.deleteEdge e a ha).IsSpherical :=
  R.deleteEdge_isSpherical_of_faceCount_add_one e a ha hR
    (R.deleteEdge_faceCount_add_one_of_isTwoSidedDart e a ha htwo)

end RotationSystem

end

end LeanCo.PackingEdgeColoring
