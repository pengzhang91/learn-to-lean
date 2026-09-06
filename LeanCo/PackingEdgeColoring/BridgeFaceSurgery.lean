import LeanCo.PackingEdgeColoring.FaceSurgery
import LeanCo.PackingEdgeColoring.FaceBoundaryGirth

/-!
# Bridge edges and facial surgery

This file supplies the graph-theoretic half of edge-deletion heredity.  Its
first result is independent of Euler counting: every bridge is incident with
the same facial orbit on both orientations in every rotation system.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open SimpleGraph

noncomputable section

variable {V : Type*} {G : SimpleGraph V}

namespace PermRestriction

variable {α : Type*}

/-- Removing the head from the cycle represented by a nodup list leaves the
cycle represented by its tail (with the removed head fixed). -/
theorem erasePoint_formPerm_cons [DecidableEq α]
    (a : α) (l : List α) (h : (a :: l).Nodup) :
    erasePoint (List.formPerm (a :: l)) a = List.formPerm l := by
  cases l with
  | nil =>
      apply Equiv.ext
      intro x
      simp [erasePoint, Equiv.Perm.mul_apply]
  | cons b l =>
      have ha : a ∉ b :: l := (List.nodup_cons.mp h).1
      rw [List.formPerm_cons_cons]
      simp [erasePoint, Equiv.Perm.mul_apply,
        List.formPerm_apply_of_notMem ha]

/-- Permutations formed from disjoint lists have disjoint support.  This also
covers empty and singleton lists, where `formPerm` is the identity. -/
theorem formPerm_disjoint_of_list_disjoint [DecidableEq α]
    {l k : List α} (h : l.Disjoint k) :
    Equiv.Perm.Disjoint l.formPerm k.formPerm := by
  intro x
  by_cases hx : x ∈ l
  · right
    exact List.formPerm_apply_of_notMem (List.disjoint_left.mp h hx)
  · left
    exact List.formPerm_apply_of_notMem hx

/-- Cutting a cyclic list at the distinguished entries `a` and `b`, then
cross-splicing and deleting those entries, leaves precisely the two open
arcs as disjoint cyclic permutations. -/
theorem erasePair_swap_formPerm_split [DecidableEq α]
    (a b : α) (p q : List α)
    (h : ((a :: p) ++ (b :: q)).Nodup) :
    erasePair
        (Equiv.swap a b * List.formPerm ((a :: p) ++ (b :: q))) a b =
      List.formPerm p * List.formPerm q := by
  have hs := List.nodup_append.mp h
  have hA : (a :: p).Nodup := hs.1
  have hB : (b :: q).Nodup := hs.2.1
  have hd : (a :: p).Disjoint (b :: q) := by
    rw [List.disjoint_left]
    intro x hx hx'
    exact hs.2.2 x hx x hx' rfl
  have heq := formPerm_append_of_disjoint a b p q hA hB hd
  have hBa : List.formPerm (b :: q) a = a := by
    apply List.formPerm_apply_of_notMem
    exact List.disjoint_left.mp hd (List.mem_cons_self)
  have hpb : p.Disjoint (b :: q) := by
    rw [List.disjoint_left] at hd ⊢
    intro x hx
    exact hd (List.mem_cons_of_mem a hx)
  have hPB : Equiv.Perm.Disjoint p.formPerm (b :: q).formPerm :=
    formPerm_disjoint_of_list_disjoint hpb
  have hPb : p.formPerm b = b := by
    apply List.formPerm_apply_of_notMem
    intro hb
    exact (List.disjoint_left.mp hpb hb) (List.mem_cons_self)
  have hpq : p.Disjoint q := by
    rw [List.disjoint_left] at hpb ⊢
    intro x hx hxq
    exact hpb hx (List.mem_cons_of_mem b hxq)
  have hPQ : Equiv.Perm.Disjoint p.formPerm q.formPerm :=
    formPerm_disjoint_of_list_disjoint hpq
  rw [heq]
  have hcancel : Equiv.swap a b *
      (Equiv.swap a b * (a :: p).formPerm * (b :: q).formPerm) =
      (a :: p).formPerm * (b :: q).formPerm := by
    calc
      _ = (Equiv.swap a b * Equiv.swap a b) *
          (a :: p).formPerm * (b :: q).formPerm := by
        simp only [mul_assoc]
      _ = _ := by rw [Equiv.swap_mul_self, one_mul]
  rw [hcancel, erasePair,
    erasePoint_mul_of_apply_right_eq_self _ _ a hBa,
    erasePoint_formPerm_cons a p hA]
  rw [hPB.commute.eq]
  rw [erasePoint_mul_of_apply_right_eq_self _ _ b hPb,
    erasePoint_formPerm_cons b q hB]
  exact hPQ.commute.eq.symm

theorem formPerm_split_apply_left_eq_right_iff [DecidableEq α]
    (a b : α) (p q : List α)
    (hn : ((a :: p) ++ (b :: q)).Nodup) :
    List.formPerm ((a :: p) ++ (b :: q)) a = b ↔ p = [] := by
  cases p with
  | nil =>
      have ha : a ∉ b :: q := by simpa using (List.nodup_cons.mp hn).1
      simp only [List.singleton_append, eq_self, iff_true] at ⊢
      rw [List.formPerm_cons_cons, Equiv.Perm.mul_apply,
        List.formPerm_apply_of_notMem ha, Equiv.swap_apply_left]
  | cons x p =>
      have ha : a ∉ x :: (p ++ b :: q) :=
        (List.nodup_cons.mp hn).1
      have hxb : x ≠ b := by
        intro h
        subst x
        simp at hn
      simp only [List.cons_append, List.cons_ne_nil, iff_false] at ⊢
      rw [List.formPerm_cons_cons, Equiv.Perm.mul_apply,
        List.formPerm_apply_of_notMem ha, Equiv.swap_apply_left]
      simpa using hxb

theorem formPerm_split_apply_right_eq_left_iff [DecidableEq α]
    (a b : α) (p q : List α)
    (hn : ((a :: p) ++ (b :: q)).Nodup) :
    List.formPerm ((a :: p) ++ (b :: q)) b = a ↔ q = [] := by
  have hrot : ((a :: p) ++ (b :: q)).IsRotated
      ((b :: q) ++ (a :: p)) := by
    refine ⟨(a :: p).length, ?_⟩
    exact List.rotate_append_length_eq (a :: p) (b :: q)
  have heq : List.formPerm ((a :: p) ++ (b :: q)) =
      List.formPerm ((b :: q) ++ (a :: p)) :=
    List.formPerm_eq_of_isRotated hn hrot
  rw [heq]
  exact formPerm_split_apply_left_eq_right_iff b a q p
    (hrot.nodup_iff.mp hn)

/-- A supported point `b` in the orbit of `a` cuts `f.toList a` into the two
oriented arcs between `a` and `b`. -/
theorem exists_toList_split_of_sameCycle [Fintype α] [DecidableEq α]
    (f : Equiv.Perm α) (a b : α) (hfa : f a ≠ a)
    (hab : a ≠ b) (hsame : f.SameCycle a b) :
    ∃ p q : List α,
      f.toList a = (a :: p) ++ (b :: q) ∧
        ((a :: p) ++ (b :: q)).Nodup := by
  have hsa : a ∈ f.support := Equiv.Perm.mem_support.mpr hfa
  have hbL : b ∈ f.toList a :=
    Equiv.Perm.mem_toList_iff.mpr ⟨hsame, hsa⟩
  have hL0 : f.toList a ≠ [] := by
    exact List.ne_nil_of_length_pos
      (Equiv.Perm.length_toList_pos_of_mem_support f a hsa)
  have hhead : (f.toList a).head hL0 = a := by
    rw [List.head_eq_getElem]
    exact Equiv.Perm.toList_getElem_zero f a hsa
  have hcons : a :: (f.toList a).tail = f.toList a := by
    calc
      a :: (f.toList a).tail =
          (f.toList a).head hL0 :: (f.toList a).tail := by rw [hhead]
      _ = f.toList a := List.cons_head_tail hL0
  have hbTail : b ∈ (f.toList a).tail := by
    rw [← hcons] at hbL
    simpa only [List.mem_cons, hab.symm, false_or] using hbL
  obtain ⟨p, q, htail⟩ := List.mem_iff_append.mp hbTail
  refine ⟨p, q, ?_, ?_⟩
  · rw [← hcons, htail]
    rfl
  · have hn := Equiv.Perm.nodup_toList f a
    rw [← hcons, htail] at hn
    exact hn

/-- Product of all cycle factors except the factor through `a`. -/
def oneCycleRemainder [Fintype α] [DecidableEq α]
    (f : Equiv.Perm α) (a : α) : Equiv.Perm α :=
  f * (f.cycleOf a)⁻¹

theorem cycleFactorsFinset_oneCycleRemainder [Fintype α]
    [DecidableEq α] (f : Equiv.Perm α) (a : α) (hfa : f a ≠ a) :
    (oneCycleRemainder f a).cycleFactorsFinset =
      f.cycleFactorsFinset.erase (f.cycleOf a) := by
  have hc : f.cycleOf a ∈ f.cycleFactorsFinset :=
    Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr
      (Equiv.Perm.mem_support.mpr hfa)
  rw [oneCycleRemainder,
    Equiv.Perm.cycleFactorsFinset_mul_inv_mem_eq_sdiff hc,
    Finset.sdiff_singleton_eq_erase]

theorem cycleOf_mul_oneCycleRemainder [Fintype α] [DecidableEq α]
    (f : Equiv.Perm α) (a : α) (hfa : f a ≠ a) :
    f.cycleOf a * oneCycleRemainder f a = f := by
  have hc : f.cycleOf a ∈ f.cycleFactorsFinset :=
    Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr
      (Equiv.Perm.mem_support.mpr hfa)
  have hcomm : Commute (f.cycleOf a) f :=
    Equiv.Perm.self_mem_cycle_factors_commute hc
  rw [oneCycleRemainder]
  calc
    f.cycleOf a * (f * (f.cycleOf a)⁻¹) =
        (f.cycleOf a * f) * (f.cycleOf a)⁻¹ := by
      rw [mul_assoc]
    _ = (f * f.cycleOf a) * (f.cycleOf a)⁻¹ := by rw [hcomm.eq]
    _ = f := by simp

theorem oneCycleRemainder_apply_of_mem_cycle [Fintype α]
    [DecidableEq α] (f : Equiv.Perm α) (a y : α) (hfa : f a ≠ a)
    (hy : y ∈ (f.cycleOf a).support) : oneCycleRemainder f a y = y := by
  have hc : f.cycleOf a ∈ f.cycleFactorsFinset :=
    Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr
      (Equiv.Perm.mem_support.mpr hfa)
  have hd := Equiv.Perm.disjoint_mul_inv_of_mem_cycleFactorsFinset hc
  rcases hd y with hry | hcy
  · exact hry
  · exact (Equiv.Perm.mem_support.mp hy hcy).elim

/-- The cross-splice on one original cycle is the product of its two open
arcs and the untouched cycle remainder. -/
theorem crossErase_eq_formPerm_split_mul_remainder [Fintype α]
    [DecidableEq α] (f : Equiv.Perm α) (a b : α) (p q : List α)
    (hfa : f a ≠ a) (hab : a ≠ b)
    (hL : f.toList a = (a :: p) ++ (b :: q))
    (hn : ((a :: p) ++ (b :: q)).Nodup) :
    crossErase f a b =
      (p.formPerm * q.formPerm) * oneCycleRemainder f a := by
  have hra : oneCycleRemainder f a a = a := by
    apply oneCycleRemainder_apply_of_mem_cycle f a a hfa
    rw [Equiv.Perm.mem_support_cycleOf_iff]
    exact ⟨Equiv.Perm.SameCycle.refl f a,
      Equiv.Perm.mem_support.mpr hfa⟩
  have hsame : f.SameCycle a b := by
    have hbL : b ∈ f.toList a := by rw [hL]; simp
    exact (Equiv.Perm.mem_toList_iff.mp hbL).1
  have hrb : oneCycleRemainder f a b = b := by
    apply oneCycleRemainder_apply_of_mem_cycle f a b hfa
    rw [Equiv.Perm.mem_support_cycleOf_iff]
    exact ⟨hsame, Equiv.Perm.mem_support.mpr hfa⟩
  have hcform : f.cycleOf a =
      List.formPerm ((a :: p) ++ (b :: q)) := by
    calc
      f.cycleOf a = List.formPerm (f.toList a) :=
        (Equiv.Perm.formPerm_toList f a).symm
      _ = _ := by rw [hL]
  have hfac := cycleOf_mul_oneCycleRemainder f a hfa
  calc
    crossErase f a b = erasePair (Equiv.swap a b * f) a b := rfl
    _ = erasePair
        (Equiv.swap a b *
          (f.cycleOf a * oneCycleRemainder f a)) a b := by
      rw [hfac]
    _ = erasePair
        ((Equiv.swap a b * f.cycleOf a) *
          oneCycleRemainder f a) a b := by
      simp only [mul_assoc]
    _ = erasePair (Equiv.swap a b * f.cycleOf a) a b *
        oneCycleRemainder f a :=
      erasePair_mul_of_apply_right_eq_self _ _ _ _ hra hrb
    _ = (p.formPerm * q.formPerm) * oneCycleRemainder f a := by
      rw [hcform, erasePair_swap_formPerm_split a b p q hn]

/-- A nodup list contributes one nontrivial cycle exactly when it has at
least two entries. -/
theorem card_cycleFactorsFinset_formPerm [Fintype α] [DecidableEq α]
    (l : List α) (hn : l.Nodup) :
    l.formPerm.cycleFactorsFinset.card = if 2 ≤ l.length then 1 else 0 := by
  by_cases hl : 2 ≤ l.length
  · rw [(List.isCycle_formPerm hn hl).cycleFactorsFinset_eq_singleton]
    simp [hl]
  · have hlen : l.length ≤ 1 := by omega
    cases l with
    | nil => simp
    | cons x l =>
        cases l with
        | nil => simp
        | cons y l => simp at hlen

/-- Exact cycle-count formula for cutting two points on one cycle.  Each
surviving arc contributes one cycle precisely when it contains at least two
points; singleton arcs disappear because cycle-factor sets omit fixed
points. -/
theorem card_cycleFactorsFinset_crossErase_sameCycle_split
    [Fintype α] [DecidableEq α]
    (f : Equiv.Perm α) (a b : α) (p q : List α)
    (hfa : f a ≠ a) (hab : a ≠ b)
    (hL : f.toList a = (a :: p) ++ (b :: q))
    (hn : ((a :: p) ++ (b :: q)).Nodup) :
    (crossErase f a b).cycleFactorsFinset.card + 1 =
      f.cycleFactorsFinset.card +
        (if 2 ≤ p.length then 1 else 0) +
        (if 2 ≤ q.length then 1 else 0) := by
  let r := oneCycleRemainder f a
  let m := p.formPerm * q.formPerm
  have hs := List.nodup_append.mp hn
  have hpNodup : p.Nodup := hs.1.of_cons
  have hqNodup : q.Nodup := hs.2.1.of_cons
  have hd : (a :: p).Disjoint (b :: q) := by
    rw [List.disjoint_left]
    intro x hx hx'
    exact hs.2.2 x hx x hx' rfl
  have hpq : p.Disjoint q := by
    rw [List.disjoint_left] at hd ⊢
    intro x hx hxq
    exact hd (List.mem_cons_of_mem a hx) (List.mem_cons_of_mem b hxq)
  have hPQ : Equiv.Perm.Disjoint p.formPerm q.formPerm :=
    formPerm_disjoint_of_list_disjoint hpq
  have hrfix : ∀ y ∈ f.toList a, r y = y := by
    intro y hy
    apply oneCycleRemainder_apply_of_mem_cycle f a y hfa
    rw [Equiv.Perm.mem_support_cycleOf_iff]
    exact Equiv.Perm.mem_toList_iff.mp hy
  have hmr : Equiv.Perm.Disjoint m r := by
    intro y
    by_cases hyp : y ∈ p
    · right
      apply hrfix y
      rw [hL]
      simp [hyp]
    · by_cases hyq : y ∈ q
      · right
        apply hrfix y
        rw [hL]
        simp [hyq]
      · left
        change p.formPerm (q.formPerm y) = y
        rw [List.formPerm_apply_of_notMem hyq,
          List.formPerm_apply_of_notMem hyp]
  have hcross :=
    crossErase_eq_formPerm_split_mul_remainder f a b p q hfa hab hL hn
  have hcrossCard : (crossErase f a b).cycleFactorsFinset.card =
      m.cycleFactorsFinset.card + r.cycleFactorsFinset.card := by
    rw [hcross, hmr.cycleFactorsFinset_mul_eq_union,
      Finset.card_union_of_disjoint hmr.disjoint_cycleFactorsFinset]
  have hmCard : m.cycleFactorsFinset.card =
      p.formPerm.cycleFactorsFinset.card +
        q.formPerm.cycleFactorsFinset.card := by
    change (p.formPerm * q.formPerm).cycleFactorsFinset.card = _
    rw [hPQ.cycleFactorsFinset_mul_eq_union,
      Finset.card_union_of_disjoint hPQ.disjoint_cycleFactorsFinset]
  have hc : f.cycleOf a ∈ f.cycleFactorsFinset :=
    Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr
      (Equiv.Perm.mem_support.mpr hfa)
  have hrCard : r.cycleFactorsFinset.card + 1 =
      f.cycleFactorsFinset.card := by
    change (oneCycleRemainder f a).cycleFactorsFinset.card + 1 = _
    rw [cycleFactorsFinset_oneCycleRemainder f a hfa]
    exact Finset.card_erase_add_one hc
  rw [hcrossCard, hmCard,
    card_cycleFactorsFinset_formPerm p hpNodup,
    card_cycleFactorsFinset_formPerm q hqNodup]
  omega

/-- If the surviving cross-splice is fixed-point-free, neither open arc can
have exactly one entry: a singleton arc would become a fixed point. -/
theorem split_lengths_ne_one_of_crossEraseRestrictDistinct_fixedPointFree
    [Fintype α] [DecidableEq α]
    (f : Equiv.Perm α) (a b : α) (p q : List α)
    (hfa : f a ≠ a) (hab : a ≠ b)
    (hL : f.toList a = (a :: p) ++ (b :: q))
    (hn : ((a :: p) ++ (b :: q)).Nodup)
    (hres : ∀ x, x ≠ a → x ≠ b → crossErase f a b x ≠ x) :
    p.length ≠ 1 ∧ q.length ≠ 1 := by
  have hcross :=
    crossErase_eq_formPerm_split_mul_remainder f a b p q hfa hab hL hn
  have hrfix : ∀ y ∈ f.toList a, oneCycleRemainder f a y = y := by
    intro y hy
    apply oneCycleRemainder_apply_of_mem_cycle f a y hfa
    rw [Equiv.Perm.mem_support_cycleOf_iff]
    exact Equiv.Perm.mem_toList_iff.mp hy
  have hs := List.nodup_append.mp hn
  have hd : (a :: p).Disjoint (b :: q) := by
    rw [List.disjoint_left]
    intro x hx hx'
    exact hs.2.2 x hx x hx' rfl
  have hpq : p.Disjoint q := by
    rw [List.disjoint_left] at hd ⊢
    intro x hx hxq
    exact hd (List.mem_cons_of_mem a hx) (List.mem_cons_of_mem b hxq)
  constructor
  · intro hpLen
    obtain ⟨x, hp⟩ := List.length_eq_one_iff.mp hpLen
    subst p
    have hn' : (a :: x :: b :: q).Nodup := by
      simpa only [List.cons_append, List.nil_append] using hn
    have hxa : x ≠ a := by
      intro h
      subst x
      exact (List.nodup_cons.mp hn').1 (List.mem_cons_self)
    have hxrest : x ∉ b :: q :=
      (List.nodup_cons.mp (List.nodup_cons.mp hn').2).1
    have hxb : x ≠ b := by
      intro h
      exact hxrest (by simp [h])
    have hxq : x ∉ q := by
      intro hx
      exact hxrest (List.mem_cons_of_mem b hx)
    have hxL : x ∈ f.toList a := by
      rw [hL]
      simp
    have hrx := hrfix x hxL
    have hcrossx : crossErase f a b x = x := by
      have heval := congrArg (fun σ : Equiv.Perm α ↦ σ x) hcross
      simpa [Equiv.Perm.mul_apply,
        List.formPerm_apply_of_notMem hxq, hrx] using heval
    exact hres x hxa hxb hcrossx
  · intro hqLen
    obtain ⟨x, hq⟩ := List.length_eq_one_iff.mp hqLen
    subst q
    have hn' : ((a :: p) ++ [b, x]).Nodup := by
      simpa only [List.cons_append, List.nil_append] using hn
    have hxb : x ≠ b := by
      have ht := (List.nodup_append.mp hn').2.1
      have hbx : b ≠ x := by
        intro h
        subst x
        exact (List.nodup_cons.mp ht).1 (List.mem_cons_self)
      exact hbx.symm
    have hxa : x ≠ a := by
      intro h
      subst x
      have hdis := (List.nodup_append.mp hn').2.2
      exact hdis a (List.mem_cons_self) a (by simp) rfl
    have hxp : x ∉ p := by
      intro hx
      have hdis := (List.nodup_append.mp hn').2.2
      exact hdis x (List.mem_cons_of_mem a hx) x (by simp) rfl
    have hxL : x ∈ f.toList a := by
      rw [hL]
      simp
    have hrx := hrfix x hxL
    have hcrossx : crossErase f a b x = x := by
      have heval := congrArg (fun σ : Equiv.Perm α ↦ σ x) hcross
      simpa [Equiv.Perm.mul_apply,
        List.formPerm_apply_of_notMem hxp, hrx] using heval
    exact hres x hxa hxb hcrossx

/-- On a derangement, cross-splicing two distinct points has the usual
predecessor-bypass description even when the two points lie on one cycle. -/
theorem crossErase_apply_of_distinct [DecidableEq α]
    (f : Equiv.Perm α) (a b x : α) (hfix : ∀ y, f y ≠ y)
    (hab : a ≠ b) (hxa : x ≠ a) (hxb : x ≠ b) :
    crossErase f a b x =
      if f x = a then f b else if f x = b then f a else f x := by
  let m : Equiv.Perm α := Equiv.swap a b * f
  let g : Equiv.Perm α := erasePoint m a
  change erasePoint g b x = _
  by_cases hfxa : f x = a
  · rw [if_pos hfxa]
    have hfba : f b ≠ a := by
      intro h
      exact hxb (f.injective (hfxa.trans h.symm))
    have hmb : m b = f b := by
      change Equiv.swap a b (f b) = f b
      exact Equiv.swap_apply_of_ne_of_ne hfba (hfix b)
    have hmx : m x = b := by
      change Equiv.swap a b (f x) = b
      rw [hfxa, Equiv.swap_apply_left]
    have hgx : g x = b := by
      rw [show g x = erasePoint m a x by rfl,
        erasePoint_apply_of_ne m a x hxa, hmx]
      exact if_neg hab.symm
    have hgb : g b = f b := by
      rw [show g b = erasePoint m a b by rfl,
        erasePoint_apply_of_ne m a b hab.symm, hmb,
        if_neg hfba]
    rw [erasePoint_apply_of_ne g b x hxb, hgx, if_pos rfl, hgb]
  · rw [if_neg hfxa]
    by_cases hfxb : f x = b
    · rw [if_pos hfxb]
      have hfab : f a ≠ b := by
        intro h
        exact hxa (f.injective (hfxb.trans h.symm))
      have hma : m a = f a := by
        change Equiv.swap a b (f a) = f a
        exact Equiv.swap_apply_of_ne_of_ne (hfix a) hfab
      have hmx : m x = a := by
        change Equiv.swap a b (f x) = a
        rw [hfxb, Equiv.swap_apply_right]
      have hgx : g x = f a := by
        rw [show g x = erasePoint m a x by rfl,
          erasePoint_apply_of_ne m a x hxa, hmx, if_pos rfl, hma]
      rw [erasePoint_apply_of_ne g b x hxb, hgx, if_neg hfab]
    · rw [if_neg hfxb]
      have hmx : m x = f x := by
        change Equiv.swap a b (f x) = f x
        exact Equiv.swap_apply_of_ne_of_ne hfxa hfxb
      have hgx : g x = f x := by
        rw [show g x = erasePoint m a x by rfl,
          erasePoint_apply_of_ne m a x hxa, hmx, if_neg hfxa]
      rw [erasePoint_apply_of_ne g b x hxb, hgx, if_neg hfxb]

theorem crossErase_apply_left_of_distinct [DecidableEq α]
    (f : Equiv.Perm α) (a b : α) (hab : a ≠ b) :
    crossErase f a b a = a := by
  let g := erasePoint (Equiv.swap a b * f) a
  have hga : g a = a := erasePoint_apply_self _ _
  rw [show crossErase f a b = erasePoint g b by rfl,
    erasePoint_apply_of_ne g b a hab]
  simp only [hga, if_neg hab]

theorem crossErase_apply_right_of_distinct [DecidableEq α]
    (f : Equiv.Perm α) (a b : α) (hab : a ≠ b) :
    crossErase f a b b = b := by
  exact erasePoint_apply_self _ _

theorem crossErase_apply_ne_left_iff_of_distinct [DecidableEq α]
    (f : Equiv.Perm α) (a b x : α) (hab : a ≠ b) :
    crossErase f a b x ≠ a ↔ x ≠ a := by
  constructor
  · intro h hxa
    subst x
    exact h (crossErase_apply_left_of_distinct f a b hab)
  · intro h hcross
    apply h
    apply (crossErase f a b).injective
    simpa only [crossErase_apply_left_of_distinct f a b hab] using hcross

theorem crossErase_apply_ne_right_iff_of_distinct [DecidableEq α]
    (f : Equiv.Perm α) (a b x : α) (hab : a ≠ b) :
    crossErase f a b x ≠ b ↔ x ≠ b := by
  constructor
  · intro h hxb
    subst x
    exact h (crossErase_apply_right_of_distinct f a b hab)
  · intro h hcross
    apply h
    apply (crossErase f a b).injective
    simpa only [crossErase_apply_right_of_distinct f a b hab] using hcross

/-- Restriction of `crossErase` to two distinct surviving points, without a
cycle-separation hypothesis. -/
def crossEraseRestrictDistinct [DecidableEq α]
    (f : Equiv.Perm α) (a b : α) (hab : a ≠ b) :
    Equiv.Perm {x : α // x ≠ a ∧ x ≠ b} :=
  (crossErase f a b).subtypePerm fun x ↦ by
    rw [crossErase_apply_ne_left_iff_of_distinct f a b x hab,
      crossErase_apply_ne_right_iff_of_distinct f a b x hab]

@[simp]
theorem crossEraseRestrictDistinct_apply_coe [DecidableEq α]
    (f : Equiv.Perm α) (a b : α) (hab : a ≠ b)
    (x : {x : α // x ≠ a ∧ x ≠ b}) :
    (crossEraseRestrictDistinct f a b hab x : α) = crossErase f a b x := rfl

/-- Extending the distinct-point restriction by the identity recovers the
ambient cross-splice.  Additional fixed points among survivors are harmless. -/
theorem ofSubtype_crossEraseRestrictDistinct [Fintype α] [DecidableEq α]
    (f : Equiv.Perm α) (a b : α) (hab : a ≠ b) :
    Equiv.Perm.ofSubtype (crossEraseRestrictDistinct f a b hab) =
      crossErase f a b := by
  exact Equiv.Perm.ofSubtype_subtypePerm
    (fun x ↦ by
      rw [crossErase_apply_ne_left_iff_of_distinct f a b x hab,
        crossErase_apply_ne_right_iff_of_distinct f a b x hab])
    (fun x hx ↦ ⟨
      fun hxa ↦ by
        subst x
        exact hx (crossErase_apply_left_of_distinct f a b hab),
      fun hxb ↦ by
        subst x
        exact hx (crossErase_apply_right_of_distinct f a b hab)⟩)

/-- Restricting a cross-splice at two distinct fixed points preserves its
nontrivial cycle count. -/
theorem card_cycleFactorsFinset_crossEraseRestrictDistinct [Fintype α]
    [DecidableEq α] (f : Equiv.Perm α) (a b : α) (hab : a ≠ b) :
    (crossEraseRestrictDistinct f a b hab).cycleFactorsFinset.card =
      (crossErase f a b).cycleFactorsFinset.card := by
  rw [card_cycleFactorsFinset_eq_card_cycleType,
    card_cycleFactorsFinset_eq_card_cycleType]
  rw [← Equiv.Perm.cycleType_ofSubtype,
    ofSubtype_crossEraseRestrictDistinct f a b hab]

end PermRestriction

namespace RotationSystem

variable (R : RotationSystem G)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The facial permutation after deleting an arbitrary edge is the
cross-splice of the two deleted darts, restricted to the surviving darts.
Unlike the earlier two-sided version, this statement also covers a bridge,
whose two orientations lie in one face cycle. -/
theorem deleteEdge_faceStep_embedding_general
    (e : Sym2 V) (a : G.Dart) (ha : a.edge = e)
    (d : (G.deleteEdges {e}).Dart) :
    dartEmbeddingOfLE (G.deleteEdges_le {e})
        ((R.deleteEdge e a ha).faceStep d) =
      PermRestriction.crossErase R.faceStep a a.symm
        (dartEmbeddingOfLE (G.deleteEdges_le {e}) d) := by
  let x : G.Dart := dartEmbeddingOfLE (G.deleteEdges_le {e}) d
  have hx : x ≠ a ∧ x ≠ a.symm :=
    (dartDeleteEdgeEquiv e a ha d).2
  have hab : a ≠ a.symm := by
    intro h
    exact a.fst_ne_snd (congrArg (fun d : G.Dart ↦ d.fst) h)
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
      PermRestriction.crossErase_apply_of_distinct R.faceStep a a.symm x
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
        PermRestriction.crossErase_apply_of_distinct R.faceStep a a.symm x
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
        PermRestriction.crossErase_apply_of_distinct R.faceStep a a.symm x
          hfix hab hx.1 hx.2]
      simp only [faceStep_apply] at hnota hnotb
      simp only [faceStep_apply, hnota, hnotb, ↓reduceIte]

/-- Conjugating the deleted facial permutation by the dart-deletion
equivalence gives the unrestricted surviving-point cross-splice. -/
theorem deleteEdge_faceStep_permCongr_general
    (e : Sym2 V) (a : G.Dart) (ha : a.edge = e) :
    (dartDeleteEdgeEquiv e a ha).permCongr
        (R.deleteEdge e a ha).faceStep =
      PermRestriction.crossEraseRestrictDistinct R.faceStep a a.symm
        (by
          intro h
          exact a.fst_ne_snd (congrArg (fun d : G.Dart ↦ d.fst) h)) := by
  apply Equiv.ext
  intro x
  apply Subtype.ext
  rw [Equiv.permCongr_apply,
    PermRestriction.crossEraseRestrictDistinct_apply_coe]
  change dartEmbeddingOfLE (G.deleteEdges_le {e})
      ((R.deleteEdge e a ha).faceStep
        ((dartDeleteEdgeEquiv e a ha).symm x)) = _
  rw [R.deleteEdge_faceStep_embedding_general e a ha]
  rw [dartDeleteEdgeEquiv_symm_coe]

/-- The complete boundary listing of a face contains each oriented dart only
once. -/
theorem faceBoundaryWalk_darts_nodup (f : R.Face)
    (a : {a : G.Dart // a ∈ f.1.support}) :
    (R.faceBoundaryWalk f a (R.faceLength f)).darts.Nodup := by
  rw [R.faceBoundaryWalk_darts]
  rw [List.nodup_ofFn]
  intro i j hij
  apply Fin.ext
  exact R.faceDartAt_injective_before_length f a i.isLt j.isLt hij

/-- A bridge is traversed in both directions by one facial boundary, for any
rotation system. -/
theorem sameCycle_faceStep_of_isBridge (a : G.Dart)
    (hbridge : G.IsBridge a.edge) :
    R.faceStep.SameCycle a a.symm := by
  by_contra hsame
  let f : R.Face := R.faceOfDart a
  let aa : {d : G.Dart // d ∈ f.1.support} :=
    ⟨a, R.mem_support_faceOfDart a⟩
  let n := R.faceLength f
  have hn : 2 ≤ n := R.two_le_faceLength f
  let p₀ := R.faceBoundaryWalk f aa n
  have hstart : R.faceVertexAt f aa 0 = a.fst := by
    rw [R.faceVertexAt_eq_faceDartAt_fst, R.faceDartAt_zero]
  have hend : R.faceVertexAt f aa n = a.fst := by
    dsimp [n]
    change (R.faceDartAt f aa (R.faceLength f)).fst = a.fst
    rw [R.faceDartAt_faceLength]
  let p : G.Walk a.fst a.fst := p₀.copy hstart hend
  have hpLen : p.length = n := by
    simp only [p, p₀, Walk.length_copy, R.faceBoundaryWalk_length]
  have hpNotNil : ¬p.Nil := by
    rw [Walk.not_nil_iff_lt_length, hpLen]
    omega
  have hpSnd : p.snd = a.snd := by
    change p.getVert 1 = a.snd
    rw [show p.getVert 1 = p₀.getVert 1 by simp [p]]
    rw [R.faceBoundaryWalk_getVert f aa n 1 (by omega)]
    rw [R.faceVertexAt_eq_faceDartAt_fst,
      show (1 : ℕ) = 0 + 1 by omega,
      R.faceDartAt_succ_fst, R.faceDartAt_zero]
  let q : G.Walk a.snd a.fst := p.tail.copy hpSnd rfl
  have hqDarts : q.darts = p.darts.drop 1 := by
    simp only [q, Walk.darts_copy, Walk.tail, Walk.darts_drop]
  have hpDarts : p.darts =
      List.ofFn (fun i : Fin n ↦ R.faceDartAt f aa i) := by
    simp only [p, p₀, Walk.darts_copy, R.faceBoundaryWalk_darts]
  have hpNodup : p.darts.Nodup := by
    simpa only [p, p₀, Walk.darts_copy] using
      R.faceBoundaryWalk_darts_nodup f aa
  have hpHead : p.darts.head? = some a := by
    rw [hpDarts]
    have hn0 : n ≠ 0 := by omega
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    rw [hm, List.ofFn_succ]
    simp only [List.head?_cons]
    rfl
  have ha_not_tail : a ∉ p.darts.drop 1 := by
    have hcons : ∃ l, p.darts = a :: l := by
      cases hd : p.darts with
      | nil => simp [hd] at hpHead
      | cons d l =>
          have hda : d = a := by simpa [hd] using hpHead
          exact ⟨l, by simp [hd, hda]⟩
    obtain ⟨l, hl⟩ := hcons
    rw [hl] at hpNodup ⊢
    simpa using (List.nodup_cons.mp hpNodup).1
  have hasymm_not_mem : a.symm ∉ p.darts := by
    intro hamem
    rw [hpDarts, List.mem_ofFn] at hamem
    obtain ⟨i, hi⟩ := hamem
    have hmem : a.symm ∈ f.1.support := by
      rw [← hi]
      exact R.faceDartAt_mem_support f aa i
    have hface : R.faceOfDart a.symm = f := by
      apply Subtype.ext
      exact (Equiv.Perm.eq_cycleOf_of_mem_cycleFactorsFinset_iff
        R.faceStep f.1 f.2 a.symm).mpr hmem |>.symm
    have haa : R.faceOfDart a = f := rfl
    apply hsame
    exact (R.faceOfDart_eq_iff_sameCycle a a.symm).mp
      (haa.trans hface.symm)
  have hqAvoid : a.edge ∉ q.edges := by
    rw [Walk.edges]
    intro he
    rw [List.mem_map] at he
    obtain ⟨d, hdq, hedge⟩ := he
    have hdp : d ∈ p.darts := by
      rw [hqDarts] at hdq
      exact List.mem_of_mem_drop hdq
    rcases (dart_edge_eq_iff d a).mp hedge with hda | hda
    · subst d
      rw [hqDarts] at hdq
      exact ha_not_tail hdq
    · subst d
      exact hasymm_not_mem hdp
  have hmust : a.edge ∈ q.edges := by
    have hb : G.IsBridge s(a.snd, a.fst) := by
      simpa only [Dart.edge, Sym2.eq_swap] using hbridge
    have hm := (G.isBridge_iff_forall_walk_mem_edges.mp hb) q
    have hedge : s(a.snd, a.fst) = a.edge := by
      rw [Dart.edge, Sym2.eq_swap]
    exact hedge ▸ hm
  exact hqAvoid hmust

theorem not_isTwoSidedDart_of_isBridge (a : G.Dart)
    (hbridge : G.IsBridge a.edge) : ¬R.IsTwoSidedDart a := by
  intro htwo
  exact (R.isTwoSidedDart_iff_not_sameCycle a).mp htwo
    (R.sameCycle_faceStep_of_isBridge a hbridge)

/-- On surviving darts, the ambient cross-splice has no fixed point because
it is conjugate to the facial permutation of the deleted graph. -/
theorem crossErase_ne_self_of_deleteEdge
    (e : Sym2 V) (a : G.Dart) (ha : a.edge = e)
    (x : G.Dart) (hxa : x ≠ a) (hxb : x ≠ a.symm) :
    PermRestriction.crossErase R.faceStep a a.symm x ≠ x := by
  have hab : a ≠ a.symm := by
    intro h
    exact a.fst_ne_snd (congrArg (fun d : G.Dart ↦ d.fst) h)
  let E := dartDeleteEdgeEquiv e a ha
  let z : {y : G.Dart // y ≠ a ∧ y ≠ a.symm} := ⟨x, hxa, hxb⟩
  have hperm := R.deleteEdge_faceStep_permCongr_general e a ha
  have hres :
      PermRestriction.crossEraseRestrictDistinct
        R.faceStep a a.symm hab z ≠ z := by
    rw [← hperm]
    intro hz
    apply (R.deleteEdge e a ha).faceStep_ne_self (E.symm z)
    apply E.injective
    simpa only [Equiv.permCongr_apply, Equiv.apply_symm_apply] using hz
  intro hx
  apply hres
  apply Subtype.ext
  exact hx

/-- Complete face-cycle bookkeeping for deleting two darts on one old face.
The returned lists are the two open facial arcs. -/
theorem exists_deleteEdge_faceSplit_of_sameCycle
    (e : Sym2 V) (a : G.Dart) (ha : a.edge = e)
    (hsame : R.faceStep.SameCycle a a.symm) :
    ∃ p q : List G.Dart,
      R.faceStep.toList a = (a :: p) ++ (a.symm :: q) ∧
      ((a :: p) ++ (a.symm :: q)).Nodup ∧
      p.length ≠ 1 ∧ q.length ≠ 1 ∧
      ((R.deleteEdge e a ha).faceCount + 1 =
        R.faceCount + (if 2 ≤ p.length then 1 else 0) +
          (if 2 ≤ q.length then 1 else 0)) ∧
      (R.faceStep a = a.symm ↔ p = []) ∧
      (R.faceStep a.symm = a ↔ q = []) := by
  have hab : a ≠ a.symm := by
    intro h
    exact a.fst_ne_snd (congrArg (fun d : G.Dart ↦ d.fst) h)
  obtain ⟨p, q, hL, hn⟩ :=
    PermRestriction.exists_toList_split_of_sameCycle
      R.faceStep a a.symm (R.faceStep_ne_self a) hab hsame
  have hlens :=
    PermRestriction.split_lengths_ne_one_of_crossEraseRestrictDistinct_fixedPointFree
      R.faceStep a a.symm p q (R.faceStep_ne_self a) hab hL hn
      (fun x hxa hxb ↦ R.crossErase_ne_self_of_deleteEdge e a ha x hxa hxb)
  have hcycles :=
    PermRestriction.card_cycleFactorsFinset_crossErase_sameCycle_split
      R.faceStep a a.symm p q (R.faceStep_ne_self a) hab hL hn
  have hface : (R.deleteEdge e a ha).faceCount + 1 =
      R.faceCount + (if 2 ≤ p.length then 1 else 0) +
        (if 2 ≤ q.length then 1 else 0) := by
    let E := dartDeleteEdgeEquiv e a ha
    change (R.deleteEdge e a ha).faceStep.cycleFactorsFinset.card + 1 =
      R.faceStep.cycleFactorsFinset.card + _ + _
    rw [← PermRestriction.card_cycleFactorsFinset_permCongr E
      (R.deleteEdge e a ha).faceStep]
    rw [R.deleteEdge_faceStep_permCongr_general e a ha]
    rw [PermRestriction.card_cycleFactorsFinset_crossEraseRestrictDistinct]
    exact hcycles
  have hcform : R.faceStep.cycleOf a =
      List.formPerm ((a :: p) ++ (a.symm :: q)) := by
    calc
      R.faceStep.cycleOf a = List.formPerm (R.faceStep.toList a) :=
        (Equiv.Perm.formPerm_toList R.faceStep a).symm
      _ = _ := by rw [hL]
  have hpEmpty : R.faceStep a = a.symm ↔ p = [] := by
    calc
      R.faceStep a = a.symm ↔ R.faceStep.cycleOf a a = a.symm := by
        rw [Equiv.Perm.cycleOf_apply_self]
      _ ↔ List.formPerm ((a :: p) ++ (a.symm :: q)) a = a.symm := by
        rw [hcform]
      _ ↔ p = [] :=
        PermRestriction.formPerm_split_apply_left_eq_right_iff
          a a.symm p q hn
  have hqEmpty : R.faceStep a.symm = a ↔ q = [] := by
    have hcApply : R.faceStep.cycleOf a a.symm = R.faceStep a.symm :=
      hsame.cycleOf_apply
    calc
      R.faceStep a.symm = a ↔ R.faceStep.cycleOf a a.symm = a := by
        rw [hcApply]
      _ ↔ List.formPerm ((a :: p) ++ (a.symm :: q)) a.symm = a := by
        rw [hcform]
      _ ↔ q = [] :=
        PermRestriction.formPerm_split_apply_right_eq_left_iff
          a a.symm p q hn
  exact ⟨p, q, hL, hn, hlens.1, hlens.2, hface, hpEmpty, hqEmpty⟩

/-- Deleting a one-face edge with a nonempty arc on both sides splits that
face into two, increasing the face count by one. -/
theorem deleteEdge_faceCount_eq_add_one_of_sameCycle
    (e : Sym2 V) (a : G.Dart) (ha : a.edge = e)
    (hsame : R.faceStep.SameCycle a a.symm)
    (hleft : R.faceStep a ≠ a.symm)
    (hright : R.faceStep a.symm ≠ a) :
    (R.deleteEdge e a ha).faceCount = R.faceCount + 1 := by
  obtain ⟨p, q, -, -, hp1, hq1, hface, hp0, hq0⟩ :=
    R.exists_deleteEdge_faceSplit_of_sameCycle e a ha hsame
  have hpLen0 : p.length ≠ 0 := by
    intro h
    exact hleft (hp0.mpr (List.length_eq_zero_iff.mp h))
  have hqLen0 : q.length ≠ 0 := by
    intro h
    exact hright (hq0.mpr (List.length_eq_zero_iff.mp h))
  have hp2 : 2 ≤ p.length := by omega
  have hq2 : 2 ≤ q.length := by omega
  simp only [if_pos hp2, if_pos hq2] at hface
  omega

/-- If exactly one side of a one-face edge has an empty facial arc, deleting
the edge preserves the number of nontrivial face cycles. -/
theorem deleteEdge_faceCount_eq_of_sameCycle_of_left_adjacent
    (e : Sym2 V) (a : G.Dart) (ha : a.edge = e)
    (hsame : R.faceStep.SameCycle a a.symm)
    (hleft : R.faceStep a = a.symm)
    (hright : R.faceStep a.symm ≠ a) :
    (R.deleteEdge e a ha).faceCount = R.faceCount := by
  obtain ⟨p, q, -, -, -, hq1, hface, hp0, hq0⟩ :=
    R.exists_deleteEdge_faceSplit_of_sameCycle e a ha hsame
  have hpNil : p = [] := hp0.mp hleft
  have hqLen0 : q.length ≠ 0 := by
    intro h
    exact hright (hq0.mpr (List.length_eq_zero_iff.mp h))
  have hq2 : 2 ≤ q.length := by omega
  subst p
  simp only [List.length_nil, Nat.reduceLeDiff, if_false, zero_add,
    if_pos hq2] at hface
  omega

theorem deleteEdge_faceCount_eq_of_sameCycle_of_right_adjacent
    (e : Sym2 V) (a : G.Dart) (ha : a.edge = e)
    (hsame : R.faceStep.SameCycle a a.symm)
    (hleft : R.faceStep a ≠ a.symm)
    (hright : R.faceStep a.symm = a) :
    (R.deleteEdge e a ha).faceCount = R.faceCount := by
  obtain ⟨p, q, -, -, hp1, -, hface, hp0, hq0⟩ :=
    R.exists_deleteEdge_faceSplit_of_sameCycle e a ha hsame
  have hqNil : q = [] := hq0.mp hright
  have hpLen0 : p.length ≠ 0 := by
    intro h
    exact hleft (hp0.mpr (List.length_eq_zero_iff.mp h))
  have hp2 : 2 ≤ p.length := by omega
  subst q
  simp only [List.length_nil, Nat.reduceLeDiff, if_false, add_zero,
    if_pos hp2] at hface
  omega

/-- If the old face consists only of the two deleted darts, the unique old
face disappears. -/
theorem deleteEdge_faceCount_add_one_eq_of_sameCycle_of_both_adjacent
    (e : Sym2 V) (a : G.Dart) (ha : a.edge = e)
    (hsame : R.faceStep.SameCycle a a.symm)
    (hleft : R.faceStep a = a.symm)
    (hright : R.faceStep a.symm = a) :
    (R.deleteEdge e a ha).faceCount + 1 = R.faceCount := by
  obtain ⟨p, q, -, -, -, -, hface, hp0, hq0⟩ :=
    R.exists_deleteEdge_faceSplit_of_sameCycle e a ha hsame
  have hpNil : p = [] := hp0.mp hleft
  have hqNil : q = [] := hq0.mp hright
  subst p
  subst q
  simpa using hface

/-- A facial arc immediately returns across the edge exactly when deleting
that edge isolates the terminal endpoint of the dart. -/
theorem faceStep_eq_symm_iff_deleteEdge_isIsolated_snd
    (e : Sym2 V) (a : G.Dart) (ha : a.edge = e) :
    R.faceStep a = a.symm ↔ (G.deleteEdges {e}).IsIsolated a.snd := by
  constructor
  · intro hface w hdw
    have hdw' := SimpleGraph.deleteEdges_adj.mp hdw
    let d : G.Dart := ⟨(a.snd, w), hdw'.1⟩
    have hrot : R.rotation a.symm = a.symm := by
      simpa only [faceStep_apply] using hface
    have hcycle : R.rotation.SameCycle a.symm d := by
      rw [R.rotation_sameCycle_iff_fst_eq]
      rfl
    have hda : a.symm = d := hcycle.eq_of_left hrot
    apply hdw'.2
    simp only [Set.mem_singleton_iff]
    calc
      s(a.snd, w) = d.edge := rfl
      _ = a.symm.edge := congrArg Dart.edge hda.symm
      _ = a.edge := Dart.edge_symm a
      _ = e := ha
  · intro hiso
    let d : G.Dart := R.rotation a.symm
    have hdfst : d.fst = a.snd := by
      exact R.rotation_fst a.symm
    have hdeq : d = a.symm := by
      by_contra hne
      have hdedge : d.edge ≠ e := by
        intro hedge
        have hedge' : d.edge = a.symm.edge := by
          rw [Dart.edge_symm, ha]
          exact hedge
        rcases (dart_edge_eq_iff d a.symm).mp hedge' with h | h
        · exact hne h
        · have hfst := congrArg (fun z : G.Dart ↦ z.fst) h
          exact a.fst_ne_snd (by simpa [hdfst] using hfst)
      have hdel : (G.deleteEdges {e}).Adj d.fst d.snd := by
        rw [SimpleGraph.deleteEdges_adj]
        refine ⟨d.adj, ?_⟩
        simpa only [Dart.edge, Set.mem_singleton_iff] using hdedge
      exact hiso d.snd (hdfst ▸ hdel)
    exact hdeq

theorem faceStep_symm_eq_iff_deleteEdge_isIsolated_fst
    (e : Sym2 V) (a : G.Dart) (ha : a.edge = e) :
    R.faceStep a.symm = a ↔ (G.deleteEdges {e}).IsIsolated a.fst := by
  have ha' : a.symm.edge = e := by simpa only [Dart.edge_symm] using ha
  change R.faceStep a.symm = a.symm.symm ↔
    (G.deleteEdges {e}).IsIsolated a.symm.snd
  exact R.faceStep_eq_symm_iff_deleteEdge_isIsolated_snd e a.symm ha'

theorem deleteEdge_faceCount_eq_add_one_of_isBridge_of_endpoints_nonisolated
    (e : Sym2 V) (a : G.Dart) (ha : a.edge = e)
    (hbridge : G.IsBridge e)
    (hfst : ¬(G.deleteEdges {e}).IsIsolated a.fst)
    (hsnd : ¬(G.deleteEdges {e}).IsIsolated a.snd) :
    (R.deleteEdge e a ha).faceCount = R.faceCount + 1 := by
  apply R.deleteEdge_faceCount_eq_add_one_of_sameCycle e a ha
  · exact R.sameCycle_faceStep_of_isBridge a (ha ▸ hbridge)
  · exact fun h ↦ hsnd
      ((R.faceStep_eq_symm_iff_deleteEdge_isIsolated_snd e a ha).mp h)
  · exact fun h ↦ hfst
      ((R.faceStep_symm_eq_iff_deleteEdge_isIsolated_fst e a ha).mp h)

theorem deleteEdge_faceCount_eq_of_isBridge_of_snd_isolated
    (e : Sym2 V) (a : G.Dart) (ha : a.edge = e)
    (hbridge : G.IsBridge e)
    (hfst : ¬(G.deleteEdges {e}).IsIsolated a.fst)
    (hsnd : (G.deleteEdges {e}).IsIsolated a.snd) :
    (R.deleteEdge e a ha).faceCount = R.faceCount := by
  apply R.deleteEdge_faceCount_eq_of_sameCycle_of_left_adjacent e a ha
  · exact R.sameCycle_faceStep_of_isBridge a (ha ▸ hbridge)
  · exact (R.faceStep_eq_symm_iff_deleteEdge_isIsolated_snd e a ha).mpr hsnd
  · exact fun h ↦ hfst
      ((R.faceStep_symm_eq_iff_deleteEdge_isIsolated_fst e a ha).mp h)

theorem deleteEdge_faceCount_eq_of_isBridge_of_fst_isolated
    (e : Sym2 V) (a : G.Dart) (ha : a.edge = e)
    (hbridge : G.IsBridge e)
    (hfst : (G.deleteEdges {e}).IsIsolated a.fst)
    (hsnd : ¬(G.deleteEdges {e}).IsIsolated a.snd) :
    (R.deleteEdge e a ha).faceCount = R.faceCount := by
  apply R.deleteEdge_faceCount_eq_of_sameCycle_of_right_adjacent e a ha
  · exact R.sameCycle_faceStep_of_isBridge a (ha ▸ hbridge)
  · exact fun h ↦ hsnd
      ((R.faceStep_eq_symm_iff_deleteEdge_isIsolated_snd e a ha).mp h)
  · exact (R.faceStep_symm_eq_iff_deleteEdge_isIsolated_fst e a ha).mpr hfst

theorem deleteEdge_faceCount_add_one_eq_of_isBridge_of_endpoints_isolated
    (e : Sym2 V) (a : G.Dart) (ha : a.edge = e)
    (hbridge : G.IsBridge e)
    (hfst : (G.deleteEdges {e}).IsIsolated a.fst)
    (hsnd : (G.deleteEdges {e}).IsIsolated a.snd) :
    (R.deleteEdge e a ha).faceCount + 1 = R.faceCount := by
  apply R.deleteEdge_faceCount_add_one_eq_of_sameCycle_of_both_adjacent e a ha
  · exact R.sameCycle_faceStep_of_isBridge a (ha ▸ hbridge)
  · exact (R.faceStep_eq_symm_iff_deleteEdge_isIsolated_snd e a ha).mpr hsnd
  · exact (R.faceStep_symm_eq_iff_deleteEdge_isIsolated_fst e a ha).mpr hfst

end Finite

end RotationSystem

end

end LeanCo.PackingEdgeColoring
