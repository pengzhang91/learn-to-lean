import LeanCo.CyclicBraidArrangement.FerrersFactorizationDirect

/-!
# Cyclic deletion and insertion for Ferrers placements

This module supplies the two exact finite equivalences needed by the direct
proof of the Ferrers graphical-Shi product.  The first removes an unselected
largest label while retaining its empty box.  The second removes a selected
largest label together with its box and records the empty successor slot.
-/

namespace CyclicBraidArrangement

namespace DeformationMatrix

variable {n q : ℕ}

/-- An unused box in an anchored Ferrers placement. -/
abbrev FerrersUnusedSlot [NeZero n] [NeZero q]
    (C : Finset (Fin n))
    (p : AnchoredFerrersBoxPlacement (n := n) (q := q) C) :=
  {y : Fin q // y ∉ Set.range p.1}

theorem card_ferrersUnusedSlot [NeZero n] [NeZero q]
    (C : Finset (Fin n))
    (p : AnchoredFerrersBoxPlacement (n := n) (q := q) C) :
    Fintype.card (FerrersUnusedSlot C p) = q - n := by
  rw [Fintype.card_subtype_compl, Fintype.card_range]
  simp

/-- Removing an unselected largest label retains an arbitrary unused box. -/
noncomputable def anchoredFerrersBoxPlacementEquivDropLast_of_not_mem
    [NeZero n] [NeZero q]
    (C : Finset (Fin (n + 1))) (htop : Fin.last n ∉ C) :
    AnchoredFerrersBoxPlacement (n := n + 1) (q := q) C ≃
      Σ p : AnchoredFerrersBoxPlacement (n := n) (q := q)
        (ferrersDropLastColumns C),
          FerrersUnusedSlot (ferrersDropLastColumns C) p := by
  let lowerGood : (Fin n ↪ Fin q) → Prop := fun e ↦
    e 0 = 0 ∧ ∀ c, c ∈ ferrersDropLastColumns C → ∀ b, b < c →
      e b ≠ nextPosition q (e c)
  exact (Equiv.subtypeEquiv (embeddingFinSuccLastEquiv n (Fin q)) (fun e ↦ by
    constructor
    · intro he
      refine ⟨?_, ?_⟩
      · simpa using he.1
      · intro c hc b hbc
        simpa using he.2 c.castSucc (by simpa using hc)
          b.castSucc (by simpa using hbc)
    · intro hz
      refine ⟨?_, ?_⟩
      · change e (0 : Fin (n + 1)) = 0
        rw [show (0 : Fin (n + 1)) = (0 : Fin n).castSucc by rfl]
        simpa using hz.1
      · intro c hc b hbc
        have hcne : c ≠ Fin.last n := by
          intro h
          apply htop
          simpa [h] using hc
        obtain ⟨c₀, rfl⟩ := Fin.exists_castSucc_eq.mpr hcne
        have hbne : b ≠ Fin.last n := by
          intro h
          subst b
          exact (not_lt_of_ge (Fin.le_last _)) hbc
        obtain ⟨b₀, rfl⟩ := Fin.exists_castSucc_eq.mpr hbne
        simpa using hz.2 c₀ (by simpa using hc) b₀ (by simpa using hbc))).trans
    (Equiv.subtypeSigmaEquiv
      (fun e : Fin n ↪ Fin q ↦ {y : Fin q // y ∉ Set.range e}) lowerGood)

/-! ## Removing a selected largest label and its box -/

theorem cyclicInsertPosition_injective {L : ℕ} [NeZero L] :
    Function.Injective (@cyclicInsertPosition L _) := by
  intro a b hab
  by_cases ha : a = 0
  · subst a
    by_cases hb : b = 0
    · exact hb.symm
    · exfalso
      have hval := congrArg Fin.val hab
      simp [cyclicInsertPosition, hb] at hval
      omega
  · by_cases hb : b = 0
    · subst b
      exfalso
      have hval := congrArg Fin.val hab
      simp [cyclicInsertPosition, ha] at hval
      omega
    · apply Fin.castSucc_injective
      simpa [cyclicInsertPosition, ha, hb] using hab

theorem cyclicInsertPosition_surjective_nonzero {L : ℕ} [NeZero L] :
    Function.Surjective
      (fun s : Fin L ↦
        (⟨cyclicInsertPosition s, cyclicInsertPosition_ne_zero s⟩ :
          {r : Fin (L + 1) // r ≠ 0})) := by
  intro r
  by_cases hr : r.1 = Fin.last L
  · refine ⟨0, ?_⟩
    apply Subtype.ext
    simp [cyclicInsertPosition, hr]
  · let s : Fin L := r.1.castPred hr
    have hs : s ≠ 0 := by
      intro h
      apply r.2
      apply Fin.ext
      have hv := congrArg Fin.val h
      simpa [s] using hv
    refine ⟨s, ?_⟩
    apply Subtype.ext
    simp [cyclicInsertPosition, hs, s]

/-- Cyclic insertion slots are exactly the possible nonzero locations of
the new box. -/
noncomputable def cyclicInsertPivotEquiv (L : ℕ) [NeZero L] :
    Fin L ≃ {r : Fin (L + 1) // r ≠ 0} :=
  Equiv.ofBijective
    (fun s : Fin L ↦
      (⟨cyclicInsertPosition s, cyclicInsertPosition_ne_zero s⟩ :
        {r : Fin (L + 1) // r ≠ 0}))
    ⟨fun _ _ h ↦ cyclicInsertPosition_injective
      (congrArg Subtype.val h), cyclicInsertPosition_surjective_nonzero⟩

@[simp] theorem cyclicInsertPivotEquiv_apply_val {L : ℕ} [NeZero L]
    (s : Fin L) :
    (cyclicInsertPivotEquiv L s).1 = cyclicInsertPosition s := rfl

/-- Anchored embeddings, before imposing any Ferrers adjacency condition. -/
def AnchoredBoxEmbedding (n L : ℕ) [NeZero n] [NeZero L] :=
  {e : Fin n ↪ Fin L // e 0 = 0}

/-- The domain on which deleting the last label and its box is reversible:
the last label's cyclic successor is unoccupied by every earlier label. -/
def AnchoredLastSuccessorFree (n L : ℕ) [NeZero n] [NeZero L] :=
  {e : Fin (n + 1) ↪ Fin (L + 1) //
    e 0 = 0 ∧ ∀ b : Fin n,
      e b.castSucc ≠ nextPosition (L + 1) (e (Fin.last n))}

/-- Insert the last label in the cyclic slot recorded by `s`. -/
def anchoredCyclicInsertLast {n L : ℕ} [NeZero n] [NeZero L] :
    (Σ e : AnchoredBoxEmbedding n L,
      {s : Fin L // s ∉ Set.range e.1}) →
      AnchoredLastSuccessorFree n L := fun z ↦ by
  let old : Fin n ↪ Fin (L + 1) :=
    z.1.1.trans (cyclicInsertEmbedding z.2.1)
  have hnew : cyclicInsertPosition z.2.1 ∉ Set.range old := by
    rintro ⟨i, hi⟩
    exact (Fin.succAbove_ne (cyclicInsertPosition z.2.1) (z.1.1 i)) hi
  let raw : Σ e : Fin n ↪ Fin (L + 1),
      {y : Fin (L + 1) // y ∉ Set.range e} :=
    ⟨old, ⟨cyclicInsertPosition z.2.1, hnew⟩⟩
  let e := (embeddingFinSuccLastEquiv n (Fin (L + 1))).symm raw
  refine ⟨e, ?_, ?_⟩
  · change e (0 : Fin (n + 1)) = 0
    rw [show (0 : Fin (n + 1)) = (0 : Fin n).castSucc by rfl,
      embeddingFinSuccLastEquiv_symm_castSucc]
    change cyclicInsertEmbedding z.2.1 (z.1.1 0) = 0
    rw [z.1.2, cyclicInsertEmbedding_zero]
  · intro b hbad
    have hnext : nextPosition (L + 1) (e (Fin.last n)) =
        cyclicInsertEmbedding z.2.1 z.2.1 := by
      rw [embeddingFinSuccLastEquiv_symm_last]
      exact nextPosition_cyclicInsertPosition z.2.1
    rw [embeddingFinSuccLastEquiv_symm_castSucc, hnext] at hbad
    have := (cyclicInsertEmbedding z.2.1).injective hbad
    exact z.2.2 ⟨b, this⟩

theorem anchoredCyclicInsertLast_injective {n L : ℕ}
    [NeZero n] [NeZero L] :
    Function.Injective (@anchoredCyclicInsertLast n L _ _) := by
  intro z w hzw
  have he : (anchoredCyclicInsertLast z).1 =
      (anchoredCyclicInsertLast w).1 := congrArg Subtype.val hzw
  have hlast := congrFun (congrArg DFunLike.coe he) (Fin.last n)
  have hs : z.2.1 = w.2.1 := by
    apply cyclicInsertPosition_injective
    simpa [anchoredCyclicInsertLast] using hlast
  have hfirst : z.1 = w.1 := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro i
    apply (cyclicInsertEmbedding z.2.1).injective
    have hi := congrFun (congrArg DFunLike.coe he) i.castSucc
    simpa [anchoredCyclicInsertLast, hs] using hi
  apply Sigma.ext hfirst
  apply (Subtype.heq_iff_coe_eq (fun x ↦ by
      simpa [hfirst])).2
  exact hs

theorem anchoredCyclicInsertLast_surjective {n L : ℕ}
    [NeZero n] [NeZero L] :
    Function.Surjective (@anchoredCyclicInsertLast n L _ _) := by
  intro p
  have hlast0 : p.1 (Fin.last n) ≠ 0 := by
    intro h
    have hsame : p.1 (Fin.last n) = p.1 (0 : Fin (n + 1)) := by
      simpa [p.2.1] using h
    have hlabels := p.1.injective hsame
    have hne : Fin.last n ≠ (0 : Fin (n + 1)) := by
      intro hzero
      have hv := congrArg Fin.val hzero
      simp only [Fin.val_last, Fin.val_zero] at hv
      exact (NeZero.ne n) hv
    exact hne hlabels
  let r : {r : Fin (L + 1) // r ≠ 0} :=
    ⟨p.1 (Fin.last n), hlast0⟩
  let s : Fin L := (cyclicInsertPivotEquiv L).symm r
  have hrs : cyclicInsertPosition s = p.1 (Fin.last n) := by
    have h := (cyclicInsertPivotEquiv L).apply_symm_apply r
    exact congrArg Subtype.val h
  have hlowerNe (i : Fin n) :
      p.1 i.castSucc ≠ cyclicInsertPosition s := by
    rw [hrs]
    exact fun h ↦ (Fin.castSucc_ne_last i) (p.1.injective h)
  let lower : Fin n ↪ Fin L :=
    ⟨fun i ↦ (finSuccAboveEquiv (cyclicInsertPosition s)).symm
        ⟨p.1 i.castSucc, hlowerNe i⟩,
      fun i j hij ↦ by
        apply Fin.castSucc_injective n
        apply p.1.injective
        have hsub := congrArg
          (fun u ↦ finSuccAboveEquiv (cyclicInsertPosition s) u) hij
        have hsub' :
            (⟨p.1 i.castSucc, hlowerNe i⟩ :
              {x : Fin (L + 1) // x ≠ cyclicInsertPosition s}) =
            ⟨p.1 j.castSucc, hlowerNe j⟩ := by
          simpa using hsub
        exact congrArg Subtype.val hsub'⟩
  have hlower_expand (i : Fin n) :
      cyclicInsertEmbedding s (lower i) = p.1 i.castSucc := by
    change ((finSuccAboveEquiv (cyclicInsertPosition s)) (lower i)).1 = _
    simp [lower]
  have hlowerZero : lower 0 = 0 := by
    apply (cyclicInsertEmbedding s).injective
    rw [hlower_expand]
    rw [show (0 : Fin n).castSucc = (0 : Fin (n + 1)) by rfl]
    rw [p.2.1]
    exact (cyclicInsertEmbedding_zero s).symm
  let lowerA : AnchoredBoxEmbedding n L := ⟨lower, hlowerZero⟩
  have hsUnused : s ∉ Set.range lower := by
    rintro ⟨b, hb⟩
    apply p.2.2 b
    have hnext : nextPosition (L + 1) (p.1 (Fin.last n)) =
        cyclicInsertEmbedding s s := by
      rw [← hrs]
      exact nextPosition_cyclicInsertPosition s
    rw [hnext]
    rw [← hlower_expand b]
    rw [hb]
  refine ⟨⟨lowerA, ⟨s, hsUnused⟩⟩, ?_⟩
  apply Subtype.ext
  apply Function.Embedding.ext
  intro i
  by_cases hi : i = Fin.last n
  · subst i
    simpa [anchoredCyclicInsertLast, hrs]
  · obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr hi
    simpa [anchoredCyclicInsertLast, lowerA] using hlower_expand j

/-- Reversible cyclic deletion/insertion of a selected largest label. -/
noncomputable def anchoredCyclicInsertLastEquiv (n L : ℕ)
    [NeZero n] [NeZero L] :
    (Σ e : AnchoredBoxEmbedding n L,
      {s : Fin L // s ∉ Set.range e.1}) ≃
      AnchoredLastSuccessorFree n L :=
  Equiv.ofBijective anchoredCyclicInsertLast
    ⟨anchoredCyclicInsertLast_injective,
      anchoredCyclicInsertLast_surjective⟩

/-- Inserting one cyclic box cannot create an old-to-old successor relation
that was not already present before insertion. -/
theorem cyclicInsertEmbedding_adjacent_reflect {L : ℕ} [NeZero L]
    (s a b : Fin L)
    (h : cyclicInsertEmbedding s b =
      nextPosition (L + 1) (cyclicInsertEmbedding s a)) :
    b = nextPosition L a := by
  cases L with
  | zero => exact Fin.elim0 s
  | succ L =>
    change cyclicInsertEmbedding s b = cyclicInsertEmbedding s a + 1 at h
    change b = a + 1
    apply Fin.ext
    have hv₀ : ((cyclicInsertPosition s).succAbove b).val =
        (((cyclicInsertPosition s).succAbove a) + 1).val :=
      congrArg Fin.val h
    have hv : ((cyclicInsertPosition s).succAbove b).val =
        if (cyclicInsertPosition s).succAbove a = Fin.last (L + 1)
        then 0 else ((cyclicInsertPosition s).succAbove a).val + 1 :=
      hv₀.trans (Fin.val_add_one ((cyclicInsertPosition s).succAbove a))
    clear h hv₀
    have hblt : b.castSucc < cyclicInsertPosition s ↔
        b.val < (cyclicInsertPosition s).val := Iff.rfl
    have halt : a.castSucc < cyclicInsertPosition s ↔
        a.val < (cyclicInsertPosition s).val := Iff.rfl
    rw [Fin.val_add_one a]
    simp only [Fin.succAbove] at hv
    split_ifs at hv ⊢ <;>
      simp only [Fin.ext_iff, Fin.val_last, Fin.val_castSucc, Fin.val_succ,
        hblt, halt] at * <;>
      omega

/-- If the inserted box is not placed before `b`, an old successor relation
`a → b` remains a successor relation after insertion. -/
theorem cyclicInsertEmbedding_adjacent_of_ne {L : ℕ} [NeZero L]
    (s a b : Fin L) (hab : b = nextPosition L a) (hsb : s ≠ b) :
    cyclicInsertEmbedding s b =
      nextPosition (L + 1) (cyclicInsertEmbedding s a) := by
  cases L with
  | zero => exact Fin.elim0 s
  | succ L =>
    change b = a + 1 at hab
    change cyclicInsertEmbedding s b = cyclicInsertEmbedding s a + 1
    apply Fin.ext
    have habv₀ := congrArg Fin.val hab
    have habv : b.val = if a = Fin.last L then 0 else a.val + 1 :=
      habv₀.trans (Fin.val_add_one a)
    have hsbv : s.val ≠ b.val := fun h ↦ hsb (Fin.ext h)
    have hnext : (((cyclicInsertPosition s).succAbove a) + 1).val =
        if (cyclicInsertPosition s).succAbove a = Fin.last (L + 1)
        then 0 else ((cyclicInsertPosition s).succAbove a).val + 1 :=
      Fin.val_add_one ((cyclicInsertPosition s).succAbove a)
    change ((cyclicInsertPosition s).succAbove b).val =
      (((cyclicInsertPosition s).succAbove a) + 1).val
    rw [hnext]
    have hblt : b.castSucc < cyclicInsertPosition s ↔
        b.val < (cyclicInsertPosition s).val := Iff.rfl
    have halt : a.castSucc < cyclicInsertPosition s ↔
        a.val < (cyclicInsertPosition s).val := Iff.rfl
    simp only [Fin.succAbove]
    unfold cyclicInsertPosition at *
    split_ifs at * <;>
      simp only [Fin.ext_iff, Fin.val_last, Fin.val_castSucc, Fin.val_succ,
        Fin.val_zero, Fin.succAbove_last, hblt, halt] at * <;>
      omega

@[simp] theorem anchoredCyclicInsertLast_castSucc {n L : ℕ}
    [NeZero n] [NeZero L]
    (z : Σ e : AnchoredBoxEmbedding n L,
      {s : Fin L // s ∉ Set.range e.1}) (i : Fin n) :
    (anchoredCyclicInsertLast z).1 i.castSucc =
      cyclicInsertEmbedding z.2.1 (z.1.1 i) := by
  simp [anchoredCyclicInsertLast]

@[simp] theorem anchoredCyclicInsertLast_last {n L : ℕ}
    [NeZero n] [NeZero L]
    (z : Σ e : AnchoredBoxEmbedding n L,
      {s : Fin L // s ∉ Set.range e.1}) :
    (anchoredCyclicInsertLast z).1 (Fin.last n) =
      cyclicInsertPosition z.2.1 := by
  simp [anchoredCyclicInsertLast]

/-- A full safe placement is equivalently a successor-free last-label
placement carrying the remaining full Ferrers safety predicate. -/
def ferrersPlacementEquivLastFreeSubtype {n L : ℕ}
    [NeZero n] [NeZero L]
    (C : Finset (Fin (n + 1))) (htop : Fin.last n ∈ C) :
    AnchoredFerrersBoxPlacement (n := n + 1) (q := L + 1) C ≃
      {p : AnchoredLastSuccessorFree n L //
        ∀ c, c ∈ C → ∀ b, b < c →
          p.1 b ≠ nextPosition (L + 1) (p.1 c)} where
  toFun p := by
    refine ⟨⟨p.1, p.2.1, ?_⟩, p.2.2⟩
    intro b
    exact p.2.2 (Fin.last n) htop b.castSucc (Fin.castSucc_lt_last b)
  invFun p := ⟨p.1.1, p.1.2.1, p.2⟩
  left_inv p := by rfl
  right_inv p := by rfl

/-- Rearrange a safe anchored embedding and its unused slot into the
ordinary anchored Ferrers placement sigma type. -/
def ferrersSafeSigmaEquivPlacement {n L : ℕ}
    [NeZero n] [NeZero L] (D : Finset (Fin n)) :
    {z : Σ e : AnchoredBoxEmbedding n L,
        {s : Fin L // s ∉ Set.range e.1} //
      ∀ c, c ∈ D → ∀ b, b < c →
        z.1.1 b ≠ nextPosition L (z.1.1 c)} ≃
      Σ p : AnchoredFerrersBoxPlacement (n := n) (q := L) D,
        FerrersUnusedSlot D p where
  toFun z := ⟨⟨z.1.1.1, z.1.1.2, z.2⟩, z.1.2⟩
  invFun z := ⟨⟨⟨z.1.1, z.1.2.1⟩, z.2⟩, z.1.2.2⟩
  left_inv z := by rfl
  right_inv z := by rfl

/-- Removing a selected largest label together with its box gives a safe
placement of the smaller Ferrers system and one arbitrary unused slot. -/
noncomputable def anchoredFerrersBoxPlacementEquivDropLast_of_mem
    {n L : ℕ} [NeZero n] [NeZero L]
    (C : Finset (Fin (n + 1))) (htop : Fin.last n ∈ C) :
    AnchoredFerrersBoxPlacement (n := n + 1) (q := L + 1) C ≃
      Σ p : AnchoredFerrersBoxPlacement (n := n) (q := L)
        (ferrersDropLastColumns C),
          FerrersUnusedSlot (ferrersDropLastColumns C) p := by
  let E := (anchoredCyclicInsertLastEquiv n L).symm
  refine (ferrersPlacementEquivLastFreeSubtype C htop).trans
    ((Equiv.subtypeEquiv E (fun p ↦ ?_)).trans
      (ferrersSafeSigmaEquivPlacement (ferrersDropLastColumns C)))
  let z := E p
  have hz : anchoredCyclicInsertLast z = p :=
    (anchoredCyclicInsertLastEquiv n L).apply_symm_apply p
  have hcast (i : Fin n) :
      p.1 i.castSucc = cyclicInsertEmbedding z.2.1 (z.1.1 i) := by
    rw [← hz]
    exact anchoredCyclicInsertLast_castSucc z i
  constructor
  · intro hp c hc b hbc hbad
    have hsne : z.2.1 ≠ z.1.1 b := by
      intro h
      exact z.2.2 ⟨b, h.symm⟩
    have hadj := cyclicInsertEmbedding_adjacent_of_ne
      z.2.1 (z.1.1 c) (z.1.1 b) hbad hsne
    apply hp c.castSucc (by simpa using hc) b.castSucc (by simpa using hbc)
    simpa only [hcast] using hadj
  · intro hlower c hc b hbc hbad
    by_cases hclast : c = Fin.last n
    · subst c
      have hbne : b ≠ Fin.last n := by
        intro h
        subst b
        exact (lt_irrefl _ hbc)
      obtain ⟨b₀, rfl⟩ := Fin.exists_castSucc_eq.mpr hbne
      exact p.2.2 b₀ hbad
    · obtain ⟨c₀, rfl⟩ := Fin.exists_castSucc_eq.mpr hclast
      have hbne : b ≠ Fin.last n := by
        intro h
        subst b
        exact (not_lt_of_ge (Fin.le_last _)) hbc
      obtain ⟨b₀, rfl⟩ := Fin.exists_castSucc_eq.mpr hbne
      apply hlower c₀ (by simpa using hc) b₀ (by simpa using hbc)
      apply cyclicInsertEmbedding_adjacent_reflect z.2.1
      simpa only [hcast] using hbad

/-- Cardinal recurrence when the largest label is not selected. -/
theorem card_anchoredFerrersBoxPlacement_dropLast_of_not_mem
    {n q : ℕ} [NeZero n] [NeZero q]
    (C : Finset (Fin (n + 1))) (htop : Fin.last n ∉ C) :
    Fintype.card (AnchoredFerrersBoxPlacement (n := n + 1) (q := q) C) =
      Fintype.card (AnchoredFerrersBoxPlacement (n := n) (q := q)
        (ferrersDropLastColumns C)) * (q - n) := by
  rw [Fintype.card_congr
    (anchoredFerrersBoxPlacementEquivDropLast_of_not_mem C htop),
    Fintype.card_sigma]
  simp_rw [card_ferrersUnusedSlot]
  simp

/-- Cardinal recurrence when the largest label is selected: its occupied box
is deleted as well. -/
theorem card_anchoredFerrersBoxPlacement_dropLast_of_mem
    {n L : ℕ} [NeZero n] [NeZero L]
    (C : Finset (Fin (n + 1))) (htop : Fin.last n ∈ C) :
    Fintype.card (AnchoredFerrersBoxPlacement (n := n + 1)
      (q := L + 1) C) =
      Fintype.card (AnchoredFerrersBoxPlacement (n := n) (q := L)
        (ferrersDropLastColumns C)) * (L - n) := by
  rw [Fintype.card_congr
    (anchoredFerrersBoxPlacementEquivDropLast_of_mem C htop),
    Fintype.card_sigma]
  simp_rw [card_ferrersUnusedSlot]
  simp

end DeformationMatrix

end CyclicBraidArrangement
