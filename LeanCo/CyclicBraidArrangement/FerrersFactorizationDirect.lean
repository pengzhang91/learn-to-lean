import LeanCo.CyclicBraidArrangement.Applications
import LeanCo.CyclicBraidArrangement.ArrangementMainTheorem
import Mathlib.Data.Fintype.CardEmbedding

/-!
# Direct combinatorics for the Ferrers graphical-Shi factorization

This file develops the internal combinatorial ingredients of equation (4.1).
For the Ferrers graph, a graphical cyclic descent is exactly a cyclic descent
whose top belongs to the selected column set.  The height is the number of
unselected labels below that top; this is the forbidden-successor count in the
standard increasing-label insertion proof of the product formula.
-/

namespace CyclicBraidArrangement

open scoped BigOperators

namespace DeformationMatrix

variable {n : ℕ}

/-- For a descending pair, Ferrers adjacency depends only on whether its
larger endpoint is a selected column. -/
theorem ferrersGraph_adj_of_gt (C : Finset (Fin n)) {a b : Fin n}
    (hba : b < a) : (ferrersGraph C).Adj a b ↔ a ∈ C := by
  rw [ferrersGraph_adj]
  constructor
  · rintro (h | h)
    · exact (hba.asymm h.1).elim
    · exact h.2
  · exact fun ha ↦ Or.inr ⟨hba, ha⟩

/-- Entry form of the Ferrers graphical-Shi deformation. -/
theorem graphicalShi_ferrers_entry (C : Finset (Fin n)) (a b : Fin n) :
    (graphicalShi (ferrersGraph C)).entry a b =
      if b < a ∧ a ∈ C then 1 else 0 := by
  classical
  unfold graphicalShi
  by_cases hba : b < a
  · have hab : ¬ a < b := hba.asymm
    simp [ferrersGraph_adj, hba, hab]
  · simp [hba]

/-- The Ferrers graphical cyclic-descent statistic: count positions whose
top lies in `C` and whose successor is smaller. -/
theorem graphicalCyclicDescents_ferrers [NeZero n]
    (C : Finset (Fin n)) (w : CyclicOrdering n) :
    graphicalCyclicDescents (ferrersGraph C) w =
      ((Finset.univ : Finset (Fin n)).filter fun k ↦
        w k ∈ C ∧ w (nextPosition n k) < w k).card := by
  classical
  unfold graphicalCyclicDescents
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hdesc : w (nextPosition n k) < w k
  · have hasc : ¬ w k < w (nextPosition n k) := hdesc.asymm
    simp [hdesc, hasc, ferrersGraph_adj]
  · simp [hdesc]

/-! ## A box model for the genuine Ferrers complement -/

variable {q : ℕ}

/-- Anchored injective placements of the labels in a `q`-cycle.  A selected
label `c` may not be immediately followed by a smaller label. -/
def AnchoredFerrersBoxPlacement [NeZero n] [NeZero q]
    (C : Finset (Fin n)) :=
  {p : Fin n ↪ Fin q //
    p 0 = 0 ∧ ∀ c, c ∈ C → ∀ b, b < c →
      p b ≠ nextPosition q (p c)}

noncomputable instance anchoredFerrersBoxPlacementFintype
    [NeZero n] [NeZero q] (C : Finset (Fin n)) :
    Fintype (AnchoredFerrersBoxPlacement (n := n) (q := q) C) :=
  by
    classical
    letI : Fintype (Fin n ↪ Fin q) := Function.Embedding.fintype
    exact Fintype.ofInjective Subtype.val Subtype.val_injective

/-- Under `Fin q ≃ ZMod q`, advancing one cyclic box has residue
difference one. -/
theorem finEquiv_nextPosition_sub [NeZero q] (p : Fin q) :
    ZMod.finEquiv q (nextPosition q p) - ZMod.finEquiv q p = 1 := by
  change ZMod.finEquiv q (p + 1) - ZMod.finEquiv q p = 1
  rw [map_add, map_one]
  simp

/-- Every point of the genuine anchored Ferrers-Shi complement has distinct
canonical boxes. -/
theorem anchoredFerrers_coordinates_injective [NeZero n] [NeZero q]
    (C : Finset (Fin n))
    (x : (graphicalShi (ferrersGraph C)).AnchoredFiniteFieldComplement
      (ZMod q)) :
    Function.Injective (fun a : Fin n ↦
      (ZMod.finEquiv q).symm (x.1.1 a)) := by
  intro a b hab
  by_contra hne
  let e : (graphicalShi (ferrersGraph C)).ForbiddenEquation :=
    ⟨a, ⟨b, Ne.symm hne⟩, ⟨0, Nat.succ_pos _⟩⟩
  apply x.1.2 e
  dsimp [e, SatisfiesEquation, ForbiddenEquation.target,
    ForbiddenEquation.source, ForbiddenEquation.distance]
  norm_num
  have hz : x.1.1 a = x.1.1 b := by
    simpa using congrArg (ZMod.finEquiv q) hab
  simp [hz]

/-- Canonical representatives turn the anchored Ferrers-Shi complement into
the box model. -/
noncomputable def anchoredFerrersToBox [NeZero n] [NeZero q]
    (C : Finset (Fin n)) :
    (graphicalShi (ferrersGraph C)).AnchoredFiniteFieldComplement
        (ZMod q) →
      AnchoredFerrersBoxPlacement (n := n) (q := q) C := fun x ↦ by
  let p : Fin n ↪ Fin q :=
    ⟨fun a ↦ (ZMod.finEquiv q).symm (x.1.1 a),
      anchoredFerrers_coordinates_injective C x⟩
  refine ⟨p, ?_, ?_⟩
  · apply (ZMod.finEquiv q).injective
    simpa [p] using x.2
  · intro c hc b hbc hsucc
    have hentry :
        (graphicalShi (ferrersGraph C)).entry c b = 1 := by
      rw [graphicalShi_ferrers_entry]
      simp [hbc, hc]
    let e : (graphicalShi (ferrersGraph C)).ForbiddenEquation :=
      ⟨c, ⟨b, Fin.ne_of_lt hbc⟩,
        ⟨1, by rw [hentry]; omega⟩⟩
    apply x.1.2 e
    dsimp [e, SatisfiesEquation, ForbiddenEquation.target,
      ForbiddenEquation.source, ForbiddenEquation.distance]
    norm_num
    calc
      x.1.1 b - x.1.1 c =
          ZMod.finEquiv q (nextPosition q (p c)) -
            ZMod.finEquiv q (p c) := by
        rw [← hsucc]
        simp [p]
      _ = 1 := finEquiv_nextPosition_sub (p c)

/-- In box coordinates, residue difference one means precisely cyclic
successorship. -/
theorem finEquiv_sub_eq_one_iff [NeZero q] (a b : Fin q) :
    ZMod.finEquiv q a - ZMod.finEquiv q b = 1 ↔
      a = nextPosition q b := by
  constructor
  · intro h
    apply (ZMod.finEquiv q).injective
    have hn := finEquiv_nextPosition_sub b
    linear_combination h - hn
  · rintro rfl
    exact finEquiv_nextPosition_sub b

/-- Realizing box indices as residues gives a genuine anchored
Ferrers-Shi-complement point. -/
noncomputable def anchoredFerrersFromBox [NeZero n] [NeZero q]
    (C : Finset (Fin n)) :
    AnchoredFerrersBoxPlacement (n := n) (q := q) C →
      (graphicalShi (ferrersGraph C)).AnchoredFiniteFieldComplement
        (ZMod q) := fun p ↦ by
  refine ⟨⟨fun a ↦ ZMod.finEquiv q (p.1 a), ?_⟩, ?_⟩
  · intro e heq
    unfold SatisfiesEquation at heq
    have hle := e.distance_le (graphicalShi (ferrersGraph C))
    have hentryLe := graphicalShi_entry_le_one (ferrersGraph C)
      (e.source (graphicalShi (ferrersGraph C)))
      (e.target (graphicalShi (ferrersGraph C)))
    have hd : e.distance (graphicalShi (ferrersGraph C)) = 0 ∨
        e.distance (graphicalShi (ferrersGraph C)) = 1 := by omega
    rcases hd with hd | hd
    · have hzero :
          ZMod.finEquiv q (p.1 (e.target (graphicalShi (ferrersGraph C)))) =
            ZMod.finEquiv q (p.1 (e.source (graphicalShi (ferrersGraph C)))) := by
          have heq0 := heq
          rw [hd] at heq0
          norm_num at heq0
          exact sub_eq_zero.mp heq0
      have hlabels := p.1.injective ((ZMod.finEquiv q).injective hzero)
      exact e.source_ne_target (graphicalShi (ferrersGraph C)) hlabels.symm
    · let a := e.source (graphicalShi (ferrersGraph C))
      let b := e.target (graphicalShi (ferrersGraph C))
      have habC : b < a ∧ a ∈ C := by
        by_contra hnot
        have hentry0 :
            (graphicalShi (ferrersGraph C)).entry a b = 0 := by
          rw [graphicalShi_ferrers_entry]
          simp [hnot]
        change e.distance (graphicalShi (ferrersGraph C)) ≤
          (graphicalShi (ferrersGraph C)).entry a b at hle
        omega
      have hone :
          ZMod.finEquiv q (p.1 b) - ZMod.finEquiv q (p.1 a) = 1 := by
        simpa [a, b, hd] using heq
      exact p.2.2 a habC.2 b habC.1
        ((finEquiv_sub_eq_one_iff (p.1 b) (p.1 a)).1 hone)
  · simp [p.2.1]

/-- Exact equivalence between the genuine anchored complement and the
injective cyclic-box model used by the Ferrers deletion/insertion proof. -/
noncomputable def anchoredFerrersComplementEquivBox [NeZero n] [NeZero q]
    (C : Finset (Fin n)) :
    (graphicalShi (ferrersGraph C)).AnchoredFiniteFieldComplement
        (ZMod q) ≃
      AnchoredFerrersBoxPlacement (n := n) (q := q) C where
  toFun := anchoredFerrersToBox (n := n) (q := q) C
  invFun := anchoredFerrersFromBox (n := n) (q := q) C
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    funext a
    simp [anchoredFerrersToBox, anchoredFerrersFromBox]
  right_inv p := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro a
    simp [anchoredFerrersToBox, anchoredFerrersFromBox]

/-! ### Removing the largest label from an embedding -/

/-- An embedding of `Fin (n+1)` is an embedding of the first `n` labels
together with the unused image of the last label.  This is the last-coordinate
version of mathlib's `Equiv.embeddingFinSucc`. -/
def embeddingFinSuccLastEquiv (n : ℕ) (γ : Type*) :
    (Fin (n + 1) ↪ γ) ≃
      Σ e : Fin n ↪ γ, {y : γ // y ∉ Set.range e} :=
  ((finSuccEquivLast.embeddingCongr (Equiv.refl γ))).trans
    (Function.Embedding.optionEmbeddingEquiv (Fin n) γ)

@[simp] theorem embeddingFinSuccLastEquiv_fst_apply
    {n : ℕ} {γ : Type*} (e : Fin (n + 1) ↪ γ) (i : Fin n) :
    (embeddingFinSuccLastEquiv n γ e).1 i = e i.castSucc := by
  change e (finSuccEquivLast.symm (some i)) = e i.castSucc
  rw [finSuccEquivLast_symm_some]

@[simp] theorem embeddingFinSuccLastEquiv_snd
    {n : ℕ} {γ : Type*} (e : Fin (n + 1) ↪ γ) :
    (embeddingFinSuccLastEquiv n γ e).2.1 = e (Fin.last n) := by
  rfl

@[simp] theorem embeddingFinSuccLastEquiv_symm_castSucc
    {n : ℕ} {γ : Type*}
    (z : Σ e : Fin n ↪ γ, {y : γ // y ∉ Set.range e}) (i : Fin n) :
    (embeddingFinSuccLastEquiv n γ).symm z i.castSucc = z.1 i := by
  have h := (embeddingFinSuccLastEquiv n γ).apply_symm_apply z
  have hi := congrArg (fun u ↦ u.1 i) h
  rw [embeddingFinSuccLastEquiv_fst_apply] at hi
  exact hi

@[simp] theorem embeddingFinSuccLastEquiv_symm_last
    {n : ℕ} {γ : Type*}
    (z : Σ e : Fin n ↪ γ, {y : γ // y ∉ Set.range e}) :
    (embeddingFinSuccLastEquiv n γ).symm z (Fin.last n) = z.2.1 := by
  have h := (embeddingFinSuccLastEquiv n γ).apply_symm_apply z
  have hy := congrArg (fun u ↦ u.2.1) h
  rw [embeddingFinSuccLastEquiv_snd] at hy
  exact hy

/-- Columns inherited after deleting the largest label. -/
def ferrersDropLastColumns (C : Finset (Fin (n + 1))) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ i.castSucc ∈ C

@[simp] theorem mem_ferrersDropLastColumns
    (C : Finset (Fin (n + 1))) (i : Fin n) :
    i ∈ ferrersDropLastColumns C ↔ i.castSucc ∈ C := by
  simp [ferrersDropLastColumns]

/-- The initial interval below `c` has `c.val` elements. -/
theorem card_Iio_fin (c : Fin n) : (Finset.Iio c).card = c.val := by
  simp

/-- Selected and unselected labels partition the labels below a column top. -/
theorem ferrersHeight_add_selectedBelow (C : Finset (Fin n)) (c : Fin n) :
    ferrersHeight C c + ((Finset.Iio c).filter fun b ↦ b ∈ C).card = c.val := by
  classical
  unfold ferrersHeight
  rw [← card_Iio_fin c]
  simpa [add_comm] using
    (Finset.card_filter_add_card_filter_not
      (s := Finset.Iio c) (p := fun b ↦ b ∈ C))

/-- Selected column labels strictly below `c`.  This is the number of
previous insertion stages when the selected labels are processed in their
ambient order. -/
def ferrersSelectedBelow (C : Finset (Fin n)) (c : Fin n) : ℕ :=
  ((Finset.Iio c).filter fun b ↦ b ∈ C).card

theorem ferrersHeight_add_ferrersSelectedBelow
    (C : Finset (Fin n)) (c : Fin n) :
    ferrersHeight C c + ferrersSelectedBelow C c = c.val := by
  exact ferrersHeight_add_selectedBelow C c

/-- If `0` is not selected, every selected column has positive height. -/
theorem ferrersHeight_pos [NeZero n] (C : Finset (Fin n))
    (hzero : (0 : Fin n) ∉ C) {c : Fin n} (hc : c ∈ C) :
    0 < ferrersHeight C c := by
  have hc0 : c ≠ 0 := by intro h; exact hzero (h ▸ hc)
  have h0c : (0 : Fin n) < c := Fin.pos_iff_ne_zero.mpr hc0
  unfold ferrersHeight
  have hmem : (0 : Fin n) ∈ (Finset.Iio c).filter fun b ↦ b ∉ C := by
    simp [h0c, hzero]
  exact Finset.card_pos.mpr ⟨0, hmem⟩

/-- There are `n-|C|` unselected labels. -/
theorem card_compl_ferrersColumns (C : Finset (Fin n)) :
    Cᶜ.card = n - C.card := by
  rw [Finset.card_compl, Fintype.card_fin]

/-- Height is bounded by the total number of unselected labels. -/
theorem ferrersHeight_le_compl_card (C : Finset (Fin n)) (c : Fin n) :
    ferrersHeight C c ≤ n - C.card := by
  classical
  rw [← card_compl_ferrersColumns C]
  unfold ferrersHeight
  apply Finset.card_le_card
  intro b hb
  simp only [Finset.mem_filter, Finset.mem_Iio] at hb
  simpa using hb.2

/-! ### Constant-size local insertion choices

In the circle-insertion proof, deleting all selected labels leaves
`q - |C|` slots.  Immediately before inserting `c`, one has additionally
split one slot for every selected label below `c`.  Exactly those earlier
splits together with the `ferrersHeight C c` unselected lower labels are
forbidden.  The next identity is the arithmetic cancellation at the heart
of the product factor `q - |C| - ferrersHeight C c`.
-/

/-- Number of slots present immediately before the insertion of `c`. -/
def ferrersInsertionStageSize (q : ℕ) (C : Finset (Fin n)) (c : Fin n) : ℕ :=
  q - C.card + ferrersSelectedBelow C c

/-- Number of forbidden slots at the insertion stage for `c`. -/
def ferrersForbiddenSlotCount (C : Finset (Fin n)) (c : Fin n) : ℕ :=
  ferrersSelectedBelow C c + ferrersHeight C c

/-- Cancellation of the previous-stage splits leaves precisely the factor
appearing in equation (4.1). -/
theorem ferrersInsertionStage_sub_forbidden
    (q : ℕ) (C : Finset (Fin n)) (c : Fin n)
    (hq : n ≤ q) :
    ferrersInsertionStageSize q C c - ferrersForbiddenSlotCount C c =
      q - C.card - ferrersHeight C c := by
  have hheight := ferrersHeight_le_compl_card C c
  have hcard : C.card ≤ n := by
    simpa using Finset.card_le_univ C
  unfold ferrersInsertionStageSize ferrersForbiddenSlotCount
  omega

/-! The available-slot set itself can be enumerated canonically up to a
finite equivalence.  This is the local combinatorial ingredient used by the
eventual insert/delete construction. -/

/-- Labels strictly below a selected top. -/
abbrev FerrersLowerLabel (c : Fin n) := {b : Fin n // b < c}

theorem card_ferrersLowerLabel (c : Fin n) :
    Fintype.card (FerrersLowerLabel c) = c.val := by
  let e : FerrersLowerLabel c ≃ {b : Fin n // b ∈ Finset.Iio c} :=
    Equiv.subtypeEquiv (Equiv.refl _) (by simp)
  rw [Fintype.card_congr e, Fintype.card_coe, card_Iio_fin]

/-- Slots occupied by lower labels, expressed through their position
embedding in the current cyclic word. -/
def ferrersForbiddenSlots {L : ℕ} {c : Fin n}
    (lowerPos : FerrersLowerLabel c ↪ Fin L) : Finset (Fin L) :=
  (Finset.univ : Finset (FerrersLowerLabel c)).map lowerPos

/-- Cyclic insertion slots whose successor is not a lower label. -/
def ferrersAllowedSlots {L : ℕ} {c : Fin n}
    (lowerPos : FerrersLowerLabel c ↪ Fin L) : Finset (Fin L) :=
  Finset.univ \ ferrersForbiddenSlots lowerPos

theorem card_ferrersForbiddenSlots {L : ℕ} {c : Fin n}
    (lowerPos : FerrersLowerLabel c ↪ Fin L) :
    (ferrersForbiddenSlots lowerPos).card = c.val := by
  rw [ferrersForbiddenSlots, Finset.card_map, Finset.card_univ,
    card_ferrersLowerLabel]

theorem card_ferrersAllowedSlots {L : ℕ} {c : Fin n}
    (lowerPos : FerrersLowerLabel c ↪ Fin L) :
    (ferrersAllowedSlots lowerPos).card = L - c.val := by
  classical
  rw [ferrersAllowedSlots, Finset.card_sdiff_of_subset
    (Finset.subset_univ (ferrersForbiddenSlots lowerPos)),
    Finset.card_univ, Fintype.card_fin, card_ferrersForbiddenSlots]

/-- The paper's `Fin (q-|C|-h_c)` choice type is an exact enumeration of
the actually allowed slots in any insertion stage having the prescribed
lower-label position embedding. -/
noncomputable def ferrersAllowedSlotEquiv
    (q : ℕ) (C : Finset (Fin n)) (c : Fin n) (hq : n ≤ q)
    (lowerPos : FerrersLowerLabel c ↪
      Fin (ferrersInsertionStageSize q C c)) :
    {s // s ∈ ferrersAllowedSlots lowerPos} ≃
      Fin (q - C.card - ferrersHeight C c) := by
  apply Finset.equivFinOfCardEq
  rw [card_ferrersAllowedSlots]
  have hheight := ferrersHeight_le_compl_card C c
  have hsplit := ferrersHeight_add_ferrersSelectedBelow C c
  have hcard : C.card ≤ n := by
    simpa using Finset.card_le_univ C
  unfold ferrersInsertionStageSize
  omega

/-! ### Cyclic box insertion primitives -/

/-- To insert a new box immediately before slot `s` while keeping slot zero
as the rotation anchor, insert at the end when `s=0`, and at the ordinary
linear position `s` otherwise. -/
def cyclicInsertPosition {L : ℕ} [NeZero L] (s : Fin L) : Fin (L + 1) :=
  if s = 0 then Fin.last L else s.castSucc

/-- Embedding of the old cyclic slots after inserting immediately before
`s`. -/
def cyclicInsertEmbedding {L : ℕ} [NeZero L] (s : Fin L) :
    Fin L ↪ Fin (L + 1) :=
  (cyclicInsertPosition s).succAboveEmb

theorem cyclicInsertPosition_ne_zero {L : ℕ} [NeZero L] (s : Fin L) :
    cyclicInsertPosition s ≠ 0 := by
  unfold cyclicInsertPosition
  split_ifs with hs
  · intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_last, Fin.val_zero] at hv
    exact (NeZero.ne L) hv
  · intro h
    apply hs
    apply Fin.ext
    simpa using congrArg Fin.val h

/-- Insertion leaves the distinguished zero slot fixed. -/
@[simp] theorem cyclicInsertEmbedding_zero {L : ℕ} [NeZero L]
    (s : Fin L) : cyclicInsertEmbedding s 0 = 0 := by
  by_cases hs : s = 0
  · subst s
    change (Fin.last L).succAbove 0 = 0
    simp
  · simp only [cyclicInsertEmbedding, cyclicInsertPosition, if_neg hs,
      Fin.coe_succAboveEmb]
    rw [Fin.succAbove_of_castSucc_lt]
    · rfl
    · simpa [Fin.pos_iff_ne_zero] using hs

/-- The successor of the inserted box is the embedded chosen slot, including
the wraparound case `s=0`. -/
theorem nextPosition_cyclicInsertPosition {L : ℕ} [NeZero L]
    (s : Fin L) :
    nextPosition (L + 1) (cyclicInsertPosition s) =
      cyclicInsertEmbedding s s := by
  by_cases hs : s = 0
  · subst s
    apply Fin.ext
    simp [cyclicInsertPosition, cyclicInsertEmbedding, nextPosition]
  · rw [show cyclicInsertPosition s = s.castSucc by
      simp [cyclicInsertPosition, hs]]
    simp only [cyclicInsertEmbedding, cyclicInsertPosition, if_neg hs,
      Fin.coe_succAboveEmb]
    rw [Fin.succAbove_of_le_castSucc _ _ Fin.le_rfl]
    change s.castSucc + 1 = s.succ
    apply Fin.ext
    rw [Fin.val_add_one_of_lt']
    · rfl
    · exact Nat.succ_lt_succ s.isLt

/-- Insert a value in a cyclic word immediately before a chosen old slot. -/
def cyclicInsertWord {L : ℕ} [NeZero L] {A : Type*}
    (s : Fin L) (a : A) (word : Fin L → A) : Fin (L + 1) → A :=
  Fin.insertNth (cyclicInsertPosition s) a word

@[simp] theorem cyclicInsertWord_new {L : ℕ} [NeZero L] {A : Type*}
    (s : Fin L) (a : A) (word : Fin L → A) :
    cyclicInsertWord s a word (cyclicInsertPosition s) = a := by
  simp [cyclicInsertWord]

@[simp] theorem cyclicInsertWord_old {L : ℕ} [NeZero L] {A : Type*}
    (s j : Fin L) (a : A) (word : Fin L → A) :
    cyclicInsertWord s a word (cyclicInsertEmbedding s j) = word j := by
  simp [cyclicInsertWord, cyclicInsertEmbedding]

/-- The chosen old slot really is the successor value of the newly inserted
box. -/
theorem cyclicInsertWord_next_new {L : ℕ} [NeZero L] {A : Type*}
    (s : Fin L) (a : A) (word : Fin L → A) :
    cyclicInsertWord s a word
        (nextPosition (L + 1) (cyclicInsertPosition s)) = word s := by
  rw [nextPosition_cyclicInsertPosition]
  exact cyclicInsertWord_old s s a word

/-- Removing the box just inserted recovers the old cyclic word. -/
@[simp] theorem removeNth_cyclicInsertWord {L : ℕ} [NeZero L]
    {A : Type*} (s : Fin L) (a : A) (word : Fin L → A) :
    Fin.removeNth (cyclicInsertPosition s)
      (cyclicInsertWord s a word) = word := by
  exact Fin.removeNth_insertNth _ _ _

/-- The local Ferrers insertion factor is nonnegative at every natural
evaluation `q ≥ n`. -/
theorem ferrersHeight_add_card_le
    (q : ℕ) (C : Finset (Fin n)) (c : Fin n) (hq : n ≤ q) :
    C.card + ferrersHeight C c ≤ q := by
  have hheight := ferrersHeight_le_compl_card C c
  have hcard : C.card ≤ n := by
    simpa using Finset.card_le_univ C
  omega

/-! ### The initial falling-factorial block

After one slot is fixed to quotient simultaneous rotation, the unselected
nonzero labels inject into `q - |C| - 1` residual slots.  Mathlib's exact
cardinality theorem for embeddings gives the first falling factorial in
the Ferrers product.
-/

/-- Unselected labels other than the rotation anchor. -/
abbrev FerrersBaseLabel [NeZero n] (C : Finset (Fin n)) :=
  {i : Fin n // i ∈ Cᶜ.erase 0}

/-- Residual slots after reserving one slot for each selected label and one
slot for the rotation anchor. -/
abbrev FerrersBaseSlot (q : ℕ) (C : Finset (Fin n)) :=
  Fin (q - C.card - 1)

/-- Initial injective placements used by the circle-insertion proof. -/
abbrev FerrersBasePlacement [NeZero n] (q : ℕ) (C : Finset (Fin n)) :=
  FerrersBaseLabel C ↪ FerrersBaseSlot q C

theorem card_ferrersBaseLabel [NeZero n]
    (C : Finset (Fin n)) (hzero : (0 : Fin n) ∉ C) :
    Fintype.card (FerrersBaseLabel C) = n - C.card - 1 := by
  rw [Fintype.card_coe]
  have hzcomp : (0 : Fin n) ∈ Cᶜ := by simpa
  rw [Finset.card_erase_of_mem hzcomp, card_compl_ferrersColumns]

/-- The base-placement cardinal is the descending factorial in equation
(4.1), before casting to `ℚ`. -/
theorem card_ferrersBasePlacement [NeZero n]
    (q : ℕ) (C : Finset (Fin n)) (hzero : (0 : Fin n) ∉ C) :
    Fintype.card (FerrersBasePlacement q C) =
      (q - C.card - 1).descFactorial (n - C.card - 1) := by
  classical
  rw [Fintype.card_embedding_eq, Fintype.card_fin,
    card_ferrersBaseLabel C hzero]

/-- Independent local slot choices for all selected labels. -/
abbrev FerrersInsertionChoice (q : ℕ) (C : Finset (Fin n)) :=
  ∀ c : {c : Fin n // c ∈ C},
    Fin (q - C.card - ferrersHeight C c.1)

/-- Product parameter space predicted by the circle-insertion proof. -/
abbrev FerrersInsertionData [NeZero n]
    (q : ℕ) (C : Finset (Fin n)) :=
  FerrersBasePlacement q C × FerrersInsertionChoice q C

theorem card_ferrersInsertionChoice
    (q : ℕ) (C : Finset (Fin n)) :
    Fintype.card (FerrersInsertionChoice q C) =
      ∏ c ∈ C, (q - C.card - ferrersHeight C c) := by
  classical
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin]
  exact Finset.prod_coe_sort C
    (fun c : Fin n ↦ q - C.card - ferrersHeight C c)

/-- Exact cardinal of the product parameter space.  Thus the only missing
ingredient for the natural-valued Ferrers count is an explicit equivalence
from safe anchored placements to `FerrersInsertionData`. -/
theorem card_ferrersInsertionData [NeZero n]
    (q : ℕ) (C : Finset (Fin n)) (hzero : (0 : Fin n) ∉ C) :
    Fintype.card (FerrersInsertionData q C) =
      (q - C.card - 1).descFactorial (n - C.card - 1) *
        ∏ c ∈ C, (q - C.card - ferrersHeight C c) := by
  rw [Fintype.card_prod, card_ferrersBasePlacement q C hzero,
    card_ferrersInsertionChoice]

/-- Rational falling factorials agree with descending factorials at a
natural argument large enough to contain all factors. -/
theorem fallingFactorialValue_natCast (a k : ℕ) (hk : k ≤ a) :
    fallingFactorialValue (a : ℚ) k = (a.descFactorial k : ℚ) := by
  unfold fallingFactorialValue
  rw [Nat.descFactorial_eq_prod_range]
  push_cast
  apply Finset.prod_congr rfl
  intro i hi
  rw [Nat.cast_sub]
  exact (Finset.mem_range.mp hi).le.trans hk

/-- At every natural evaluation `q ≥ n`, the first rational factor in
equation (4.1) is exactly the cardinal of the base-placement type. -/
theorem ferrersBaseFactorValue_natCast [NeZero n]
    (q : ℕ) (C : Finset (Fin n)) (hzero : (0 : Fin n) ∉ C)
    (hq : n ≤ q) :
    fallingFactorialValue ((q : ℚ) - C.card - 1)
        (n - C.card - 1) =
      (Fintype.card (FerrersBasePlacement q C) : ℚ) := by
  have hcard : C.card ≤ n := by
    simpa using Finset.card_le_univ C
  have hCq : C.card ≤ q := hcard.trans hq
  have hC_lt_n : C.card < n := by
    have hproper : C ⊂ (Finset.univ : Finset (Fin n)) := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ C, ?_⟩
      intro h
      have : (0 : Fin n) ∈ C := by rw [h]; simp
      exact hzero this
    simpa using Finset.card_lt_card hproper
  have hone : 1 ≤ q - C.card := by omega
  have hk : n - C.card - 1 ≤ q - C.card - 1 := by omega
  have harg : ((q - C.card - 1 : ℕ) : ℚ) =
      (q : ℚ) - C.card - 1 := by
    rw [Nat.cast_sub hone, Nat.cast_sub hCq]
    norm_num
  rw [← harg, fallingFactorialValue_natCast _ _ hk,
    card_ferrersBasePlacement q C hzero]

/-- Every linear Ferrers factor at `q ≥ n` is the cast of its explicit
finite slot count. -/
theorem ferrersLinearFactor_natCast
    (q : ℕ) (C : Finset (Fin n)) (c : Fin n) (hq : n ≤ q) :
    (q : ℚ) - C.card - ferrersHeight C c =
      (q - C.card - ferrersHeight C c : ℕ) := by
  have hCq : C.card ≤ q :=
    (by simpa using Finset.card_le_univ C : C.card ≤ n).trans hq
  have htot := ferrersHeight_add_card_le q C c hq
  rw [Nat.cast_sub (show ferrersHeight C c ≤ q - C.card by omega),
    Nat.cast_sub hCq]

/-- The entire rational Ferrers product at `q ≥ n` is the cast of the
finite insertion-data cardinal. -/
theorem ferrersShiFactorValue_natCast_eq_card [NeZero n]
    (q : ℕ) (C : Finset (Fin n)) (hzero : (0 : Fin n) ∉ C)
    (hq : n ≤ q) :
    ferrersShiFactorValue C q =
      (Fintype.card (FerrersInsertionData q C) : ℚ) := by
  rw [ferrersShiFactorValue,
    ferrersBaseFactorValue_natCast q C hzero hq]
  simp_rw [ferrersLinearFactor_natCast q C _ hq]
  rw [← Nat.cast_prod]
  rw [card_ferrersBasePlacement q C hzero]
  norm_cast
  exact (card_ferrersInsertionData q C hzero).symm

/-! ### Polynomial and finite-field reduction of equation (4.1) -/

/-- Polynomial whose evaluation is the explicit Ferrers product in equation
(4.1). -/
noncomputable def ferrersShiFactorPolynomial (C : Finset (Fin n)) :
    Polynomial ℚ :=
  (∏ i ∈ Finset.range (n - C.card - 1),
      (Polynomial.X - Polynomial.C ((C.card + 1 + i : ℕ) : ℚ))) *
    ∏ c ∈ C,
      (Polynomial.X -
        Polynomial.C ((C.card + ferrersHeight C c : ℕ) : ℚ))

@[simp] theorem eval_ferrersShiFactorPolynomial
    (C : Finset (Fin n)) (t : ℚ) :
    Polynomial.eval t (ferrersShiFactorPolynomial C) =
      ferrersShiFactorValue C t := by
  classical
  unfold ferrersShiFactorPolynomial ferrersShiFactorValue
  simp only [Polynomial.eval_mul, Polynomial.eval_prod,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  congr 1
  · unfold fallingFactorialValue
    apply Finset.prod_congr rfl
    intro i hi
    push_cast
    ring
  · apply Finset.prod_congr rfl
    intro c hc
    push_cast
    ring

/-- The exact remaining combinatorial construction in the direct proof:
delete selected labels from an anchored safe circle placement, then record
the residual embedding and one allowed reinsertion slot for each selected
label.  Unlike the former factorization law, this interface asserts a
concrete equivalence of independently defined finite types. -/
def FerrersInsertionEquivalence : Prop :=
  ∀ {n : ℕ} [NeZero n] (C : Finset (Fin n)),
    (0 : Fin n) ∉ C → ∀ (q : ℕ) [NeZero q], n ≤ q →
      Nonempty
        ((graphicalShi (ferrersGraph C)).AnchoredFiniteFieldComplement
            (ZMod q) ≃ FerrersInsertionData q C)

/-- A concrete circle-insertion equivalence makes the explicit Ferrers
product satisfy the independently defined reduced finite-field
specification. -/
theorem ferrersShiFactorPolynomial_isReducedFiniteFieldPolynomial
    (hInsert : FerrersInsertionEquivalence)
    {n : ℕ} [NeZero n] (C : Finset (Fin n))
    (hzero : (0 : Fin n) ∉ C) :
    (graphicalShi (ferrersGraph C)).IsReducedFiniteFieldPolynomial
      (ferrersShiFactorPolynomial C) := by
  refine ⟨n, ?_⟩
  intro q hq
  letI : NeZero q :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (NeZero.pos n) hq)⟩
  rw [eval_ferrersShiFactorPolynomial,
    ferrersShiFactorValue_natCast_eq_card q C hzero hq]
  have hdata :
      Fintype.card
          ((graphicalShi (ferrersGraph C)).AnchoredFiniteFieldComplement
            (ZMod q)) =
        Fintype.card (FerrersInsertionData q C) :=
    Fintype.card_congr (Classical.choice (hInsert C hzero q hq))
  have horbit :=
    (graphicalShi (ferrersGraph C)).card_anchoredFiniteFieldComplement_eq_finiteFieldComplementOrbitCount hq
  exact_mod_cast hdata.symm.trans horbit

/-- Equation (4.1) follows from the explicit insertion equivalence via
finite-field polynomial uniqueness.  No characteristic-polynomial theorem
is assumed in this reduction. -/
theorem ferrersShiFactorization_of_insertionEquivalence
    (hInsert : FerrersInsertionEquivalence)
    {n : ℕ} [NeZero n] (C : Finset (Fin n))
    (hzero : (0 : Fin n) ∉ C) (t : ℚ) :
    cycleFormula (graphicalShi (ferrersGraph C)) t =
      ferrersShiFactorValue C t := by
  have hpoly : cyclePolynomial (graphicalShi (ferrersGraph C)) =
      ferrersShiFactorPolynomial C :=
    isReducedFiniteFieldPolynomial_unique (graphicalShi (ferrersGraph C))
      (cyclePolynomial_isReducedFiniteFieldPolynomial
        (graphicalShi (ferrersGraph C))
        (cyclicallyCompatible_graphicalShi (ferrersGraph C)))
      (ferrersShiFactorPolynomial_isReducedFiniteFieldPolynomial
        hInsert C hzero)
  calc
    cycleFormula (graphicalShi (ferrersGraph C)) t =
        Polynomial.eval t
          (cyclePolynomial (graphicalShi (ferrersGraph C))) :=
      (eval_cyclePolynomial _ _).symm
    _ = Polynomial.eval t (ferrersShiFactorPolynomial C) := by rw [hpoly]
    _ = ferrersShiFactorValue C t := eval_ferrersShiFactorPolynomial C t

/-- Proposition 4.3 at the cyclic-formula level, reduced to the concrete
circle-insertion equivalence rather than the former external factorization
law. -/
theorem proposition_four_three_cycleFormula_of_insertionEquivalence
    (hInsert : FerrersInsertionEquivalence)
    {n : ℕ} [NeZero n] (hn : 2 ≤ n) (C : Finset (Fin n))
    (hzero : (0 : Fin n) ∉ C)
    (M : DeformationMatrix n) (ρ γ : Fin n → ℤ)
    (hentry : ∀ i j, i ≠ j →
      (M.entry i j : ℤ) =
        ((graphicalShi (ferrersGraph C)).entry i j : ℤ) + ρ i + γ j)
    (t : ℚ) :
    cycleFormula M t = ferrersShiFactorValue C
      (t - (integerGaugeTotal ρ γ : ℚ)) := by
  rw [cycleFormula_integerGauge_shift hn M
    (graphicalShi (ferrersGraph C)) ρ γ hentry]
  exact ferrersShiFactorization_of_insertionEquivalence
    hInsert C hzero _

/-- Proposition 4.3 for the independently defined reduced Whitney
characteristic polynomial.  Its only remaining premise is the explicit
finite-type insertion equivalence. -/
theorem proposition_four_three_whitney_of_insertionEquivalence
    (hInsert : FerrersInsertionEquivalence)
    {n : ℕ} [NeZero n] (hn : 2 ≤ n) (C : Finset (Fin n))
    (hzero : (0 : Fin n) ∉ C)
    (M : DeformationMatrix n) (hcompat : M.CyclicallyCompatible)
    (ρ γ : Fin n → ℤ)
    (hentry : ∀ i j, i ≠ j →
      (M.entry i j : ℤ) =
        ((graphicalShi (ferrersGraph C)).entry i j : ℤ) + ρ i + γ j)
    (t : ℚ) :
    Polynomial.eval t M.whitneyReducedCharacteristicPolynomial =
      ferrersShiFactorValue C
        (t - (integerGaugeTotal ρ γ : ℚ)) := by
  rw [M.whitney_mainTheorem_reduced hcompat, eval_cyclePolynomial]
  exact proposition_four_three_cycleFormula_of_insertionEquivalence
    hInsert hn C hzero M ρ γ hentry t

/-- Equation (4.1) reduced to its precise descent-top Worpitzky identity.
This statement contains no arrangement-theoretic premise; its remaining proof
is the increasing-label circle-insertion bijection. -/
def FerrersDescentTopWorpitzky : Prop :=
  ∀ {n : ℕ} [NeZero n] (C : Finset (Fin n)),
    (0 : Fin n) ∉ C → ∀ t : ℚ,
      (∑ w : NormalizedCycle n,
        generalizedChoose
          (t - ((Finset.univ : Finset (Fin n)).filter fun k ↦
            w.1 k ∈ C ∧ w.1 (nextPosition n k) < w.1 k).card - 1)
          (n - 1)) = ferrersShiFactorValue C t

/-- The pure descent-top identity implies the base Ferrers graphical-Shi
factorization, with no `FerrersShiFactorizationLaw` parameter. -/
theorem ferrersShiFactorization_of_descentTopWorpitzky
    (hW : FerrersDescentTopWorpitzky)
    {n : ℕ} [NeZero n] (C : Finset (Fin n))
    (hC : (0 : Fin n) ∉ C) (t : ℚ) :
    cycleFormula (graphicalShi (ferrersGraph C)) t =
      ferrersShiFactorValue C t := by
  rw [cycleFormula_graphicalShi]
  simpa only [graphicalCyclicDescents_ferrers] using hW C hC t

end DeformationMatrix

end CyclicBraidArrangement
