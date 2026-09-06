import LeanCo.QuantumLatin.SingularProduct

/-!
# Resolution of the singular direct product

This file completes Construction 4.6.  The labels `Sum.inl (q, e)` combine
the `q`-fiber of the second outer resolution with the `e`-transversal of
each inner square.  The labels `Sum.inr r` combine the incomplete
transversal of the `r`-th pointed square with the `r`-transversal of the
exceptional square.
-/

open scoped BigOperators ComplexConjugate

namespace LeanCo.QuantumLatin

universe u v w x

variable {α : Type u} {β : Type v} {ρ : Type w} {γ : Type x}
  [Fintype α] [Fintype β] [Fintype ρ]
  [DecidableEq α] [DecidableEq β] [DecidableEq ρ]
  [Fintype γ] [DecidableEq γ]

namespace SingularProductData

variable (X : SingularProductData (α := α) (β := β) (ρ := ρ) (γ := γ))

private def resolutionSpecialLabel (r : ρ) : α :=
  X.split.symm (Sum.inr r)

private noncomputable def resolutionSpecialColumn (r : ρ) (i : α) : α :=
  X.outer.first.fiberColumn (X.resolutionSpecialLabel r) i

@[simp] private theorem first_resolutionSpecialColumn (r : ρ) (i : α) :
    X.outer.first.symbol i (X.resolutionSpecialColumn r i) =
      X.resolutionSpecialLabel r := by
  simp [resolutionSpecialColumn]

@[simp] private theorem split_first_resolutionSpecialColumn (r : ρ) (i : α) :
    X.split (X.outer.first.symbol i (X.resolutionSpecialColumn r i)) =
      Sum.inr r := by
  simp [resolutionSpecialLabel]

private theorem resolutionSpecialColumn_eq_of_split {i j : α} (r : ρ)
    (h : X.split (X.outer.first.symbol i j) = Sum.inr r) :
    X.resolutionSpecialColumn r i = j := by
  apply (X.outer.first.row_bijective i).injective
  apply X.split.injective
  rw [X.split_first_resolutionSpecialColumn, h]

/-- The unique cell in the intersection of the special first fiber `r` and
the second fiber `q`. -/
private noncomputable def resolutionIntersection (r : ρ) (q : α) : α × α :=
  Classical.choose
    (X.outer.existsUnique_intersection (X.resolutionSpecialLabel r) q)

@[simp] private theorem resolutionIntersection_first (r : ρ) (q : α) :
    X.outer.first.symbol (X.resolutionIntersection r q).1
        (X.resolutionIntersection r q).2 = X.resolutionSpecialLabel r :=
  (Classical.choose_spec
    (X.outer.existsUnique_intersection (X.resolutionSpecialLabel r) q)).1.1

@[simp] private theorem resolutionIntersection_second (r : ρ) (q : α) :
    X.outer.second.symbol (X.resolutionIntersection r q).1
        (X.resolutionIntersection r q).2 = q :=
  (Classical.choose_spec
    (X.outer.existsUnique_intersection (X.resolutionSpecialLabel r) q)).1.2

@[simp] private theorem split_resolutionIntersection_first (r : ρ) (q : α) :
    X.split (X.outer.first.symbol (X.resolutionIntersection r q).1
      (X.resolutionIntersection r q).2) = Sum.inr r := by
  simp [resolutionSpecialLabel]

@[simp] private theorem fiberRow_resolutionIntersection (r : ρ) (q : α) :
    X.outer.first.fiberRow (X.resolutionSpecialLabel r)
        (X.resolutionIntersection r q).2 =
      (X.resolutionIntersection r q).1 := by
  apply (X.outer.first.col_bijective
    (X.resolutionIntersection r q).2).injective
  change X.outer.first.symbol
      (X.outer.first.fiberRow (X.resolutionSpecialLabel r)
        (X.resolutionIntersection r q).2)
      (X.resolutionIntersection r q).2 =
    X.outer.first.symbol (X.resolutionIntersection r q).1
      (X.resolutionIntersection r q).2
  rw [X.outer.first.symbol_fiberRow, X.resolutionIntersection_first]

private theorem eq_resolutionIntersection {i j : α} (r : ρ) (q : α)
    (hfirst : X.outer.first.symbol i j = X.resolutionSpecialLabel r)
    (hsecond : X.outer.second.symbol i j = q) :
    (i, j) = X.resolutionIntersection r q := by
  exact (Classical.choose_spec
    (X.outer.existsUnique_intersection
      (X.resolutionSpecialLabel r) q)).2 (i, j) ⟨hfirst, hsecond⟩

/-- Embed the columns of a pointed block into the global array.  Its `none`
column is precisely the boundary column indexed by that block. -/
private def embedPointedColumn (j : α) (r : ρ) :
    Option β → ((α × β) ⊕ ρ)
  | some l => Sum.inl (j, l)
  | none => Sum.inr r

private theorem pointed_someLabel_none_ne_none
    (P : PointedMaximalRQLS β) (e : β) :
    P.full.resolution.column (some e) none ≠ none := by
  intro h
  have heq : P.full.resolution.column (some e) none =
      P.full.resolution.column none none := h.trans P.hole_transversal.symm
  have := (P.full.resolution.covers none).injective heq
  simp at this

private theorem pointed_incomplete_lastCoord_zero
    (P : PointedMaximalRQLS β) (k : β) :
    P.full.square.entry (some k) (some (P.incompleteColumn k)) none = 0 := by
  have h := P.full.resolution.orthonormal none none (some k)
  rw [if_neg (by simp)] at h
  change dot
    (P.full.square.entry none (P.full.resolution.column none none))
    (P.full.square.entry (some k)
      (P.full.resolution.column none (some k))) = 0 at h
  rw [P.hole_transversal, P.hole_entry,
    PointedMaximalRQLS.dot_basis_left] at h
  rw [← P.incompleteColumn_some] at h
  exact h

/-- Raw column selector for the transversals `R(q,e)` of Construction 4.6. -/
private noncomputable def ordinaryColumnFun (q : α) (e : β) :
    ((α × β) ⊕ ρ) → ((α × β) ⊕ ρ)
  | Sum.inl (i, k) =>
      let j := X.outer.second.fiberColumn q i
      match X.split (X.outer.first.symbol i j) with
      | Sum.inl g => Sum.inl
          (j, (X.ordinary.copy g).resolution.column e k)
      | Sum.inr r => embedPointedColumn j r
          ((X.special.copy r).full.resolution.column (some e) (some k))
  | Sum.inr r =>
      let cell := X.resolutionIntersection r q
      embedPointedColumn cell.2 r
        ((X.special.copy r).full.resolution.column (some e) none)

/-- Raw column selector for the transversals `S(r)` of Construction 4.6. -/
private noncomputable def incompleteColumnFun (r : ρ) :
    ((α × β) ⊕ ρ) → ((α × β) ⊕ ρ)
  | Sum.inl (i, k) => Sum.inl
      (X.resolutionSpecialColumn r i,
        (X.special.copy r).incompleteColumn k)
  | Sum.inr s => Sum.inr (X.exceptional.resolution.column r s)

private theorem alongSecond_row_eq {q : α} {i i' : α}
    (hfirst : X.outer.first.symbol i (X.outer.second.fiberColumn q i) =
      X.outer.first.symbol i' (X.outer.second.fiberColumn q i')) : i = i' := by
  exact (X.outer.first_second hfirst (by simp)).1

private theorem intersection_row_eq_of_column_eq (r s : ρ) (q : α)
    (hcol : (X.resolutionIntersection r q).2 =
      (X.resolutionIntersection s q).2) :
    (X.resolutionIntersection r q).1 =
      (X.resolutionIntersection s q).1 := by
  apply (X.outer.second.col_bijective
    (X.resolutionIntersection s q).2).injective
  calc
    X.outer.second.symbol (X.resolutionIntersection r q).1
        (X.resolutionIntersection s q).2 =
        X.outer.second.symbol (X.resolutionIntersection r q).1
          (X.resolutionIntersection r q).2 := by rw [hcol]
    _ = q := X.resolutionIntersection_second r q
    _ = X.outer.second.symbol (X.resolutionIntersection s q).1
          (X.resolutionIntersection s q).2 :=
      (X.resolutionIntersection_second s q).symm

private theorem intersection_label_eq_of_column_eq (r s : ρ) (q : α)
    (hcol : (X.resolutionIntersection r q).2 =
      (X.resolutionIntersection s q).2) : r = s := by
  have hrow := X.intersection_row_eq_of_column_eq r s q hcol
  have hfirst : X.resolutionSpecialLabel r = X.resolutionSpecialLabel s := by
    rw [← X.resolutionIntersection_first r q,
      ← X.resolutionIntersection_first s q, hrow, hcol]
  have hs := congrArg X.split hfirst
  simpa [resolutionSpecialLabel] using hs

private theorem ordinaryColumnFun_top_ne_bottom (q : α) (e : β)
    (i : α) (k : β) (s : ρ) :
    X.ordinaryColumnFun q e (Sum.inl (i, k)) ≠
      X.ordinaryColumnFun q e (Sum.inr s) := by
  classical
  intro h
  cases hkind : X.split
      (X.outer.first.symbol i (X.outer.second.fiberColumn q i)) with
  | inl g =>
      cases hc : (X.special.copy s).full.resolution.column (some e) none with
      | none =>
          exact (pointed_someLabel_none_ne_none
            (X.special.copy s) e hc)
      | some l =>
          simp only [ordinaryColumnFun, hkind, hc, embedPointedColumn,
            Sum.inl.injEq, Prod.mk.injEq] at h
          have hi : i = (X.resolutionIntersection s q).1 := by
            apply (X.outer.second.col_bijective
              (X.outer.second.fiberColumn q i)).injective
            simp only [X.outer.second.symbol_fiberColumn]
            rw [h.1]
            simp
          have hbad : X.split
              (X.outer.first.symbol i
                (X.outer.second.fiberColumn q i)) = Sum.inr s := by
            rw [h.1, hi]
            exact X.split_resolutionIntersection_first s q
          rw [hkind] at hbad
          simp at hbad
  | inr r =>
      cases hc : (X.special.copy r).full.resolution.column
          (some e) (some k) with
      | none =>
          cases hc' : (X.special.copy s).full.resolution.column
              (some e) none with
          | none =>
              exact pointed_someLabel_none_ne_none
                (X.special.copy s) e hc'
          | some l' =>
              simp [ordinaryColumnFun, hkind, hc, hc',
                embedPointedColumn] at h
      | some l =>
          cases hc' : (X.special.copy s).full.resolution.column
              (some e) none with
          | none =>
              exact (pointed_someLabel_none_ne_none
                (X.special.copy s) e hc')
          | some l' =>
              simp only [ordinaryColumnFun, hkind, hc, hc',
                embedPointedColumn, Sum.inl.injEq, Prod.mk.injEq] at h
              have hi : i = (X.resolutionIntersection s q).1 := by
                apply (X.outer.second.col_bijective
                  (X.outer.second.fiberColumn q i)).injective
                simp only [X.outer.second.symbol_fiberColumn]
                rw [h.1]
                simp
              have hrs : r = s := by
                have hlabels : (Sum.inr r : γ ⊕ ρ) = Sum.inr s := by
                  have hj : X.outer.second.fiberColumn q
                      (X.resolutionIntersection s q).1 =
                      (X.resolutionIntersection s q).2 := by
                    simpa only [X.resolutionIntersection_second] using
                      X.outer.second.fiberColumn_symbol
                        (X.resolutionIntersection s q).1
                        (X.resolutionIntersection s q).2
                  calc
                    Sum.inr r = X.split
                        (X.outer.first.symbol i
                          (X.outer.second.fiberColumn q i)) := hkind.symm
                    _ = X.split
                        (X.outer.first.symbol
                          (X.resolutionIntersection s q).1
                          (X.resolutionIntersection s q).2) := by
                            rw [hi, hj]
                    _ = Sum.inr s := X.split_resolutionIntersection_first s q
                exact Sum.inr.inj hlabels
              subst s
              have hrows : (some k : Option β) = none := by
                apply ((X.special.copy r).full.resolution.column
                  (some e)).injective
                rw [hc, hc', h.2]
              simp at hrows

private theorem ordinaryColumnFun_injective (q : α) (e : β) :
    Function.Injective (X.ordinaryColumnFun q e) := by
  classical
  intro a b h
  rcases a with ⟨i, k⟩ | r <;> rcases b with ⟨i', k'⟩ | s
  · cases hkind : X.split
        (X.outer.first.symbol i (X.outer.second.fiberColumn q i)) with
    | inl g =>
        cases hkind' : X.split
            (X.outer.first.symbol i' (X.outer.second.fiberColumn q i')) with
        | inl g' =>
            simp only [ordinaryColumnFun, hkind, hkind', Sum.inl.injEq,
              Prod.mk.injEq] at h
            have hi : i = i' :=
              (X.outer.second.fiberColumn_bijective q).injective h.1
            subst i'
            have hgg : g = g' := Sum.inl.inj (hkind.symm.trans hkind')
            subst g'
            have hk : k = k' :=
              ((X.ordinary.copy g).resolution.column e).injective h.2
            exact congrArg Sum.inl (Prod.ext rfl hk)
        | inr s =>
            cases hc : (X.special.copy s).full.resolution.column
                (some e) (some k') with
            | none =>
                simp [ordinaryColumnFun, hkind, hkind', hc,
                  embedPointedColumn] at h
            | some l =>
                simp only [ordinaryColumnFun, hkind, hkind', hc,
                  embedPointedColumn, Sum.inl.injEq, Prod.mk.injEq] at h
                have hi : i = i' :=
                  (X.outer.second.fiberColumn_bijective q).injective h.1
                subst i'
                have hbad : (Sum.inl g : γ ⊕ ρ) = Sum.inr s :=
                  hkind.symm.trans hkind'
                simp at hbad
    | inr r =>
        cases hkind' : X.split
            (X.outer.first.symbol i' (X.outer.second.fiberColumn q i')) with
        | inl g' =>
            cases hc : (X.special.copy r).full.resolution.column
                (some e) (some k) with
            | none =>
                simp [ordinaryColumnFun, hkind, hkind', hc,
                  embedPointedColumn] at h
            | some l =>
                simp only [ordinaryColumnFun, hkind, hkind', hc,
                  embedPointedColumn, Sum.inl.injEq, Prod.mk.injEq] at h
                have hi : i = i' :=
                  (X.outer.second.fiberColumn_bijective q).injective h.1
                subst i'
                have hbad : (Sum.inr r : γ ⊕ ρ) = Sum.inl g' :=
                  hkind.symm.trans hkind'
                simp at hbad
        | inr s =>
            cases hc : (X.special.copy r).full.resolution.column
                (some e) (some k) <;>
              cases hc' : (X.special.copy s).full.resolution.column
                (some e) (some k')
            · simp only [ordinaryColumnFun, hkind, hkind', hc, hc',
                embedPointedColumn, Sum.inr.injEq] at h
              have hrs : r = s := h
              subst s
              have hi : i = i' := X.alongSecond_row_eq
                (X.split.injective (hkind.trans hkind'.symm))
              subst i'
              have hkopt : (some k : Option β) = some k' := by
                apply ((X.special.copy r).full.resolution.column
                  (some e)).injective
                rw [hc, hc']
              exact congrArg Sum.inl (Prod.ext rfl (Option.some.inj hkopt))
            · simp [ordinaryColumnFun, hkind, hkind', hc, hc',
                embedPointedColumn] at h
            · simp [ordinaryColumnFun, hkind, hkind', hc, hc',
                embedPointedColumn] at h
            · simp only [ordinaryColumnFun, hkind, hkind', hc, hc',
                embedPointedColumn, Sum.inl.injEq, Prod.mk.injEq] at h
              have hi : i = i' :=
                (X.outer.second.fiberColumn_bijective q).injective h.1
              subst i'
              have hrs : r = s := Sum.inr.inj (hkind.symm.trans hkind')
              subst s
              have hkopt : (some k : Option β) = some k' := by
                apply ((X.special.copy r).full.resolution.column
                  (some e)).injective
                rw [hc, hc', h.2]
              exact congrArg Sum.inl (Prod.ext rfl (Option.some.inj hkopt))
  · exact False.elim (X.ordinaryColumnFun_top_ne_bottom q e i k s h)
  · exact False.elim (X.ordinaryColumnFun_top_ne_bottom q e i' k' r h.symm)
  · cases hc : (X.special.copy r).full.resolution.column (some e) none with
    | none =>
        exact False.elim
          (pointed_someLabel_none_ne_none (X.special.copy r) e hc)
    | some l =>
      cases hc' : (X.special.copy s).full.resolution.column (some e) none with
      | none =>
          exact False.elim
            (pointed_someLabel_none_ne_none (X.special.copy s) e hc')
      | some l' =>
          simp only [ordinaryColumnFun, hc, hc', embedPointedColumn,
            Sum.inl.injEq, Prod.mk.injEq] at h
          have hrs := X.intersection_label_eq_of_column_eq r s q h.1
          subst s
          rfl

private theorem ordinaryColumnFun_bijective (q : α) (e : β) :
    Function.Bijective (X.ordinaryColumnFun q e) :=
  (Fintype.bijective_iff_injective_and_card
    (X.ordinaryColumnFun q e)).2 ⟨X.ordinaryColumnFun_injective q e, by simp⟩

private theorem incompleteColumnFun_bijective (r : ρ) :
    Function.Bijective (X.incompleteColumnFun r) := by
  exact (Fintype.bijective_iff_injective_and_card
      (X.incompleteColumnFun r)).2 ⟨by
        intro a b h
        rcases a with ⟨i, k⟩ | s <;> rcases b with ⟨i', k'⟩ | s'
        · simp only [incompleteColumnFun, Sum.inl.injEq, Prod.mk.injEq] at h
          have hi : i = i' :=
            (X.outer.first.fiberColumn_bijective
              (X.resolutionSpecialLabel r)).injective h.1
          subst i'
          have hk : k = k' :=
            (X.special.copy r).incompleteColumn.injective h.2
          exact congrArg Sum.inl (Prod.ext rfl hk)
        · simp [incompleteColumnFun] at h
        · simp [incompleteColumnFun] at h
        · simp only [incompleteColumnFun, Sum.inr.injEq] at h
          exact congrArg Sum.inr
            ((X.exceptional.resolution.column r).injective h), by simp⟩

/-- The column selector for all `mn+h` transversals in Construction 4.6. -/
private noncomputable def resolutionColumnFun :
    ((α × β) ⊕ ρ) → ((α × β) ⊕ ρ) → ((α × β) ⊕ ρ)
  | Sum.inl (q, e) => X.ordinaryColumnFun q e
  | Sum.inr r => X.incompleteColumnFun r

private theorem resolutionColumnFun_bijective (t : (α × β) ⊕ ρ) :
    Function.Bijective (X.resolutionColumnFun t) := by
  rcases t with ⟨q, e⟩ | r
  · exact X.ordinaryColumnFun_bijective q e
  · exact X.incompleteColumnFun_bijective r

private noncomputable def resolutionCoverFun (row : (α × β) ⊕ ρ) :
    ((α × β) ⊕ ρ) → ((α × β) ⊕ ρ) :=
  fun t => X.resolutionColumnFun t row

private theorem resolutionCoverFun_surjective
    (row : (α × β) ⊕ ρ) :
    Function.Surjective (X.resolutionCoverFun row) := by
  classical
  intro target
  rcases row with ⟨i, k⟩ | s
  · rcases target with ⟨j, l⟩ | r
    · let q := X.outer.second.symbol i j
      have hj : X.outer.second.fiberColumn q i = j := by
        exact X.outer.second.fiberColumn_symbol i j
      cases hkind : X.split (X.outer.first.symbol i j) with
      | inl g =>
          obtain ⟨e, he⟩ :=
            ((X.ordinary.copy g).resolution.covers k).surjective l
          refine ⟨Sum.inl (q, e), ?_⟩
          simp [resolutionCoverFun, resolutionColumnFun,
            ordinaryColumnFun, hj, hkind, he]
      | inr r =>
          obtain ⟨t, ht⟩ :=
            ((X.special.copy r).full.resolution.covers (some k)).surjective
              (some l)
          cases t with
          | none =>
              refine ⟨Sum.inr r, ?_⟩
              have hjr : X.resolutionSpecialColumn r i = j :=
                X.resolutionSpecialColumn_eq_of_split r hkind
              have hl : (X.special.copy r).incompleteColumn k = l := by
                apply Option.some.inj
                calc
                  some ((X.special.copy r).incompleteColumn k) =
                      (X.special.copy r).full.resolution.column none (some k) :=
                    (X.special.copy r).incompleteColumn_some k
                  _ = some l := ht
              simp [resolutionCoverFun, resolutionColumnFun,
                incompleteColumnFun, hjr, hl]
          | some e =>
              refine ⟨Sum.inl (q, e), ?_⟩
              simp [resolutionCoverFun, resolutionColumnFun,
                ordinaryColumnFun, hj, hkind, ht, embedPointedColumn]
    · let j := X.resolutionSpecialColumn r i
      let q := X.outer.second.symbol i j
      obtain ⟨t, ht⟩ :=
        ((X.special.copy r).full.resolution.covers (some k)).surjective none
      cases t with
      | none =>
          exact False.elim (Option.some_ne_none _
            ((X.special.copy r).incompleteColumn_some k |>.trans ht))
      | some e =>
          refine ⟨Sum.inl (q, e), ?_⟩
          have hj : X.outer.second.fiberColumn q i = j :=
            X.outer.second.fiberColumn_symbol i j
          have hkind : X.split (X.outer.first.symbol i j) = Sum.inr r := by
            dsimp [j]
            exact X.split_first_resolutionSpecialColumn r i
          simp [resolutionCoverFun, resolutionColumnFun,
            ordinaryColumnFun, hj, hkind, ht, embedPointedColumn]
  · rcases target with ⟨j, l⟩ | r
    · let i := X.outer.first.fiberRow (X.resolutionSpecialLabel s) j
      let q := X.outer.second.symbol i j
      have hfirst : X.outer.first.symbol i j = X.resolutionSpecialLabel s := by
        exact X.outer.first.symbol_fiberRow (X.resolutionSpecialLabel s) j
      have hcell : (i, j) = X.resolutionIntersection s q :=
        X.eq_resolutionIntersection s q hfirst rfl
      obtain ⟨t, ht⟩ :=
        ((X.special.copy s).full.resolution.covers none).surjective (some l)
      cases t with
      | none =>
          have hbad : (none : Option β) = some l := by
            calc
              none = (X.special.copy s).full.resolution.column none none :=
                (X.special.copy s).hole_transversal.symm
              _ = some l := ht
          simp at hbad
      | some e =>
          refine ⟨Sum.inl (q, e), ?_⟩
          simp [resolutionCoverFun, resolutionColumnFun,
            ordinaryColumnFun, ← hcell, ht, embedPointedColumn]
    · obtain ⟨z, hz⟩ :=
        (X.exceptional.resolution.covers s).surjective r
      refine ⟨Sum.inr z, ?_⟩
      simp [resolutionCoverFun, resolutionColumnFun,
        incompleteColumnFun, hz]

private theorem resolutionCoverFun_bijective
    (row : (α × β) ⊕ ρ) :
    Function.Bijective (X.resolutionCoverFun row) :=
  (Fintype.bijective_iff_surjective_and_card
    (X.resolutionCoverFun row)).2
      ⟨X.resolutionCoverFun_surjective row, by simp⟩

/-- The vector selected by `R(q,e)`, written without the global column
case split.  This is the form used in the orthonormality calculation. -/
private noncomputable def ordinarySelected (q : α) (e : β) :
    ((α × β) ⊕ ρ) → Ket ((α × β) ⊕ ρ)
  | Sum.inl (i, k) =>
      let j := X.outer.second.fiberColumn q i
      match X.split (X.outer.first.symbol i j) with
      | Sum.inl g => extendedTensor (ρ := ρ)
          (basis (X.outer.base.symbol i j))
          ((X.ordinary.copy g).square.entry k
            ((X.ordinary.copy g).resolution.column e k))
      | Sum.inr r => parameterTensor r
          (basis (X.outer.base.symbol i j))
          ((X.special.copy r).full.square.entry (some k)
            ((X.special.copy r).full.resolution.column (some e) (some k)))
  | Sum.inr r =>
      let cell := X.resolutionIntersection r q
      parameterTensor r
        (basis (X.outer.base.symbol cell.1 cell.2))
        ((X.special.copy r).full.square.entry none
          ((X.special.copy r).full.resolution.column (some e) none))

/-- The vector selected by `S(r)`, again in its calculation-friendly form. -/
private noncomputable def incompleteSelected (r : ρ) :
    ((α × β) ⊕ ρ) → Ket ((α × β) ⊕ ρ)
  | Sum.inl (i, k) => parameterTensor r
      (basis (X.outer.base.symbol i (X.resolutionSpecialColumn r i)))
      ((X.special.copy r).full.square.entry (some k)
        (some ((X.special.copy r).incompleteColumn k)))
  | Sum.inr s => exceptionalKet (α := α) (β := β)
      (X.exceptional.square.entry s
        (X.exceptional.resolution.column r s))

private theorem squareEntry_ordinaryColumnFun (q : α) (e : β)
    (row : (α × β) ⊕ ρ) :
    X.square.entry row (X.ordinaryColumnFun q e row) =
      X.ordinarySelected q e row := by
  classical
  rcases row with ⟨i, k⟩ | r
  · cases hkind : X.split
        (X.outer.first.symbol i (X.outer.second.fiberColumn q i)) with
    | inl g =>
        simp [SingularProductData.square, ordinaryColumnFun,
          ordinarySelected, SingularProductData.squareEntry, hkind]
    | inr r =>
        have hj : X.resolutionSpecialColumn r i =
            X.outer.second.fiberColumn q i :=
          X.resolutionSpecialColumn_eq_of_split r hkind
        cases hc : (X.special.copy r).full.resolution.column
            (some e) (some k) with
        | none =>
            simp [SingularProductData.square, ordinaryColumnFun,
              ordinarySelected, SingularProductData.squareEntry, hkind, hc,
              embedPointedColumn]
            change parameterTensor r
                (basis (X.outer.base.symbol i
                  (X.resolutionSpecialColumn r i)))
                ((X.special.copy r).full.square.entry (some k) none) = _
            rw [hj]
        | some l =>
            simp [SingularProductData.square, ordinaryColumnFun,
              ordinarySelected, SingularProductData.squareEntry, hkind, hc,
              embedPointedColumn]
  · cases hc : (X.special.copy r).full.resolution.column (some e) none with
    | none =>
        exact False.elim
          (pointed_someLabel_none_ne_none (X.special.copy r) e hc)
    | some l =>
        simp [SingularProductData.square, ordinaryColumnFun,
          ordinarySelected, SingularProductData.squareEntry, hc,
          embedPointedColumn]
        change parameterTensor r
            (basis (X.outer.base.symbol
              (X.outer.first.fiberRow (X.resolutionSpecialLabel r)
                (X.resolutionIntersection r q).2)
              (X.resolutionIntersection r q).2))
            ((X.special.copy r).full.square.entry none (some l)) = _
        rw [X.fiberRow_resolutionIntersection]

private theorem squareEntry_incompleteColumnFun (r : ρ)
    (row : (α × β) ⊕ ρ) :
    X.square.entry row (X.incompleteColumnFun r row) =
      X.incompleteSelected r row := by
  classical
  rcases row with ⟨i, k⟩ | s
  · simp [SingularProductData.square, incompleteColumnFun,
      incompleteSelected, SingularProductData.squareEntry,
      resolutionSpecialColumn, resolutionSpecialLabel]
  · simp [SingularProductData.square, incompleteColumnFun,
      incompleteSelected, SingularProductData.squareEntry]

private theorem base_ne_along_first (r : ρ) {i i' : α} (hi : i ≠ i') :
    X.outer.base.symbol i (X.resolutionSpecialColumn r i) ≠
      X.outer.base.symbol i' (X.resolutionSpecialColumn r i') := by
  intro hbase
  have hfirst : X.outer.first.symbol i (X.resolutionSpecialColumn r i) =
      X.outer.first.symbol i' (X.resolutionSpecialColumn r i') := by simp
  exact hi (X.outer.base_first hbase hfirst).1

private theorem base_ne_along_second (q : α) {i i' : α} (hi : i ≠ i') :
    X.outer.base.symbol i (X.outer.second.fiberColumn q i) ≠
      X.outer.base.symbol i' (X.outer.second.fiberColumn q i') := by
  intro hbase
  have hsecond : X.outer.second.symbol i (X.outer.second.fiberColumn q i) =
      X.outer.second.symbol i' (X.outer.second.fiberColumn q i') := by simp
  exact hi (X.outer.base_second hbase hsecond).1

private theorem incomplete_projectedDot
    (P : PointedMaximalRQLS β) (k k' : β) :
    projectedDot
        (P.full.square.entry (some k) (some (P.incompleteColumn k)))
        (P.full.square.entry (some k') (some (P.incompleteColumn k'))) =
      if k = k' then 1 else 0 := by
  simpa [projectedDot, IsOrthonormal, dot] using
    P.incomplete_orthonormal k k'

private theorem incompleteSelected_orthonormal (r : ρ) :
    IsOrthonormal (X.incompleteSelected r) := by
  classical
  intro row row'
  rcases row with ⟨i, k⟩ | s <;> rcases row' with ⟨i', k'⟩ | s'
  · by_cases hi : i = i'
    · subst i'
      simp only [incompleteSelected]
      rw [dot_parameterTensor_same]
      · rw [dot_option_decompose,
          pointed_incomplete_lastCoord_zero,
          pointed_incomplete_lastCoord_zero,
          incomplete_projectedDot]
        simp
      · exact dot_basis_named_self _
    · have hb := X.base_ne_along_first r hi
      simp only [incompleteSelected]
      rw [dot_parameterTensor_basis, if_neg hb, if_pos rfl,
        pointed_incomplete_lastCoord_zero,
        pointed_incomplete_lastCoord_zero]
      simp [hi]
  · simp only [incompleteSelected]
    rw [dot_parameter_exceptional,
      pointed_incomplete_lastCoord_zero]
    simp
  · simp only [incompleteSelected]
    rw [dot_exceptional_parameter,
      pointed_incomplete_lastCoord_zero]
    simp
  · simp only [incompleteSelected]
    rw [dot_exceptionalKet,
      X.exceptional.resolution.orthonormal]
    simp

@[simp] private theorem fiberColumn_resolutionIntersection (r : ρ) (q : α) :
    X.outer.second.fiberColumn q (X.resolutionIntersection r q).1 =
      (X.resolutionIntersection r q).2 := by
  simpa only [X.resolutionIntersection_second] using
    X.outer.second.fiberColumn_symbol
      (X.resolutionIntersection r q).1 (X.resolutionIntersection r q).2

private theorem base_ne_top_intersection (q : α) (s : ρ) {i : α}
    (hi : i ≠ (X.resolutionIntersection s q).1) :
    X.outer.base.symbol i (X.outer.second.fiberColumn q i) ≠
      X.outer.base.symbol (X.resolutionIntersection s q).1
        (X.resolutionIntersection s q).2 := by
  intro hbase
  have hsecond : X.outer.second.symbol i
      (X.outer.second.fiberColumn q i) =
      X.outer.second.symbol (X.resolutionIntersection s q).1
        (X.resolutionIntersection s q).2 := by simp
  exact hi (X.outer.base_second hbase hsecond).1

private theorem special_ne_top_intersection (q : α) (s r : ρ) {i : α}
    (hi : i ≠ (X.resolutionIntersection s q).1)
    (hkind : X.split
      (X.outer.first.symbol i (X.outer.second.fiberColumn q i)) =
        Sum.inr r) : r ≠ s := by
  intro hrs
  subst s
  have hfirst : X.outer.first.symbol i
      (X.outer.second.fiberColumn q i) =
      X.outer.first.symbol (X.resolutionIntersection r q).1
        (X.resolutionIntersection r q).2 := by
    apply X.split.injective
    rw [hkind, X.split_resolutionIntersection_first]
  have hsecond : X.outer.second.symbol i
      (X.outer.second.fiberColumn q i) =
      X.outer.second.symbol (X.resolutionIntersection r q).1
        (X.resolutionIntersection r q).2 := by simp
  exact hi (X.outer.first_second hfirst hsecond).1

private theorem base_ne_intersections (q : α) {r s : ρ} (hrs : r ≠ s) :
    X.outer.base.symbol (X.resolutionIntersection r q).1
        (X.resolutionIntersection r q).2 ≠
      X.outer.base.symbol (X.resolutionIntersection s q).1
        (X.resolutionIntersection s q).2 := by
  intro hbase
  have hsecond : X.outer.second.symbol (X.resolutionIntersection r q).1
      (X.resolutionIntersection r q).2 =
      X.outer.second.symbol (X.resolutionIntersection s q).1
        (X.resolutionIntersection s q).2 := by simp
  rcases X.outer.base_second hbase hsecond with ⟨hi, hj⟩
  have hfirst : X.resolutionSpecialLabel r = X.resolutionSpecialLabel s := by
    rw [← X.resolutionIntersection_first r q,
      ← X.resolutionIntersection_first s q, hi, hj]
  have hlabels := congrArg X.split hfirst
  exact hrs (by simpa [resolutionSpecialLabel] using hlabels)

private theorem ordinarySelected_top_bottom_dot (q : α) (e : β)
    (i : α) (k : β) (s : ρ) :
    dot (X.ordinarySelected q e (Sum.inl (i, k)))
      (X.ordinarySelected q e (Sum.inr s)) = 0 := by
  classical
  by_cases hi : i = (X.resolutionIntersection s q).1
  · subst i
    have hkind : X.split
        (X.outer.first.symbol (X.resolutionIntersection s q).1
          (X.outer.second.fiberColumn q
            (X.resolutionIntersection s q).1)) =
          Sum.inr s := by
      rw [X.fiberColumn_resolutionIntersection]
      exact X.split_resolutionIntersection_first s q
    simp only [ordinarySelected, hkind]
    rw [X.fiberColumn_resolutionIntersection, dot_parameterTensor_same,
      (X.special.copy s).full.resolution.orthonormal]
    · simp
    · exact dot_basis_named_self _
  · have hb := X.base_ne_top_intersection q s hi
    cases hkind : X.split
        (X.outer.first.symbol i (X.outer.second.fiberColumn q i)) with
    | inl g =>
        simp only [ordinarySelected, hkind]
        rw [dot_extended_parameter, dot_basis_named, if_neg hb]
        simp
    | inr r =>
        have hrs := X.special_ne_top_intersection q s r hi hkind
        simp only [ordinarySelected, hkind]
        rw [dot_parameterTensor_basis, if_neg hb, if_neg hrs]
        simp

private theorem ordinarySelected_orthonormal (q : α) (e : β) :
    IsOrthonormal (X.ordinarySelected q e) := by
  classical
  intro row row'
  rcases row with ⟨i, k⟩ | r <;> rcases row' with ⟨i', k'⟩ | s
  · by_cases hi : i = i'
    · subst i'
      cases hkind : X.split
          (X.outer.first.symbol i (X.outer.second.fiberColumn q i)) with
      | inl g =>
          simp only [ordinarySelected, hkind]
          rw [dot_extendedTensor, dot_basis_named_self,
            (X.ordinary.copy g).resolution.orthonormal]
          simp
      | inr r =>
          simp only [ordinarySelected, hkind]
          rw [dot_parameterTensor_same,
            (X.special.copy r).full.resolution.orthonormal]
          · simp
          · exact dot_basis_named_self _
    · have hb := X.base_ne_along_second q hi
      cases hkind : X.split
          (X.outer.first.symbol i (X.outer.second.fiberColumn q i)) <;>
        cases hkind' : X.split
          (X.outer.first.symbol i' (X.outer.second.fiberColumn q i'))
      · simp only [ordinarySelected, hkind, hkind']
        rw [dot_extendedTensor, dot_basis_named, if_neg hb]
        simp [hi]
      · simp only [ordinarySelected, hkind, hkind']
        rw [dot_extended_parameter, dot_basis_named, if_neg hb]
        simp [hi]
      · simp only [ordinarySelected, hkind, hkind']
        rw [dot_parameter_extended, dot_basis_named, if_neg hb]
        simp [hi]
      · rename_i r s
        have hrs : r ≠ s := by
          intro h
          subst s
          exact hi (X.alongSecond_row_eq
            (X.split.injective (hkind.trans hkind'.symm)))
        simp only [ordinarySelected, hkind, hkind']
        rw [dot_parameterTensor_basis, if_neg hb, if_neg hrs]
        simp [hi]
  · simpa using X.ordinarySelected_top_bottom_dot q e i k s
  · rw [SingularProductData.dot_conj_symm]
    simpa using congrArg conj
      (X.ordinarySelected_top_bottom_dot q e i' k' r)
  · by_cases hrs : r = s
    · subst s
      simp only [ordinarySelected]
      rw [dot_parameterTensor_same,
        (X.special.copy r).full.resolution.orthonormal]
      · simp
      · exact dot_basis_named_self _
    · have hb := X.base_ne_intersections q hrs
      simp only [ordinarySelected]
      rw [dot_parameterTensor_basis, if_neg hb, if_neg hrs]
      simp [hrs]

/-- The resolution asserted by Construction 4.6 for the singular direct
product.  The left labels are the `R(q,e)` transversals and the right labels
are the `S(r)` transversals in the paper. -/
noncomputable def resolution : X.square.Resolution where
  column t := Equiv.ofBijective (X.resolutionColumnFun t)
    (X.resolutionColumnFun_bijective t)
  covers row := by
    change Function.Bijective (X.resolutionCoverFun row)
    exact X.resolutionCoverFun_bijective row
  orthonormal t := by
    rcases t with ⟨q, e⟩ | r
    · intro row row'
      change dot
          (X.square.entry row (X.ordinaryColumnFun q e row))
          (X.square.entry row' (X.ordinaryColumnFun q e row')) =
        if row = row' then 1 else 0
      rw [X.squareEntry_ordinaryColumnFun,
        X.squareEntry_ordinaryColumnFun]
      exact X.ordinarySelected_orthonormal q e row row'
    · intro row row'
      change dot
          (X.square.entry row (X.incompleteColumnFun r row))
          (X.square.entry row' (X.incompleteColumnFun r row')) =
        if row = row' then 1 else 0
      rw [X.squareEntry_incompleteColumnFun,
        X.squareEntry_incompleteColumnFun]
      exact X.incompleteSelected_orthonormal r row row'

end SingularProductData

end LeanCo.QuantumLatin
