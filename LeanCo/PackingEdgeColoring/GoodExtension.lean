import LeanCo.PackingEdgeColoring.GoodColoring

/-!
# Local support for preserving good-colouring conditions

Recolouring arguments change a colouring on a small set of edges.  This
file records exactly which vertices can notice such a change.  Matching
colour visibility only depends on changed edges incident with the vertex;
induced-colour visibility only depends on changed edges having an endpoint
equal or adjacent to the vertex.

The resulting locality rules reduce preservation of Conditions I and 2 to
checking the affected degree-two vertices.  They make no assumptions about
how the colours on the support were chosen, so they apply uniformly to
patches and to single-edge recolourings.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open SimpleGraph

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

/-! ## Change supports and their vertex influence domains -/

/-- Two colourings agree on every edge outside `S`. -/
def ColoringsAgreeOff {k : ℕ} (S : Set G.edgeSet)
    (old new : G.edgeSet → OneTwoColor k) : Prop :=
  ∀ e, e ∉ S → old e = new e

/-- A change on `S` can affect whether `u` sees the matching colour exactly
when some edge of `S` is incident with `u`. -/
def MatchingAffectedBy (S : Set G.edgeSet) (u : V) : Prop :=
  ∃ e, e ∈ S ∧ u ∈ (e : Sym2 V)

/-- A change on `S` can affect whether `u` sees an induced colour exactly
when some edge of `S` has an endpoint equal or adjacent to `u`. -/
def InducedAffectedBy (S : Set G.edgeSet) (u : V) : Prop :=
  ∃ e, e ∈ S ∧ ∃ v, v ∈ (e : Sym2 V) ∧ (u = v ∨ G.Adj u v)

/-- The union of the two influence domains relevant to the palette
condition at a degree-two vertex. -/
def PaletteAffectedBy (S : Set G.edgeSet) (u : V) : Prop :=
  MatchingAffectedBy G S u ∨ InducedAffectedBy G S u

theorem matchingAffectedBy_mono {S T : Set G.edgeSet} (hST : S ⊆ T)
    {u : V} : MatchingAffectedBy G S u → MatchingAffectedBy G T u := by
  rintro ⟨e, heS, hue⟩
  exact ⟨e, hST heS, hue⟩

theorem inducedAffectedBy_mono {S T : Set G.edgeSet} (hST : S ⊆ T)
    {u : V} : InducedAffectedBy G S u → InducedAffectedBy G T u := by
  rintro ⟨e, heS, v, hve, huv⟩
  exact ⟨e, hST heS, v, hve, huv⟩

/-- Incidence is the distance-zero part of the induced-colour influence
domain. -/
theorem matchingAffectedBy_imp_inducedAffectedBy {S : Set G.edgeSet}
    {u : V} :
    MatchingAffectedBy G S u → InducedAffectedBy G S u := by
  rintro ⟨e, heS, hue⟩
  exact ⟨e, heS, u, hue, Or.inl rfl⟩

theorem paletteAffectedBy_mono {S T : Set G.edgeSet} (hST : S ⊆ T)
    {u : V} : PaletteAffectedBy G S u → PaletteAffectedBy G T u := by
  rintro (h | h)
  · exact Or.inl (matchingAffectedBy_mono G hST h)
  · exact Or.inr (inducedAffectedBy_mono G hST h)

theorem paletteAffectedBy_iff_inducedAffectedBy {S : Set G.edgeSet}
    {u : V} :
    PaletteAffectedBy G S u ↔ InducedAffectedBy G S u := by
  constructor
  · rintro (h | h)
    · exact matchingAffectedBy_imp_inducedAffectedBy G h
    · exact h
  · exact Or.inr

@[simp] theorem matchingAffectedBy_empty (u : V) :
    ¬ MatchingAffectedBy G ∅ u := by
  simp [MatchingAffectedBy]

@[simp] theorem inducedAffectedBy_empty (u : V) :
    ¬ InducedAffectedBy G ∅ u := by
  simp [InducedAffectedBy]

@[simp] theorem paletteAffectedBy_empty (u : V) :
    ¬ PaletteAffectedBy G ∅ u := by
  simp [PaletteAffectedBy]

@[simp] theorem matchingAffectedBy_singleton (e : G.edgeSet) (u : V) :
    MatchingAffectedBy G ({e} : Set G.edgeSet) u ↔ u ∈ (e : Sym2 V) := by
  simp [MatchingAffectedBy]

@[simp] theorem inducedAffectedBy_singleton (e : G.edgeSet) (u : V) :
    InducedAffectedBy G ({e} : Set G.edgeSet) u ↔
      ∃ v, v ∈ (e : Sym2 V) ∧ (u = v ∨ G.Adj u v) := by
  simp [InducedAffectedBy]

@[simp] theorem paletteAffectedBy_singleton (e : G.edgeSet) (u : V) :
    PaletteAffectedBy G ({e} : Set G.edgeSet) u ↔
      u ∈ (e : Sym2 V) ∨
        ∃ v, v ∈ (e : Sym2 V) ∧ (u = v ∨ G.Adj u v) := by
  simp [PaletteAffectedBy]

/-! ## Visibility is unchanged outside the influence domain -/

theorem vertexSeesMatching_iff_of_not_affected {k : ℕ}
    {S : Set G.edgeSet} {old new : G.edgeSet → OneTwoColor k}
    (hagree : ColoringsAgreeOff G S old new) {u : V}
    (hu : ¬ MatchingAffectedBy G S u) :
    VertexSeesMatching G old u ↔ VertexSeesMatching G new u := by
  rw [vertexSeesMatching_iff, vertexSeesMatching_iff]
  constructor
  · rintro ⟨e, he, hue⟩
    have heS : e ∉ S := fun heS => hu ⟨e, heS, hue⟩
    exact ⟨e, (hagree e heS).symm.trans he, hue⟩
  · rintro ⟨e, he, hue⟩
    have heS : e ∉ S := fun heS => hu ⟨e, heS, hue⟩
    exact ⟨e, (hagree e heS).trans he, hue⟩

theorem vertexSeesInduced_iff_of_not_affected {k : ℕ}
    {S : Set G.edgeSet} {old new : G.edgeSet → OneTwoColor k}
    (hagree : ColoringsAgreeOff G S old new) {u : V}
    (hu : ¬ InducedAffectedBy G S u) (i : Fin k) :
    VertexSeesInduced G old u i ↔ VertexSeesInduced G new u i := by
  rw [vertexSeesInduced_iff, vertexSeesInduced_iff]
  constructor
  · rintro ⟨e, he, v, hve, huv⟩
    have heS : e ∉ S := fun heS => hu ⟨e, heS, v, hve, huv⟩
    exact ⟨e, (hagree e heS).symm.trans he, v, hve, huv⟩
  · rintro ⟨e, he, v, hve, huv⟩
    have heS : e ∉ S := fun heS => hu ⟨e, heS, v, hve, huv⟩
    exact ⟨e, (hagree e heS).trans he, v, hve, huv⟩

/-! Finset-facing wrappers.  The underlying theorem remains set-based so
the same API also handles infinite supports when useful. -/

theorem vertexSeesMatching_iff_of_not_affected_finset {k : ℕ}
    (S : Finset G.edgeSet) {old new : G.edgeSet → OneTwoColor k}
    (hagree : ∀ e, e ∉ S → old e = new e) {u : V}
    (hu : ¬ MatchingAffectedBy G (S : Set G.edgeSet) u) :
    VertexSeesMatching G old u ↔ VertexSeesMatching G new u := by
  apply vertexSeesMatching_iff_of_not_affected G
    (S := (S : Set G.edgeSet)) (old := old) (new := new) _ hu
  intro e he
  exact hagree e (by simpa using he)

theorem vertexSeesInduced_iff_of_not_affected_finset {k : ℕ}
    (S : Finset G.edgeSet) {old new : G.edgeSet → OneTwoColor k}
    (hagree : ∀ e, e ∉ S → old e = new e) {u : V}
    (hu : ¬ InducedAffectedBy G (S : Set G.edgeSet) u) (i : Fin k) :
    VertexSeesInduced G old u i ↔ VertexSeesInduced G new u i := by
  apply vertexSeesInduced_iff_of_not_affected G
    (S := (S : Set G.edgeSet)) (old := old) (new := new) _ hu i
  intro e he
  exact hagree e (by simpa using he)

/-! ## Local verification of the palette conditions -/

section Finite

variable [Fintype V] [DecidableRel G.Adj]

/-- To preserve the common palette condition, it is enough to check the
new condition at affected degree-two vertices. -/
theorem TwoVertexPaletteCondition.of_agreeOff {k : ℕ}
    {S : Set G.edgeSet} {old new : G.edgeSet → OneTwoColor k}
    (hold : TwoVertexPaletteCondition G old)
    (hagree : ColoringsAgreeOff G S old new)
    (hcheck : ∀ u, IsTwoVertex G u → PaletteAffectedBy G S u →
      VertexSeesMatching G new u →
      ¬ ∀ i : Fin k, VertexSeesInduced G new u i) :
    TwoVertexPaletteCondition G new := by
  intro u hu hmatch hall
  by_cases haffect : PaletteAffectedBy G S u
  · exact hcheck u hu haffect hmatch hall
  · have hmatchUnaffected : ¬ MatchingAffectedBy G S u :=
      fun h => haffect (Or.inl h)
    have hinducedUnaffected : ¬ InducedAffectedBy G S u :=
      fun h => haffect (Or.inr h)
    apply hold u hu
    · exact (vertexSeesMatching_iff_of_not_affected G hagree
        hmatchUnaffected).mpr hmatch
    · intro i
      exact (vertexSeesInduced_iff_of_not_affected G hagree
        hinducedUnaffected i).mpr (hall i)

/-- Finset-facing version of the local palette verification rule. -/
theorem TwoVertexPaletteCondition.of_agreeOff_finset {k : ℕ}
    (S : Finset G.edgeSet) {old new : G.edgeSet → OneTwoColor k}
    (hold : TwoVertexPaletteCondition G old)
    (hagree : ∀ e, e ∉ S → old e = new e)
    (hcheck : ∀ u, IsTwoVertex G u →
      PaletteAffectedBy G (S : Set G.edgeSet) u →
      VertexSeesMatching G new u →
      ¬ ∀ i : Fin k, VertexSeesInduced G new u i) :
    TwoVertexPaletteCondition G new := by
  apply hold.of_agreeOff (S := (S : Set G.edgeSet))
  · intro e he
    exact hagree e (by simpa using he)
  · exact hcheck

/-- Condition I only needs to be rechecked at affected degree-two
vertices. -/
theorem ConditionI.of_agreeOff {S : Set G.edgeSet}
    {old new : G.edgeSet → OneTwoColor 5}
    (hold : ConditionI G old)
    (hagree : ColoringsAgreeOff G S old new)
    (hcheck : ∀ u, IsTwoVertex G u → PaletteAffectedBy G S u →
      VertexSeesMatching G new u →
      ¬ ∀ i : Fin 5, VertexSeesInduced G new u i) :
    ConditionI G new :=
  TwoVertexPaletteCondition.of_agreeOff G hold hagree hcheck

/-- Condition 2 only needs to be rechecked at affected degree-two
vertices. -/
theorem ConditionTwo.of_agreeOff {S : Set G.edgeSet}
    {old new : G.edgeSet → OneTwoColor 4}
    (hold : ConditionTwo G old)
    (hagree : ColoringsAgreeOff G S old new)
    (hcheck : ∀ u, IsTwoVertex G u → PaletteAffectedBy G S u →
      VertexSeesMatching G new u →
      ¬ ∀ i : Fin 4, VertexSeesInduced G new u i) :
    ConditionTwo G new :=
  TwoVertexPaletteCondition.of_agreeOff G hold hagree hcheck

end Finite

/-! ## Patching a set of edges -/

section Patch

variable {S : Set G.edgeSet} [DecidablePred (· ∈ S)]

/-- A patch is definitionally unchanged off its support. -/
theorem coloringsAgreeOff_patchColoring {k : ℕ}
    (old replacement : G.edgeSet → OneTwoColor k) :
    ColoringsAgreeOff G S old (patchColoring G S old replacement) := by
  intro e he
  simp [patchColoring, he]

section Finite

variable [Fintype V] [DecidableRel G.Adj]

theorem TwoVertexPaletteCondition.patch_of_local {k : ℕ}
    {old replacement : G.edgeSet → OneTwoColor k}
    (hold : TwoVertexPaletteCondition G old)
    (hcheck : ∀ u, IsTwoVertex G u → PaletteAffectedBy G S u →
      VertexSeesMatching G (patchColoring G S old replacement) u →
      ¬ ∀ i : Fin k,
        VertexSeesInduced G (patchColoring G S old replacement) u i) :
    TwoVertexPaletteCondition G (patchColoring G S old replacement) :=
  TwoVertexPaletteCondition.of_agreeOff G hold
    (coloringsAgreeOff_patchColoring G old replacement) hcheck

theorem ConditionI.patch_of_local
    {old replacement : G.edgeSet → OneTwoColor 5}
    (hold : ConditionI G old)
    (hcheck : ∀ u, IsTwoVertex G u → PaletteAffectedBy G S u →
      VertexSeesMatching G (patchColoring G S old replacement) u →
      ¬ ∀ i : Fin 5,
        VertexSeesInduced G (patchColoring G S old replacement) u i) :
    ConditionI G (patchColoring G S old replacement) :=
  TwoVertexPaletteCondition.patch_of_local G hold hcheck

theorem ConditionTwo.patch_of_local
    {old replacement : G.edgeSet → OneTwoColor 4}
    (hold : ConditionTwo G old)
    (hcheck : ∀ u, IsTwoVertex G u → PaletteAffectedBy G S u →
      VertexSeesMatching G (patchColoring G S old replacement) u →
      ¬ ∀ i : Fin 4,
        VertexSeesInduced G (patchColoring G S old replacement) u i) :
    ConditionTwo G (patchColoring G S old replacement) :=
  TwoVertexPaletteCondition.patch_of_local G hold hcheck

end Finite

end Patch

/-! ## Single-edge recolouring specializations -/

section Recolor

variable [DecidableEq G.edgeSet]

theorem coloringsAgreeOff_recolor {k : ℕ}
    (colour : G.edgeSet → OneTwoColor k) (e : G.edgeSet)
    (a : OneTwoColor k) :
    ColoringsAgreeOff G ({e} : Set G.edgeSet) colour
      (recolor G colour e a) := by
  intro f hf
  exact (recolor_ne G colour a (by simpa using hf)).symm

theorem vertexSeesMatching_recolor_iff_of_not_incident {k : ℕ}
    (colour : G.edgeSet → OneTwoColor k) (e : G.edgeSet)
    (a : OneTwoColor k) {u : V} (hu : u ∉ (e : Sym2 V)) :
    VertexSeesMatching G colour u ↔
      VertexSeesMatching G (recolor G colour e a) u := by
  apply vertexSeesMatching_iff_of_not_affected G
    (coloringsAgreeOff_recolor G colour e a)
  simpa using hu

theorem vertexSeesInduced_recolor_iff_of_far {k : ℕ}
    (colour : G.edgeSet → OneTwoColor k) (e : G.edgeSet)
    (a : OneTwoColor k) {u : V}
    (hu : ¬ ∃ v, v ∈ (e : Sym2 V) ∧ (u = v ∨ G.Adj u v)) (i : Fin k) :
    VertexSeesInduced G colour u i ↔
      VertexSeesInduced G (recolor G colour e a) u i := by
  apply vertexSeesInduced_iff_of_not_affected G
    (coloringsAgreeOff_recolor G colour e a)
  simpa using hu

section Finite

variable [Fintype V] [DecidableRel G.Adj]

theorem TwoVertexPaletteCondition.recolor_of_local {k : ℕ}
    {colour : G.edgeSet → OneTwoColor k} {e : G.edgeSet}
    {a : OneTwoColor k} (hold : TwoVertexPaletteCondition G colour)
    (hcheck : ∀ u, IsTwoVertex G u →
      PaletteAffectedBy G ({e} : Set G.edgeSet) u →
      VertexSeesMatching G (recolor G colour e a) u →
      ¬ ∀ i : Fin k, VertexSeesInduced G (recolor G colour e a) u i) :
    TwoVertexPaletteCondition G (recolor G colour e a) :=
  TwoVertexPaletteCondition.of_agreeOff G hold
    (coloringsAgreeOff_recolor G colour e a) hcheck

theorem ConditionI.recolor_of_local
    {colour : G.edgeSet → OneTwoColor 5} {e : G.edgeSet}
    {a : OneTwoColor 5} (hold : ConditionI G colour)
    (hcheck : ∀ u, IsTwoVertex G u →
      PaletteAffectedBy G ({e} : Set G.edgeSet) u →
      VertexSeesMatching G (recolor G colour e a) u →
      ¬ ∀ i : Fin 5, VertexSeesInduced G (recolor G colour e a) u i) :
    ConditionI G (recolor G colour e a) :=
  TwoVertexPaletteCondition.recolor_of_local G hold hcheck

theorem ConditionTwo.recolor_of_local
    {colour : G.edgeSet → OneTwoColor 4} {e : G.edgeSet}
    {a : OneTwoColor 4} (hold : ConditionTwo G colour)
    (hcheck : ∀ u, IsTwoVertex G u →
      PaletteAffectedBy G ({e} : Set G.edgeSet) u →
      VertexSeesMatching G (recolor G colour e a) u →
      ¬ ∀ i : Fin 4, VertexSeesInduced G (recolor G colour e a) u i) :
    ConditionTwo G (recolor G colour e a) :=
  TwoVertexPaletteCondition.recolor_of_local G hold hcheck

end Finite

end Recolor

end

end LeanCo.PackingEdgeColoring
