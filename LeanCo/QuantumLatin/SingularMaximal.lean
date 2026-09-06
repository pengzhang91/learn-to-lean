import LeanCo.QuantumLatin.SingularProduct

/-!
# Maximality of the singular product

The published proof delegates this part to a classical singular-product
reference.  Here the three kinds of cells are classified explicitly and all
projective-collision cases are discharged from the separation hypotheses.
-/

namespace LeanCo.QuantumLatin

universe u v w x

variable {α : Type u} {β : Type v} {ρ : Type w} {γ : Type x}
  [Fintype α] [Fintype β] [Fintype ρ] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq ρ] [DecidableEq γ]

open SingularProductData

/-- Syntactic classification of all cells in the singular array. -/
inductive SingularCellDescriptor (α : Type u) (β : Type v)
    (ρ : Type w) (γ : Type x)
  | ordinary (g : γ) (i j : α) (k l : β)
  | parameter (r : ρ) (i j : α) (s t : Option β)
  | exceptional (r s : ρ)
  deriving DecidableEq

namespace SingularProductData

variable (X : SingularProductData (α := α) (β := β) (ρ := ρ) (γ := γ))

private noncomputable def cellDescriptor :
    (((α × β) ⊕ ρ) × ((α × β) ⊕ ρ)) →
      SingularCellDescriptor α β ρ γ
  | (Sum.inl (i, k), Sum.inl (j, l)) =>
      match X.split (X.outer.first.symbol i j) with
      | Sum.inl g => .ordinary g i j k l
      | Sum.inr r => .parameter r i j (some k) (some l)
  | (Sum.inl (i, k), Sum.inr r) =>
      .parameter r i (X.specialColumn r i) (some k) none
  | (Sum.inr r, Sum.inl (j, l)) =>
      .parameter r (X.specialRow r j) j none (some l)
  | (Sum.inr r, Sum.inr s) => .exceptional r s

private noncomputable def descriptorKet :
    SingularCellDescriptor α β ρ γ → Ket ((α × β) ⊕ ρ)
  | .ordinary g i j k l =>
      extendedTensor (ρ := ρ) (basis (X.outer.base.symbol i j))
        ((X.ordinary.copy g).square.entry k l)
  | .parameter r i j s t =>
      parameterTensor r (basis (X.outer.base.symbol i j))
        ((X.special.copy r).full.square.entry s t)
  | .exceptional r s =>
      exceptionalKet (α := α) (β := β)
        (X.exceptional.square.entry r s)

private theorem entry_eq_descriptorKet (p q : (α × β) ⊕ ρ) :
    X.squareEntry p q = X.descriptorKet (X.cellDescriptor (p, q)) := by
  rcases p with ⟨i, k⟩ | r <;> rcases q with ⟨j, l⟩ | s
  · cases h : X.split (X.outer.first.symbol i j) <;>
      simp [cellDescriptor, descriptorKet, squareEntry, h]
  · simp [cellDescriptor, descriptorKet, squareEntry]
  · simp [cellDescriptor, descriptorKet, squareEntry]
  · simp [cellDescriptor, descriptorKet, squareEntry]

/-- A descriptor is incident with the required outer first transversal, and
parameter descriptors never describe the deleted hole. -/
private def DescriptorValid : SingularCellDescriptor α β ρ γ → Prop
  | .ordinary g i j _ _ =>
      X.split (X.outer.first.symbol i j) = Sum.inl g
  | .parameter r i j s t =>
      X.split (X.outer.first.symbol i j) = Sum.inr r ∧
        PointedMaximalRQLS.IsNonholeCell s t
  | .exceptional _ _ => True

private theorem cellDescriptor_valid (p q : (α × β) ⊕ ρ) :
    X.DescriptorValid (X.cellDescriptor (p, q)) := by
  rcases p with ⟨i, k⟩ | r <;> rcases q with ⟨j, l⟩ | s
  · cases h : X.split (X.outer.first.symbol i j) <;>
      simp [cellDescriptor, DescriptorValid, h,
        PointedMaximalRQLS.IsNonholeCell]
  · simp [cellDescriptor, DescriptorValid,
      PointedMaximalRQLS.IsNonholeCell, specialLabel]
  · simp [cellDescriptor, DescriptorValid,
      PointedMaximalRQLS.IsNonholeCell, specialLabel]
  · simp [cellDescriptor, DescriptorValid]

private theorem cellDescriptor_injective : Function.Injective X.cellDescriptor := by
  rintro ⟨p, q⟩ ⟨p', q'⟩ h
  rcases p with ⟨i, k⟩ | r <;> rcases q with ⟨j, l⟩ | s <;>
    rcases p' with ⟨i', k'⟩ | r' <;> rcases q' with ⟨j', l'⟩ | s'
  all_goals
    simp only [cellDescriptor] at h
  all_goals
    repeat' first | split at h | contradiction
  all_goals
    simp_all

/-- The two fixed nonzero coordinates and the finite avoidance condition
needed to turn the QLS constructed in `SingularProduct` into a
maximal-cardinality QLS. -/
structure SeparationHypotheses where
  regular_coordinates : ∃ d e : β, d ≠ e ∧
    (∀ (g : γ) (i j : β),
      (X.ordinary.copy g).square.entry i j d ≠ 0 ∧
        (X.ordinary.copy g).square.entry i j e ≠ 0) ∧
    (∀ (r : ρ), (X.special.copy r).RegularAt d e)
  ordinary_avoids_special : ∀ (g : γ) (i j : β) (r : ρ)
      (s t : Option β),
    PointedMaximalRQLS.IsNonholeCell s t →
    (X.special.copy r).full.square.entry s t none = 0 →
    ¬ PhaseEquivalent ((X.ordinary.copy g).square.entry i j)
      (fun b ↦ (X.special.copy r).full.square.entry s t (some b))

private theorem circle_scalar_ne_zero {z : ℂ} (hz : ‖z‖ = 1) : z ≠ 0 := by
  intro h
  simp [h] at hz

private theorem phase_extended_factors (d : β) {a a' : α} {b b' : Ket β}
    (hbd : b d ≠ 0)
    (h : PhaseEquivalent
      (extendedTensor (ρ := ρ) (basis a) b)
      (extendedTensor (ρ := ρ) (basis a') b')) :
    a = a' ∧ PhaseEquivalent b b' := by
  rcases h with ⟨z, hz, hvec⟩
  have haa : a = a' := by
    by_contra hne
    have hv := congrFun hvec (Sum.inl (a, d))
    simp [extendedTensor, basis_apply, hne, Ne.symm hne] at hv
    exact hbd hv
  subst a'
  refine ⟨rfl, ⟨z, hz, ?_⟩⟩
  funext t
  have hv := congrFun hvec (Sum.inl (a, t))
  simpa [extendedTensor, basis_apply] using hv

private theorem phase_parameter_base (d : β) {r s : ρ} {a a' : α}
    {c c' : Ket (Option β)} (hcd : c (some d) ≠ 0)
    (h : PhaseEquivalent (parameterTensor r (basis a) c)
      (parameterTensor s (basis a') c')) : a = a' := by
  rcases h with ⟨z, hz, hvec⟩
  by_contra hne
  have hv := congrFun hvec (Sum.inl (a, d))
  simp [parameterTensor, basis_apply, hne, Ne.symm hne] at hv
  exact hcd hv

private theorem phase_parameter_same {r : ρ} {a : α}
    {c c' : Ket (Option β)}
    (h : PhaseEquivalent (parameterTensor r (basis a) c)
      (parameterTensor r (basis a) c')) : PhaseEquivalent c c' := by
  rcases h with ⟨z, hz, hvec⟩
  refine ⟨z, hz, ?_⟩
  funext t
  rcases t with _ | b
  · have hv := congrFun hvec (Sum.inr r)
    simpa [parameterTensor] using hv
  · have hv := congrFun hvec (Sum.inl (a, b))
    simpa [parameterTensor, basis_apply] using hv

private theorem phase_parameter_different {r s : ρ} (hrs : r ≠ s) {a : α}
    {c c' : Ket (Option β)}
    (h : PhaseEquivalent (parameterTensor r (basis a) c)
      (parameterTensor s (basis a) c')) :
    c none = 0 ∧ c' none = 0 ∧ PhaseEquivalent c c' := by
  rcases h with ⟨z, hz, hvec⟩
  have hz0 := circle_scalar_ne_zero hz
  have hc : c none = 0 := by
    have hv := congrFun hvec (Sum.inr r)
    simpa [parameterTensor, hrs] using hv
  have hc' : c' none = 0 := by
    have hv := congrFun hvec (Sum.inr s)
    have hsr : s ≠ r := Ne.symm hrs
    simp [parameterTensor, hrs, hsr] at hv
    exact hv.resolve_left hz0
  refine ⟨hc, hc', ⟨z, hz, ?_⟩⟩
  funext t
  rcases t with _ | b
  · simp [hc, hc']
  · have hv := congrFun hvec (Sum.inl (a, b))
    simpa [parameterTensor, basis_apply] using hv

private theorem phase_extended_parameter (d : β) {r : ρ} {a a' : α}
    {b : Ket β} {c : Ket (Option β)} (hbd : b d ≠ 0)
    (h : PhaseEquivalent (extendedTensor (ρ := ρ) (basis a) b)
      (parameterTensor r (basis a') c)) :
    a = a' ∧ c none = 0 ∧
      PhaseEquivalent b (fun t ↦ c (some t)) := by
  rcases h with ⟨z, hz, hvec⟩
  have hz0 := circle_scalar_ne_zero hz
  have haa : a = a' := by
    by_contra hne
    have hv := congrFun hvec (Sum.inl (a, d))
    simp [extendedTensor, parameterTensor, basis_apply, hne, Ne.symm hne] at hv
    exact hbd hv
  subst a'
  have hc : c none = 0 := by
    have hv := congrFun hvec (Sum.inr r)
    simp [extendedTensor, parameterTensor] at hv
    exact hv.resolve_left hz0
  refine ⟨rfl, hc, ⟨z, hz, ?_⟩⟩
  funext t
  have hv := congrFun hvec (Sum.inl (a, t))
  simpa [extendedTensor, parameterTensor, basis_apply] using hv

private theorem no_phase_extended_exceptional (d : β) {a : α} {b : Ket β}
    {v : Ket ρ} (hbd : b d ≠ 0) :
    ¬ PhaseEquivalent (extendedTensor (ρ := ρ) (basis a) b)
      (exceptionalKet (α := α) (β := β) v) := by
  rintro ⟨z, hz, hvec⟩
  have hv := congrFun hvec (Sum.inl (a, d))
  simp [extendedTensor, exceptionalKet, basis_apply] at hv
  exact hbd hv

private theorem no_phase_parameter_exceptional (d : β) {r : ρ} {a : α}
    {c : Ket (Option β)} {v : Ket ρ} (hcd : c (some d) ≠ 0) :
    ¬ PhaseEquivalent (parameterTensor r (basis a) c)
      (exceptionalKet (α := α) (β := β) v) := by
  rintro ⟨z, hz, hvec⟩
  have hv := congrFun hvec (Sum.inl (a, d))
  simp [parameterTensor, exceptionalKet, basis_apply] at hv
  exact hcd hv

private theorem phase_exceptional_iff {v v' : Ket ρ} :
    PhaseEquivalent (exceptionalKet (α := α) (β := β) v)
      (exceptionalKet (α := α) (β := β) v') ↔ PhaseEquivalent v v' := by
  constructor
  · rintro ⟨z, hz, hvec⟩
    refine ⟨z, hz, ?_⟩
    funext r
    have hv := congrFun hvec (Sum.inr r)
    simpa [exceptionalKet] using hv
  · rintro ⟨z, hz, hvec⟩
    refine ⟨z, hz, ?_⟩
    funext q
    rcases q with p | r
    · simp [exceptionalKet]
    · simpa [exceptionalKet] using congrFun hvec r

private theorem descriptor_phase_injective
    (S : X.SeparationHypotheses)
    {p q : SingularCellDescriptor α β ρ γ}
    (hp : X.DescriptorValid p) (hq : X.DescriptorValid q)
    (hphase : PhaseEquivalent (X.descriptorKet p) (X.descriptorKet q)) :
    p = q := by
  obtain ⟨d, e, hde, hordinary, hspecial⟩ := S.regular_coordinates
  rcases p with ⟨g, i, j, k, l⟩ | ⟨r, i, j, s, t⟩ | ⟨r, s⟩ <;>
    rcases q with ⟨g', i', j', k', l'⟩ |
      ⟨r', i', j', s', t'⟩ | ⟨r', s'⟩
  · rcases phase_extended_factors d (hordinary g k l).1 hphase with
      ⟨hbase, hinner⟩
    have hg : g = g' := by
      by_contra hgg
      exact X.ordinary.pairwise_disjoint hgg k l k' l' hinner
    subst g'
    have hfirst : X.outer.first.symbol i j = X.outer.first.symbol i' j' := by
      apply X.split.injective
      rw [hp, hq]
    rcases X.outer.base_first hbase hfirst with ⟨hi, hj⟩
    subst i'; subst j'
    rcases (X.ordinary.copy g).maximal hinner with ⟨hk, hl⟩
    subst k'; subst l'
    rfl
  · rcases phase_extended_parameter d (hordinary g k l).1 hphase with
      ⟨-, hc0, hinner⟩
    exact ((S.ordinary_avoids_special g k l r' s' t' hq.2 hc0) hinner).elim
  · exact ((no_phase_extended_exceptional d (hordinary g k l).1) hphase).elim
  · rcases phase_extended_parameter d (hordinary g' k' l').1 hphase.symm with
      ⟨-, hc0, hinner⟩
    exact ((S.ordinary_avoids_special g' k' l' r s t hp.2 hc0) hinner).elim
  · have hcd : (X.special.copy r).full.square.entry s t (some d) ≠ 0 :=
      ((hspecial r).2 s t hp.2).1
    have hbase := phase_parameter_base d hcd hphase
    by_cases hrr : r = r'
    · subst r'
      have hfirst : X.outer.first.symbol i j = X.outer.first.symbol i' j' := by
        apply X.split.injective
        rw [hp.1, hq.1]
      have hphase' : PhaseEquivalent
          (parameterTensor r (basis (X.outer.base.symbol i j))
            ((X.special.copy r).full.square.entry s t))
          (parameterTensor r (basis (X.outer.base.symbol i j))
            ((X.special.copy r).full.square.entry s' t')) := by
        simpa [descriptorKet, hbase] using hphase
      have hcphase := phase_parameter_same hphase'
      rcases X.outer.base_first hbase hfirst with ⟨hi, hj⟩
      rcases (X.special.copy r).full.maximal hcphase with ⟨hs, ht⟩
      subst i'; subst j'; subst s'; subst t'
      rfl
    · have hphase' : PhaseEquivalent
          (parameterTensor r (basis (X.outer.base.symbol i j))
            ((X.special.copy r).full.square.entry s t))
          (parameterTensor r' (basis (X.outer.base.symbol i j))
            ((X.special.copy r').full.square.entry s' t')) := by
        simpa [descriptorKet, hbase] using hphase
      obtain ⟨-, -, hcphase⟩ := phase_parameter_different hrr hphase'
      exact ((X.special.pairwise_disjoint hrr hp.2 hq.2) hcphase).elim
  · exact ((no_phase_parameter_exceptional d
      ((hspecial r).2 s t hp.2).1) hphase).elim
  · exact ((no_phase_extended_exceptional d
      (hordinary g' k' l').1) hphase.symm).elim
  · exact ((no_phase_parameter_exceptional d
      ((hspecial r').2 s' t' hq.2).1) hphase.symm).elim
  · have hdphase := phase_exceptional_iff.mp hphase
    rcases X.exceptional.maximal hdphase with ⟨hr, hs⟩
    subst r'; subst s'
    rfl

/-- Under the explicit separation hypotheses, every two projectively equal
entries of the singular array occupy the same cell. -/
theorem square_hasMaximalCardinality (S : X.SeparationHypotheses) :
    X.square.HasMaximalCardinality := by
  intro p q p' q' hphase
  have hdescPhase : PhaseEquivalent
      (X.descriptorKet (X.cellDescriptor (p, q)))
      (X.descriptorKet (X.cellDescriptor (p', q'))) := by
    rw [← X.entry_eq_descriptorKet, ← X.entry_eq_descriptorKet]
    exact hphase
  have hdesc := X.descriptor_phase_injective S
    (X.cellDescriptor_valid p q) (X.cellDescriptor_valid p' q') hdescPhase
  have hcell : (p, q) = (p', q') := X.cellDescriptor_injective hdesc
  exact ⟨congrArg Prod.fst hcell, congrArg Prod.snd hcell⟩

end SingularProductData

end LeanCo.QuantumLatin
