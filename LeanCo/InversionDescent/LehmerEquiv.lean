import LeanCo.InversionDescent.Permutation

/-!
# The reverse Lehmer-code equivalence

This file proves that the reverse Lehmer code is not merely a statistic: it is
an equivalence between permutations of `Fin n` and inversion sequences of
length `n`.  The proof first shows directly that the ordinary Lehmer code
determines a permutation.  Surjectivity then follows from the exact finite
cardinalities; consequently the inverse in `reverseLehmerEquiv` is the genuine
inverse of the pointwise code appearing in the paper.
-/

open scoped BigOperators

namespace LeanCo.Permutation

variable {n : ℕ}

/-! ## The Lehmer code determines the permutation -/

/-- Positions to the left of `i` carrying a smaller value. -/
def leftSmaller (σ : Equiv.Perm (Fin n)) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun j ↦ j < i ∧ σ j < σ i

@[simp]
theorem mem_leftSmaller {σ : Equiv.Perm (Fin n)} {i j : Fin n} :
    j ∈ leftSmaller σ i ↔ j < i ∧ σ j < σ i := by
  simp [leftSmaller]

/-- Exactly `(σ i).val` positions carry a value below `σ i`. -/
theorem card_positions_value_lt (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    (Finset.univ.filter fun j ↦ σ j < σ i).card = (σ i).val := by
  classical
  rw [← Fin.card_Iio (σ i)]
  refine Finset.card_bij (fun j _ ↦ σ j) ?_ ?_ ?_
  · intro j hj
    exact Finset.mem_Iio.mpr (Finset.mem_filter.mp hj).2
  · intro j₁ hj₁ j₂ hj₂ h
    exact σ.injective h
  · intro y hy
    refine ⟨σ.symm y, ?_, by simp⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using Finset.mem_Iio.mp hy⟩

/-- The smaller values split into those occurring to the left and to the right. -/
theorem card_leftSmaller_add_lehmerCode (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    (leftSmaller σ i).card + lehmerCode σ i = (σ i).val := by
  classical
  have hsplit :
      (Finset.univ.filter fun j ↦ σ j < σ i) =
        leftSmaller σ i ∪ rightSmaller σ i := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      mem_leftSmaller, mem_rightSmaller]
    constructor
    · intro hji
      have hne : j ≠ i := by
        intro h
        subst j
        exact (lt_irrefl (σ i)) hji
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact Or.inl ⟨hlt, hji⟩
      · exact Or.inr ⟨hgt, hji⟩
    · rintro (⟨_, h⟩ | ⟨_, h⟩) <;> exact h
  have hdisj : Disjoint (leftSmaller σ i) (rightSmaller σ i) := by
    refine Finset.disjoint_left.mpr ?_
    intro j hjl hjr
    have hlt := (mem_leftSmaller.mp hjl).1
    have hgt := (mem_rightSmaller.mp hjr).1
    exact (not_lt_of_ge (le_of_lt hlt)) hgt
  rw [← card_positions_value_lt σ i, hsplit, Finset.card_union_of_disjoint hdisj]
  rfl

/-- If two permutations agree before `i`, then a smaller value at `i` has a
strictly smaller Lehmer-code digit.  This is the rank-among-unused-values
characterization, proved without choosing an inverse decoder. -/
theorem lehmerCode_lt_of_eq_on_Iio_of_apply_lt
    {σ τ : Equiv.Perm (Fin n)} (i : Fin n)
    (hprefix : ∀ j, j < i → σ j = τ j) (hi : σ i < τ i) :
    lehmerCode σ i < lehmerCode τ i := by
  classical
  let e : Fin n ≃ Fin n := σ.trans τ.symm
  have he_apply (j : Fin n) : τ (e j) = σ j := by
    simp [e]
  have he_gt (j : Fin n) (hj : i < j) (hjval : σ j < σ i) : i < e j := by
    by_contra hnot
    have hei : e j ≤ i := le_of_not_gt hnot
    rcases eq_or_lt_of_le hei with heq | helt
    · have : σ j = τ i := by simpa [heq] using (he_apply j).symm
      exact (ne_of_lt (hjval.trans hi)) this
    · have hsame := hprefix (e j) helt
      have hσ : σ (e j) = σ j := hsame.trans (he_apply j)
      have : e j = j := σ.injective hσ
      exact (not_lt_of_ge (le_of_lt hj)) (this ▸ helt)
  have hmap_subset :
      (rightSmaller σ i).map e.toEmbedding ⊆ rightSmaller τ i := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hx
    have hj' := mem_rightSmaller.mp hj
    apply mem_rightSmaller.mpr
    exact ⟨he_gt j hj'.1 hj'.2, (he_apply j) ▸ hj'.2.trans hi⟩
  have hextra_mem : e i ∈ rightSmaller τ i := by
    apply mem_rightSmaller.mpr
    constructor
    · by_contra hnot
      have hei : e i ≤ i := le_of_not_gt hnot
      rcases eq_or_lt_of_le hei with heq | helt
      · have : σ i = τ i := by simpa [heq] using (he_apply i).symm
        exact (ne_of_lt hi) this
      · have hsame := hprefix (e i) helt
        have hσ : σ (e i) = σ i := hsame.trans (he_apply i)
        exact (ne_of_lt helt) (σ.injective hσ)
    · simpa [he_apply] using hi
  have hextra_not : e i ∉ (rightSmaller σ i).map e.toEmbedding := by
    intro hmem
    obtain ⟨j, hj, heq⟩ := Finset.mem_map.mp hmem
    have : j = i := e.injective heq
    subst j
    exact (lt_irrefl i) (mem_rightSmaller.mp hj).1
  change (rightSmaller σ i).card < (rightSmaller τ i).card
  rw [← Finset.card_map]
  apply Finset.card_lt_card
  exact (Finset.ssubset_iff_of_subset hmap_subset).2 ⟨e i, hextra_mem, hextra_not⟩

/-- The ordinary Lehmer-code function is injective. -/
theorem lehmerCode_injective :
    Function.Injective (lehmerCode : Equiv.Perm (Fin n) → Fin n → ℕ) := by
  intro σ τ hcode
  have hall : ∀ k (hk : k < n), σ ⟨k, hk⟩ = τ ⟨k, hk⟩ := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro hk
        let i : Fin n := ⟨k, hk⟩
        have hprefix : ∀ j, j < i → σ j = τ j := by
          intro j hj
          have hjk : j.1 < k := by
            change j.1 < k at hj
            exact hj
          simpa using ih j.1 hjk j.isLt
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have hc := lehmerCode_lt_of_eq_on_Iio_of_apply_lt i hprefix hlt
          exact (ne_of_lt hc) (congrFun hcode i)
        · have hc := lehmerCode_lt_of_eq_on_Iio_of_apply_lt i
            (fun j hj ↦ (hprefix j hj).symm) hgt
          exact (ne_of_gt hc) (congrFun hcode i)
  apply Equiv.ext
  intro i
  exact hall i.1 i.isLt

/-- The reverse Lehmer-code function is injective. -/
theorem reverseLehmerCode_injective :
    Function.Injective (reverseLehmerCode : Equiv.Perm (Fin n) → Fin n → ℕ) := by
  intro σ τ hcode
  apply lehmerCode_injective
  funext i
  simpa [reverseLehmerCode] using congrFun hcode i.rev

/-! ## Exact cardinality and the equivalence -/

/-- Regard an inversion-sequence digit as an element of `Fin (i + 1)`. -/
def inversionSequencesEquivDigits (n : ℕ) :
    InversionSequences n ≃ ((i : Fin n) → Fin (i.1 + 1)) where
  toFun a i := ⟨a.1 i, Nat.lt_succ_iff.mpr (a.2 i)⟩
  invFun a := ⟨fun i ↦ (a i).1, fun i ↦ Nat.le_of_lt_succ (a i).2⟩
  left_inv a := by
    apply Subtype.ext
    funext i
    rfl
  right_inv a := by
    funext i
    apply Fin.ext
    rfl

noncomputable instance inversionSequencesFintype (n : ℕ) :
    Fintype (InversionSequences n) :=
  Fintype.ofEquiv ((i : Fin n) → Fin (i.1 + 1))
    (inversionSequencesEquivDigits n).symm

theorem prod_fin_digit_sizes (n : ℕ) :
    (∏ i : Fin n, (i.1 + 1)) = n.factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Fin.prod_univ_castSucc]
      simp [ih, Nat.factorial_succ, mul_comm]

/-- There are exactly `n!` inversion sequences of length `n`. -/
theorem card_inversionSequences (n : ℕ) :
    Fintype.card (InversionSequences n) = n.factorial := by
  classical
  rw [Fintype.card_congr (inversionSequencesEquivDigits n), Fintype.card_pi]
  simp only [Fintype.card_fin]
  exact prod_fin_digit_sizes n

/-- The reverse Lehmer code bundled with its defining inversion-sequence bounds. -/
def reverseLehmerMap (σ : Equiv.Perm (Fin n)) : InversionSequences n :=
  ⟨reverseLehmerCode σ, reverseLehmerCode_isInversionSequence σ⟩

@[simp]
theorem reverseLehmerMap_apply (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    (reverseLehmerMap σ).1 i = reverseLehmerCode σ i :=
  rfl

theorem reverseLehmerMap_injective :
    Function.Injective (reverseLehmerMap : Equiv.Perm (Fin n) → InversionSequences n) := by
  intro σ τ h
  apply reverseLehmerCode_injective
  exact congrArg Subtype.val h

theorem reverseLehmerMap_bijective :
    Function.Bijective (reverseLehmerMap : Equiv.Perm (Fin n) → InversionSequences n) := by
  classical
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨reverseLehmerMap_injective, ?_⟩
  rw [Fintype.card_perm, Fintype.card_fin, card_inversionSequences]

/-- The standard equivalence between permutations and inversion sequences.

Its forward map is definitionally the reverse Lehmer code, not an arbitrary
equivalence obtained from the equality of cardinalities.
-/
noncomputable def reverseLehmerEquiv (n : ℕ) :
    Equiv.Perm (Fin n) ≃ InversionSequences n :=
  Equiv.ofBijective reverseLehmerMap reverseLehmerMap_bijective

@[simp]
theorem reverseLehmerEquiv_apply_val (σ : Equiv.Perm (Fin n)) :
    (reverseLehmerEquiv n σ).1 = reverseLehmerCode σ :=
  rfl


@[simp]
theorem reverseLehmerEquiv_apply (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    (reverseLehmerEquiv n σ).1 i = reverseLehmerCode σ i :=
  rfl

/-- Applying the decoder after the reverse Lehmer code returns the permutation. -/
theorem reverseLehmerEquiv_symm_apply_apply (σ : Equiv.Perm (Fin n)) :
    (reverseLehmerEquiv n).symm (reverseLehmerMap σ) = σ :=
  (reverseLehmerEquiv n).symm_apply_apply σ

/-- Applying the reverse Lehmer code after the decoder returns every digit. -/
theorem reverseLehmerEquiv_apply_symm_apply (a : InversionSequences n) :
    reverseLehmerMap ((reverseLehmerEquiv n).symm a) = a :=
  (reverseLehmerEquiv n).apply_symm_apply a

/-! ## Restriction to the two avoidance classes -/

/-- Proposition 2.3 restricted to an equivalence of the avoidance classes. -/
noncomputable def avoidingReverseLehmerEquiv (n : ℕ) :
    {σ : Equiv.Perm (Fin n) // Avoids32_1 σ} ≃
      {a : InversionSequences n // Avoids0_12 a.1} :=
  (reverseLehmerEquiv n).subtypeEquiv fun σ ↦ by
    rw [reverseLehmerEquiv_apply_val]
    exact proposition_2_3 σ

@[simp]
theorem avoidingReverseLehmerEquiv_apply
    (σ : {σ : Equiv.Perm (Fin n) // Avoids32_1 σ}) (i : Fin n) :
    (avoidingReverseLehmerEquiv n σ).1.1 i = reverseLehmerCode σ.1 i :=
  rfl

/-! ## Preservation of the two weights -/

/-- Sum of the entries of an inversion sequence. -/
def inversionSequenceWeight (a : InversionSequences n) : ℕ :=
  ∑ i, a.1 i

/-- Adjacent strict rises of an inversion sequence of length `n + 1`. -/
def inversionSequenceRisePositions (a : InversionSequences (n + 1)) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ a.1 i.castSucc < a.1 i.succ

@[simp]
theorem mem_inversionSequenceRisePositions
    {a : InversionSequences (n + 1)} {i : Fin n} :
    i ∈ inversionSequenceRisePositions a ↔ a.1 i.castSucc < a.1 i.succ := by
  simp [inversionSequenceRisePositions]

/-- Number of adjacent strict rises. -/
def inversionSequenceRiseNumber (a : InversionSequences (n + 1)) : ℕ :=
  (inversionSequenceRisePositions a).card

/-- The equivalence preserves inversion number as entry sum. -/
theorem reverseLehmerEquiv_preserves_inversionNumber (σ : Equiv.Perm (Fin n)) :
    inversionNumber σ = inversionSequenceWeight (reverseLehmerEquiv n σ) := by
  simpa [inversionSequenceWeight, reverseLehmerEquiv_apply_val] using
    inversionNumber_eq_sum_reverseLehmerCode σ

/-- The equivalence preserves descent number as number of adjacent rises. -/
theorem reverseLehmerEquiv_preserves_descentNumber
    (σ : Equiv.Perm (Fin (n + 1))) :
    descentNumber σ = inversionSequenceRiseNumber (reverseLehmerEquiv (n + 1) σ) := by
  rw [descentNumber_eq_card_reverseLehmerRisePositions]
  rfl

/-- Weight preservation on the restricted avoidance equivalence. -/
theorem avoidingReverseLehmerEquiv_preserves_inversionNumber
    (σ : {σ : Equiv.Perm (Fin n) // Avoids32_1 σ}) :
    inversionNumber σ.1 =
      inversionSequenceWeight (avoidingReverseLehmerEquiv n σ).1 := by
  exact reverseLehmerEquiv_preserves_inversionNumber σ.1

/-- Descent/rise preservation on the restricted avoidance equivalence. -/
theorem avoidingReverseLehmerEquiv_preserves_descentNumber
    (σ : {σ : Equiv.Perm (Fin (n + 1)) // Avoids32_1 σ}) :
    descentNumber σ.1 =
      inversionSequenceRiseNumber (avoidingReverseLehmerEquiv (n + 1) σ).1 := by
  exact reverseLehmerEquiv_preserves_descentNumber σ.1

end LeanCo.Permutation
