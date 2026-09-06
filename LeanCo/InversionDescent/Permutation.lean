import Mathlib

/-!
# Permutations, Lehmer codes, and the vincular pattern `32-1`

This file formalizes Definitions 1.1, 2.1, and 2.2 and Propositions 2.3 and 2.4
of *Inversion-descent enumerators of 321-avoiding permutations*.  Positions are
zero-indexed, so the paper's bound `p_i ≤ n - i` becomes `p i ≤ n - 1 - i`.

The notation in the paper underlines the adjacent letters of a vincular pattern.
Here `Occurs32_1` requires the positions of `3` and `2` to be adjacent, while
`Occurs0_12` requires the positions of `1` and `2` to be adjacent.
-/

open scoped BigOperators

namespace LeanCo.Permutation

variable {n : ℕ}

/-! ## Inversions and descents -/

/-- The inversion pairs of a permutation (Definition 1.1). -/
def inversionPairs (σ : Equiv.Perm (Fin n)) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun ij ↦ ij.1 < ij.2 ∧ σ ij.2 < σ ij.1

@[simp]
theorem mem_inversionPairs {σ : Equiv.Perm (Fin n)} {i j : Fin n} :
    (i, j) ∈ inversionPairs σ ↔ i < j ∧ σ j < σ i := by
  simp [inversionPairs]

/-- The inversion number is the cardinality of the set of inversion pairs. -/
def inversionNumber (σ : Equiv.Perm (Fin n)) : ℕ :=
  (inversionPairs σ).card

/-- Two positions are adjacent, with `j` immediately to the right of `i`. -/
def Adjacent (i j : Fin n) : Prop :=
  j.1 = i.1 + 1

/-- A descent is indexed by its left-hand position. -/
noncomputable def descentSet (σ : Equiv.Perm (Fin n)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i ↦ ∃ j, Adjacent i j ∧ σ j < σ i

@[simp]
theorem mem_descentSet {σ : Equiv.Perm (Fin n)} {i : Fin n} :
    i ∈ descentSet σ ↔ ∃ j, Adjacent i j ∧ σ j < σ i := by
  classical
  simp [descentSet]

/-- The number of descents of a permutation. -/
noncomputable def descentNumber (σ : Equiv.Perm (Fin n)) : ℕ :=
  (descentSet σ).card

/-! ## Lehmer and reverse Lehmer codes -/

/-- Positions to the right of `i` carrying a smaller value. -/
def rightSmaller (σ : Equiv.Perm (Fin n)) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun j ↦ i < j ∧ σ j < σ i

@[simp]
theorem mem_rightSmaller {σ : Equiv.Perm (Fin n)} {i j : Fin n} :
    j ∈ rightSmaller σ i ↔ i < j ∧ σ j < σ i := by
  simp [rightSmaller]

/-- The Lehmer code of a permutation (Definition 2.1). -/
def lehmerCode (σ : Equiv.Perm (Fin n)) (i : Fin n) : ℕ :=
  (rightSmaller σ i).card

/-- Definition 1.1 decomposed by the left endpoint of each inversion. -/
theorem inversionNumber_eq_sum_lehmerCode (σ : Equiv.Perm (Fin n)) :
    inversionNumber σ = ∑ i, lehmerCode σ i := by
  classical
  simp only [inversionNumber, inversionPairs, lehmerCode, rightSmaller,
    Finset.card_eq_sum_ones, Finset.sum_filter, ← Finset.univ_product_univ,
    Finset.sum_product]

/-- The defining bounds for the collection `L_n` of Lehmer codes. -/
def IsLehmerCode (p : Fin n → ℕ) : Prop :=
  ∀ i, p i ≤ n - 1 - i.1

/-- The collection `L_n` in Definition 2.1. -/
def LehmerCodes (n : ℕ) :=
  {p : Fin n → ℕ // IsLehmerCode p}

theorem lehmerCode_bound (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    lehmerCode σ i ≤ n - 1 - i.1 := by
  calc
    lehmerCode σ i ≤ (Finset.Ioi i).card := by
      apply Finset.card_le_card
      intro j hj
      exact Finset.mem_Ioi.mpr (mem_rightSmaller.mp hj).1
    _ = n - 1 - i.1 := Fin.card_Ioi i

theorem lehmerCode_isLehmerCode (σ : Equiv.Perm (Fin n)) :
    IsLehmerCode (lehmerCode σ) :=
  lehmerCode_bound σ

/-- Reverse indexing of the Lehmer code (Definition 2.2). -/
def reverseLehmerCode (σ : Equiv.Perm (Fin n)) (i : Fin n) : ℕ :=
  lehmerCode σ i.rev

theorem sum_reverseLehmerCode_eq_sum_lehmerCode (σ : Equiv.Perm (Fin n)) :
    ∑ i, reverseLehmerCode σ i = ∑ i, lehmerCode σ i := by
  exact Equiv.sum_comp Fin.revPerm (lehmerCode σ)

/-- The inversion number is the weight of the reverse Lehmer code. -/
theorem inversionNumber_eq_sum_reverseLehmerCode (σ : Equiv.Perm (Fin n)) :
    inversionNumber σ = ∑ i, reverseLehmerCode σ i := by
  rw [inversionNumber_eq_sum_lehmerCode, sum_reverseLehmerCode_eq_sum_lehmerCode]

/-- The defining bounds for inversion sequences. -/
def IsInversionSequence (a : Fin n → ℕ) : Prop :=
  ∀ i, a i ≤ i.1

/-- The collection `I_n` of inversion sequences. -/
def InversionSequences (n : ℕ) :=
  {a : Fin n → ℕ // IsInversionSequence a}

theorem reverseLehmerCode_bound (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    reverseLehmerCode σ i ≤ i.1 := by
  have h := lehmerCode_bound σ i.rev
  change lehmerCode σ i.rev ≤ i.1
  change lehmerCode σ i.rev ≤ n - 1 - (n - (i.1 + 1)) at h
  omega

theorem reverseLehmerCode_isInversionSequence (σ : Equiv.Perm (Fin n)) :
    IsInversionSequence (reverseLehmerCode σ) :=
  reverseLehmerCode_bound σ

/-- The first entry of every reverse Lehmer code is zero. -/
theorem reverseLehmerCode_eq_zero_of_val_eq_zero (σ : Equiv.Perm (Fin n))
    (i : Fin n) (hi : i.1 = 0) : reverseLehmerCode σ i = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro hpos
  change 0 < (rightSmaller σ i.rev).card at hpos
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hpos
  have hj' := mem_rightSmaller.mp hj
  have hlt : n - (i.1 + 1) < j.1 := by
    change i.rev < j
    exact hj'.1
  omega

/-- A positive Lehmer-code entry supplies a smaller value to its right. -/
theorem exists_right_smaller_of_lehmerCode_pos (σ : Equiv.Perm (Fin n)) (i : Fin n)
    (h : 0 < lehmerCode σ i) : ∃ j, i < j ∧ σ j < σ i := by
  obtain ⟨j, hj⟩ := Finset.card_pos.mp h
  exact ⟨j, mem_rightSmaller.mp hj⟩

/-!
For adjacent positions, a descent is equivalent to a strict decrease of Lehmer-code
entries.  This is the local comparison used in Proposition 2.3.
-/
theorem descent_iff_lehmerCode_gt (σ : Equiv.Perm (Fin n)) {i j : Fin n}
    (hij : Adjacent i j) :
    σ j < σ i ↔ lehmerCode σ j < lehmerCode σ i := by
  constructor
  · intro hdesc
    change (rightSmaller σ j).card < (rightSmaller σ i).card
    apply Finset.card_lt_card
    have hsubset : rightSmaller σ j ⊆ rightSmaller σ i := by
      intro k hk
      have hk' := mem_rightSmaller.mp hk
      apply mem_rightSmaller.mpr
      constructor
      · change i.1 < k.1
        change j.1 = i.1 + 1 at hij
        omega
      · exact hk'.2.trans hdesc
    apply (Finset.ssubset_iff_of_subset hsubset).2
    refine ⟨j, mem_rightSmaller.mpr ?_, ?_⟩
    · constructor
      ·
        change i.1 < j.1
        change j.1 = i.1 + 1 at hij
        omega
      · exact hdesc
    · simp
  · intro hcode
    change (rightSmaller σ j).card < (rightSmaller σ i).card at hcode
    by_contra hnotdesc
    have hij_ne : i ≠ j := by
      intro h
      subst j
      change i.1 = i.1 + 1 at hij
      omega
    have hvalue_ne : σ i ≠ σ j := fun h ↦ hij_ne (σ.injective h)
    have hvalue : σ i < σ j :=
      lt_of_le_of_ne (le_of_not_gt hnotdesc) hvalue_ne
    have hsubset : rightSmaller σ i ⊆ rightSmaller σ j := by
      intro k hk
      have hk' := mem_rightSmaller.mp hk
      apply mem_rightSmaller.mpr
      constructor
      · change j.1 < k.1
        change j.1 = i.1 + 1 at hij
        have hkj : k ≠ j := by
          intro h
          subst k
          exact (not_lt_of_ge (le_of_lt hvalue)) hk'.2
        omega
      · exact hk'.2.trans hvalue
    exact (not_lt_of_ge (Finset.card_le_card hsubset)) hcode

/-! ## Descent and reverse-code rise statistics -/

/-- Descent positions in a permutation of length `n + 1`, indexed by `Fin n`. -/
def descentPositions (σ : Equiv.Perm (Fin (n + 1))) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ σ i.succ < σ i.castSucc

@[simp]
theorem mem_descentPositions {σ : Equiv.Perm (Fin (n + 1))} {i : Fin n} :
    i ∈ descentPositions σ ↔ σ i.succ < σ i.castSucc := by
  simp [descentPositions]

/-- Adjacent strict rises of the reverse Lehmer code, indexed by `Fin n`. -/
def reverseLehmerRisePositions (σ : Equiv.Perm (Fin (n + 1))) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦
    reverseLehmerCode σ i.castSucc < reverseLehmerCode σ i.succ

@[simp]
theorem mem_reverseLehmerRisePositions {σ : Equiv.Perm (Fin (n + 1))} {i : Fin n} :
    i ∈ reverseLehmerRisePositions σ ↔
      reverseLehmerCode σ i.castSucc < reverseLehmerCode σ i.succ := by
  simp [reverseLehmerRisePositions]

/-- Reversing indices sends a descent to an adjacent reverse-code rise. -/
theorem descentAt_iff_reverseLehmerRiseAt_rev
    (σ : Equiv.Perm (Fin (n + 1))) (i : Fin n) :
    σ i.succ < σ i.castSucc ↔
      reverseLehmerCode σ i.rev.castSucc < reverseLehmerCode σ i.rev.succ := by
  have hadj : Adjacent i.castSucc i.succ := by
    simp [Adjacent]
  simpa only [reverseLehmerCode, Fin.rev_castSucc, Fin.rev_succ, Fin.rev_rev] using
    (descent_iff_lehmerCode_gt σ hadj)

/-- The descent positions and adjacent reverse-code rises are equinumerous. -/
theorem card_descentPositions_eq_card_reverseLehmerRisePositions
    (σ : Equiv.Perm (Fin (n + 1))) :
    (descentPositions σ).card = (reverseLehmerRisePositions σ).card := by
  refine Finset.card_bij (fun i _ ↦ i.rev) ?_ ?_ ?_
  · intro i hi
    exact mem_reverseLehmerRisePositions.mpr
      ((descentAt_iff_reverseLehmerRiseAt_rev σ i).mp (mem_descentPositions.mp hi))
  · intro i₁ _ i₂ _ h
    exact Fin.rev_injective h
  · intro i hi
    refine ⟨i.rev, ?_, by simp⟩
    apply mem_descentPositions.mpr
    apply (descentAt_iff_reverseLehmerRiseAt_rev σ i.rev).mpr
    simpa using mem_reverseLehmerRisePositions.mp hi

/-- The generic descent count agrees with the `Fin n`-indexed descent positions. -/
theorem descentNumber_eq_card_descentPositions (σ : Equiv.Perm (Fin (n + 1))) :
    descentNumber σ = (descentPositions σ).card := by
  have hcard : (descentPositions σ).card = (descentSet σ).card := by
    refine Finset.card_bij (fun i _ ↦ i.castSucc) ?_ ?_ ?_
    · intro i hi
      apply mem_descentSet.mpr
      exact ⟨i.succ, by simp [Adjacent], mem_descentPositions.mp hi⟩
    · intro i₁ _ i₂ _ h
      exact Fin.castSucc_injective _ h
    · intro i hi
      obtain ⟨j, hij, hdesc⟩ := mem_descentSet.mp hi
      have hi_lt : i.1 < n := by
        change j.1 = i.1 + 1 at hij
        omega
      let k : Fin n := ⟨i.1, hi_lt⟩
      have hi_cast : k.castSucc = i := Fin.ext rfl
      have hj_succ : k.succ = j := by
        apply Fin.ext
        change k.1 + 1 = j.1
        change j.1 = i.1 + 1 at hij
        simpa [k] using hij.symm
      refine ⟨k, mem_descentPositions.mpr ?_, hi_cast⟩
      simpa [hi_cast, hj_succ] using hdesc
  exact hcard.symm

/-- Descents are counted by adjacent rises of the reverse Lehmer code. -/
theorem descentNumber_eq_card_reverseLehmerRisePositions
    (σ : Equiv.Perm (Fin (n + 1))) :
    descentNumber σ = (reverseLehmerRisePositions σ).card := by
  rw [descentNumber_eq_card_descentPositions,
    card_descentPositions_eq_card_reverseLehmerRisePositions]

/-! ## The vincular patterns `32-1` and `0-12` -/

/-- An occurrence of `32-1`: the entries playing `3` and `2` are adjacent. -/
def Occurs32_1 (σ : Equiv.Perm (Fin n)) : Prop :=
  ∃ i j k, Adjacent i j ∧ j < k ∧ σ j < σ i ∧ σ k < σ j

/-- Avoidance of the vincular pattern `32-1`. -/
def Avoids32_1 (σ : Equiv.Perm (Fin n)) : Prop :=
  ¬ Occurs32_1 σ

/-- An occurrence of `0-12`: the entries playing `1` and `2` are adjacent. -/
def Occurs0_12 (a : Fin n → ℕ) : Prop :=
  ∃ i j k, i < j ∧ Adjacent j k ∧ a i < a j ∧ a j < a k

/-- Avoidance of the vincular inversion-sequence pattern `0-12`. -/
def Avoids0_12 (a : Fin n → ℕ) : Prop :=
  ¬ Occurs0_12 a

/-- Occurrence form of Proposition 2.3. -/
theorem occurs32_1_iff_occurs0_12_reverseLehmerCode (σ : Equiv.Perm (Fin n)) :
    Occurs32_1 σ ↔ Occurs0_12 (reverseLehmerCode σ) := by
  constructor
  · rintro ⟨i, j, k, hij, hjk, hji, hkj⟩
    let z : Fin n := ⟨0, by omega⟩
    let u : Fin n := j.rev
    let v : Fin n := i.rev
    refine ⟨z, u, v, ?_, ?_, ?_, ?_⟩
    · change 0 < n - (j.1 + 1)
      omega
    · change n - (i.1 + 1) = (n - (j.1 + 1)) + 1
      change j.1 = i.1 + 1 at hij
      omega
    · have hzero : reverseLehmerCode σ z = 0 :=
        reverseLehmerCode_eq_zero_of_val_eq_zero σ z rfl
      have hpos : 0 < lehmerCode σ j := by
        apply Finset.card_pos.mpr
        exact ⟨k, mem_rightSmaller.mpr ⟨hjk, hkj⟩⟩
      rw [hzero]
      simpa [u, reverseLehmerCode] using hpos
    · have hcode : lehmerCode σ j < lehmerCode σ i :=
        (descent_iff_lehmerCode_gt σ hij).mp hji
      simpa [u, v, reverseLehmerCode] using hcode
  · rintro ⟨x, u, v, hxu, huv, hxuCode, huvCode⟩
    let i : Fin n := v.rev
    let j : Fin n := u.rev
    have hij : Adjacent i j := by
      change n - (u.1 + 1) = (n - (v.1 + 1)) + 1
      change v.1 = u.1 + 1 at huv
      omega
    have hcode : lehmerCode σ j < lehmerCode σ i := by
      simpa [i, j, reverseLehmerCode] using huvCode
    have hji : σ j < σ i :=
      (descent_iff_lehmerCode_gt σ hij).mpr hcode
    have hpos : 0 < lehmerCode σ j := by
      have : 0 < reverseLehmerCode σ u :=
        (Nat.zero_le (reverseLehmerCode σ x)).trans_lt hxuCode
      simpa [j, reverseLehmerCode] using this
    obtain ⟨k, hjk, hkj⟩ := exists_right_smaller_of_lehmerCode_pos σ j hpos
    exact ⟨i, j, k, hij, hjk, hji, hkj⟩

/-- Proposition 2.3: `32-1` avoidance is transported to `0-12` avoidance. -/
theorem avoids32_1_iff_avoids0_12_reverseLehmerCode (σ : Equiv.Perm (Fin n)) :
    Avoids32_1 σ ↔ Avoids0_12 (reverseLehmerCode σ) := by
  exact not_congr (occurs32_1_iff_occurs0_12_reverseLehmerCode σ)

/-- Paper-numbered alias for Proposition 2.3. -/
theorem proposition_2_3 (σ : Equiv.Perm (Fin n)) :
    Avoids32_1 σ ↔ Avoids0_12 (reverseLehmerCode σ) :=
  avoids32_1_iff_avoids0_12_reverseLehmerCode σ

/-!
Proposition 2.4: in the reverse Lehmer code of a `32-1`-avoiding permutation,
the left entry of every strict rise is zero.
-/
theorem reverseLehmerCode_eq_zero_of_rise (σ : Equiv.Perm (Fin n))
    (havoid : Avoids32_1 σ) {j k : Fin n} (hjk : Adjacent j k)
    (hrise : reverseLehmerCode σ j < reverseLehmerCode σ k) :
    reverseLehmerCode σ j = 0 := by
  have havoid' : Avoids0_12 (reverseLehmerCode σ) :=
    (avoids32_1_iff_avoids0_12_reverseLehmerCode σ).mp havoid
  by_contra hne
  have hpos : 0 < reverseLehmerCode σ j := Nat.pos_of_ne_zero hne
  let z : Fin n := ⟨0, lt_of_le_of_lt (Nat.zero_le j.1) j.isLt⟩
  have hzero : reverseLehmerCode σ z = 0 :=
    reverseLehmerCode_eq_zero_of_val_eq_zero σ z rfl
  have hzj : z < j := by
    change 0 < j.1
    by_contra hj
    have hj0 : j.1 = 0 := by omega
    have := reverseLehmerCode_eq_zero_of_val_eq_zero σ j hj0
    omega
  apply havoid'
  have hzCode : reverseLehmerCode σ z < reverseLehmerCode σ j := by
    rw [hzero]
    exact hpos
  exact ⟨z, j, k, hzj, hjk, hzCode, hrise⟩

/-- Paper-numbered alias for Proposition 2.4. -/
theorem proposition_2_4 (σ : Equiv.Perm (Fin n))
    (havoid : Avoids32_1 σ) {j k : Fin n} (hjk : Adjacent j k)
    (hrise : reverseLehmerCode σ j < reverseLehmerCode σ k) :
    reverseLehmerCode σ j = 0 :=
  reverseLehmerCode_eq_zero_of_rise σ havoid hjk hrise

end LeanCo.Permutation
