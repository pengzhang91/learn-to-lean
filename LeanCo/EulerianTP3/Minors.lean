import Mathlib

/-!
# Minors of order at most three

This file supplies the finite-order form of the lower-triangular Fekete
criterion used in arXiv:2608.29224.  Everything is stated explicitly for
orders one, two, and three, so no total-positivity result is imported as a
black box.
-/

namespace LeanCo.EulerianTP3

/-- The determinant of the indicated two rows and two columns. -/
def det2 (M : ℕ → ℕ → ℝ) (i₀ i₁ j₀ j₁ : ℕ) : ℝ :=
  M i₀ j₀ * M i₁ j₁ - M i₀ j₁ * M i₁ j₀

/-- The determinant of the indicated three rows and three columns. -/
def det3 (M : ℕ → ℕ → ℝ) (i₀ i₁ i₂ j₀ j₁ j₂ : ℕ) : ℝ :=
  M i₀ j₀ * M i₁ j₁ * M i₂ j₂
    + M i₀ j₁ * M i₁ j₂ * M i₂ j₀
    + M i₀ j₂ * M i₁ j₀ * M i₂ j₁
    - M i₀ j₂ * M i₁ j₁ * M i₂ j₀
    - M i₀ j₁ * M i₁ j₀ * M i₂ j₂
    - M i₀ j₀ * M i₁ j₂ * M i₂ j₁

/-- Entries above the diagonal vanish. -/
def LowerTriangular (M : ℕ → ℕ → ℝ) : Prop :=
  ∀ i j, i < j → M i j = 0

/-- The solid minors through order three are strictly positive whenever
they are admissible. -/
structure SolidStrictUpToThree (M : ℕ → ℕ → ℝ) : Prop where
  entry_pos : ∀ i j, j ≤ i → 0 < M i j
  det2_pos : ∀ n k, k ≤ n → 0 < det2 M n (n + 1) k (k + 1)
  det3_pos : ∀ n k, k ≤ n → 0 < det3 M n (n + 1) (n + 2) k (k + 1) (k + 2)

/-- Strict positivity of every admissible minor through order three. -/
structure AdmissibleStrictUpToThree (M : ℕ → ℕ → ℝ) : Prop where
  entry_pos : ∀ i j, j ≤ i → 0 < M i j
  det2_pos : ∀ i₀ i₁ j₀ j₁, i₀ < i₁ → j₀ < j₁ →
    j₀ ≤ i₀ → j₁ ≤ i₁ → 0 < det2 M i₀ i₁ j₀ j₁
  det3_pos : ∀ i₀ i₁ i₂ j₀ j₁ j₂,
    i₀ < i₁ → i₁ < i₂ → j₀ < j₁ → j₁ < j₂ →
    j₀ ≤ i₀ → j₁ ≤ i₁ → j₂ ≤ i₂ →
    0 < det3 M i₀ i₁ i₂ j₀ j₁ j₂

/-- Total nonnegativity through order three, written without a variable-size
matrix API. -/
structure TotallyNonnegativeUpToThree (M : ℕ → ℕ → ℝ) : Prop where
  entry_nonneg : ∀ i j, 0 ≤ M i j
  det2_nonneg : ∀ i₀ i₁ j₀ j₁, i₀ < i₁ → j₀ < j₁ →
    0 ≤ det2 M i₀ i₁ j₀ j₁
  det3_nonneg : ∀ i₀ i₁ i₂ j₀ j₁ j₂,
    i₀ < i₁ → i₁ < i₂ → j₀ < j₁ → j₁ < j₂ →
    0 ≤ det3 M i₀ i₁ i₂ j₀ j₁ j₂

lemma det2_row_delete_identity (M : ℕ → ℕ → ℝ) (a b c x y : ℕ) :
    det2 M a c x y * M b x =
      det2 M a b x y * M c x + det2 M b c x y * M a x := by
  simp only [det2]
  ring

lemma det2_column_delete_identity (M : ℕ → ℕ → ℝ) (a b x y z : ℕ) :
    det2 M a b x z * M b y =
      det2 M a b y z * M b x + det2 M a b x y * M b z := by
  simp only [det2]
  ring

lemma det3_row_delete_identity (M : ℕ → ℕ → ℝ)
    (a b c d x y z : ℕ) :
    det3 M a b d x y z * det2 M b c x y =
      det3 M a b c x y z * det2 M b d x y
        + det3 M b c d x y z * det2 M a b x y := by
  simp only [det2, det3]
  ring

lemma det3_row_delete_identity' (M : ℕ → ℕ → ℝ)
    (a b c d x y z : ℕ) :
    det3 M a c d x y z * det2 M b c x y =
      det3 M a b c x y z * det2 M c d x y
        + det3 M b c d x y z * det2 M a c x y := by
  simp only [det2, det3]
  ring

lemma det3_column_delete_identity (M : ℕ → ℕ → ℝ)
    (i₀ i₁ i₂ a b c d : ℕ) :
    det3 M i₀ i₁ i₂ a c d * det2 M i₁ i₂ b c =
      det3 M i₀ i₁ i₂ b c d * det2 M i₁ i₂ a c
        + det3 M i₀ i₁ i₂ a b c * det2 M i₁ i₂ c d := by
  simp only [det2, det3]
  ring

lemma det3_column_delete_identity' (M : ℕ → ℕ → ℝ)
    (i₀ i₁ i₂ a b c d : ℕ) :
    det3 M i₀ i₁ i₂ a b d * det2 M i₁ i₂ b c =
      det3 M i₀ i₁ i₂ b c d * det2 M i₁ i₂ a b
        + det3 M i₀ i₁ i₂ a b c * det2 M i₁ i₂ b d := by
  simp only [det2, det3]
  ring

lemma det2_eq_zero_of_not_admissible (M : ℕ → ℕ → ℝ) (hM : LowerTriangular M)
    {i₀ i₁ j₀ j₁ : ℕ} (hi : i₀ < i₁) (hj : j₀ < j₁)
    (hbad : i₀ < j₀ ∨ i₁ < j₁) : det2 M i₀ i₁ j₀ j₁ = 0 := by
  rcases hbad with hbad | hbad
  · have h₀ := hM i₀ j₀ hbad
    have h₁ := hM i₀ j₁ (by omega)
    simp [det2, h₀, h₁]
  · have h₀ := hM i₀ j₁ (by omega)
    have h₁ := hM i₁ j₁ hbad
    simp [det2, h₀, h₁]

lemma det3_eq_zero_of_not_admissible (M : ℕ → ℕ → ℝ) (hM : LowerTriangular M)
    {i₀ i₁ i₂ j₀ j₁ j₂ : ℕ}
    (hi01 : i₀ < i₁) (hi12 : i₁ < i₂) (hj01 : j₀ < j₁) (hj12 : j₁ < j₂)
    (hbad : i₀ < j₀ ∨ i₁ < j₁ ∨ i₂ < j₂) :
    det3 M i₀ i₁ i₂ j₀ j₁ j₂ = 0 := by
  rcases hbad with hbad | hbad | hbad
  · have h₀ := hM i₀ j₀ hbad
    have h₁ := hM i₀ j₁ (by omega)
    have h₂ := hM i₀ j₂ (by omega)
    simp [det3, h₀, h₁, h₂]
  · have h₀ := hM i₀ j₁ (by omega)
    have h₁ := hM i₀ j₂ (by omega)
    have h₂ := hM i₁ j₁ hbad
    have h₃ := hM i₁ j₂ (by omega)
    simp [det3, h₀, h₁, h₂, h₃]
  · have h₀ := hM i₀ j₂ (by omega)
    have h₁ := hM i₁ j₂ (by omega)
    have h₂ := hM i₂ j₂ hbad
    simp [det3, h₀, h₁, h₂]

/-- Fekete's row propagation in order two, specialized to consecutive
columns. -/
theorem det2_consecutiveColumns_pos (M : ℕ → ℕ → ℝ)
    (hsolid : SolidStrictUpToThree M) (i₀ i₁ k : ℕ)
    (hi : i₀ < i₁) (hk : k ≤ i₀) :
    0 < det2 M i₀ i₁ k (k + 1) := by
  by_cases hs : i₁ = i₀ + 1
  · subst i₁
    exact hsolid.det2_pos i₀ k hk
  · have hi₀m : i₀ < i₁ - 1 := by omega
    have hmi₁ : i₁ - 1 < i₁ := by omega
    have hkm : k ≤ i₁ - 1 := hk.trans hi₀m.le
    have hleft := det2_consecutiveColumns_pos M hsolid i₀ (i₁ - 1) k hi₀m hk
    have hright : 0 < det2 M (i₁ - 1) i₁ k (k + 1) := by
      have hm : i₁ - 1 + 1 = i₁ := by omega
      simpa only [hm] using hsolid.det2_pos (i₁ - 1) k hkm
    have hmid := hsolid.entry_pos (i₁ - 1) k hkm
    have htop := hsolid.entry_pos i₀ k hk
    have hbot := hsolid.entry_pos i₁ k (by omega)
    have hid := det2_row_delete_identity M i₀ (i₁ - 1) i₁ k (k + 1)
    have hprod : 0 < det2 M i₀ i₁ k (k + 1) * M (i₁ - 1) k := by
      rw [hid]
      exact add_pos (mul_pos hleft hbot) (mul_pos hright htop)
    rcases mul_pos_iff.mp hprod with h | h
    · exact h.1
    · exact (not_lt_of_ge hmid.le h.2).elim
termination_by i₁ - i₀

/-- Every admissible second-order minor is positive once the solid minors
through order two are positive. -/
theorem det2_admissible_pos (M : ℕ → ℕ → ℝ) (htri : LowerTriangular M)
    (hsolid : SolidStrictUpToThree M) (i₀ i₁ j₀ j₁ : ℕ)
    (hi : i₀ < i₁) (hj : j₀ < j₁) (hadm₀ : j₀ ≤ i₀) (hadm₁ : j₁ ≤ i₁) :
    0 < det2 M i₀ i₁ j₀ j₁ := by
  by_cases hs : j₁ = j₀ + 1
  · subst j₁
    exact det2_consecutiveColumns_pos M hsolid i₀ i₁ j₀ hi hadm₀
  · let b := j₁ - 1
    have hj₀b : j₀ < b := by dsimp [b]; omega
    have hbj₁ : b < j₁ := by dsimp [b]; omega
    have hb_le_i₁ : b ≤ i₁ := hbj₁.le.trans hadm₁
    have hleft := det2_admissible_pos M htri hsolid i₀ i₁ j₀ b
      hi hj₀b hadm₀ hb_le_i₁
    have hshift : 0 ≤ det2 M i₀ i₁ b j₁ := by
      by_cases hb : b ≤ i₀
      · exact (det2_admissible_pos M htri hsolid i₀ i₁ b j₁
          hi hbj₁ hb hadm₁).le
      · have hbad : i₀ < b := by omega
        rw [det2_eq_zero_of_not_admissible M htri hi hbj₁ (Or.inl hbad)]
    have hden := hsolid.entry_pos i₁ b hb_le_i₁
    have hfirst := hsolid.entry_pos i₁ j₀ (hadm₀.trans hi.le)
    have hlast := hsolid.entry_pos i₁ j₁ hadm₁
    have hid := det2_column_delete_identity M i₀ i₁ j₀ b j₁
    have hprod : 0 < det2 M i₀ i₁ j₀ j₁ * M i₁ b := by
      rw [hid]
      exact add_pos_of_nonneg_of_pos (mul_nonneg hshift hfirst.le) (mul_pos hleft hlast)
    rcases mul_pos_iff.mp hprod with h | h
    · exact h.1
    · exact (not_lt_of_ge hden.le h.2).elim
termination_by j₁ - j₀

/-- Fekete's row propagation in order three, specialized to consecutive
columns. -/
theorem det3_consecutiveColumns_pos (M : ℕ → ℕ → ℝ)
    (htri : LowerTriangular M) (hsolid : SolidStrictUpToThree M)
    (i₀ i₁ i₂ k : ℕ) (hi01 : i₀ < i₁) (hi12 : i₁ < i₂) (hk : k ≤ i₀) :
    0 < det3 M i₀ i₁ i₂ k (k + 1) (k + 2) := by
  by_cases hlast : i₂ = i₁ + 1
  · by_cases hfirst : i₁ = i₀ + 1
    · subst i₁
      subst i₂
      simpa [Nat.add_assoc] using hsolid.det3_pos i₀ k hk
    · let b := i₀ + 1
      have hi₀b : i₀ < b := by simp [b]
      have hbi₁ : b < i₁ := by dsimp [b]; omega
      have hleft := det3_consecutiveColumns_pos M htri hsolid i₀ b i₁ k
        hi₀b hbi₁ hk
      have hright := det3_consecutiveColumns_pos M htri hsolid b i₁ i₂ k
        hbi₁ hi12 (hk.trans hi₀b.le)
      have hden := det2_consecutiveColumns_pos M hsolid b i₁ k hbi₁
        (hk.trans hi₀b.le)
      have hcd := det2_consecutiveColumns_pos M hsolid i₁ i₂ k hi12
        (hk.trans hi01.le)
      have hac := det2_consecutiveColumns_pos M hsolid i₀ i₁ k hi01 hk
      have hid := det3_row_delete_identity' M i₀ b i₁ i₂ k (k + 1) (k + 2)
      have hprod : 0 < det3 M i₀ i₁ i₂ k (k + 1) (k + 2) *
          det2 M b i₁ k (k + 1) := by
        rw [hid]
        exact add_pos (mul_pos hleft hcd) (mul_pos hright hac)
      rcases mul_pos_iff.mp hprod with h | h
      · exact h.1
      · exact (not_lt_of_ge hden.le h.2).elim
  · let c := i₂ - 1
    have hi₁c : i₁ < c := by dsimp [c]; omega
    have hci₂ : c < i₂ := by dsimp [c]; omega
    have hleft := det3_consecutiveColumns_pos M htri hsolid i₀ i₁ c k
      hi01 hi₁c hk
    have hright := det3_consecutiveColumns_pos M htri hsolid i₁ c i₂ k
      hi₁c hci₂ (hk.trans hi01.le)
    have hden := det2_consecutiveColumns_pos M hsolid i₁ c k hi₁c
      (hk.trans hi01.le)
    have hbd := det2_consecutiveColumns_pos M hsolid i₁ i₂ k hi12
      (hk.trans hi01.le)
    have hab := det2_consecutiveColumns_pos M hsolid i₀ i₁ k hi01 hk
    have hid := det3_row_delete_identity M i₀ i₁ c i₂ k (k + 1) (k + 2)
    have hprod : 0 < det3 M i₀ i₁ i₂ k (k + 1) (k + 2) *
        det2 M i₁ c k (k + 1) := by
      rw [hid]
      exact add_pos (mul_pos hleft hbd) (mul_pos hright hab)
    rcases mul_pos_iff.mp hprod with h | h
    · exact h.1
    · exact (not_lt_of_ge hden.le h.2).elim
termination_by i₂ - i₀

/-- Every admissible third-order minor is positive once the solid minors
through order three are positive. -/
theorem det3_admissible_pos (M : ℕ → ℕ → ℝ) (htri : LowerTriangular M)
    (hsolid : SolidStrictUpToThree M)
    (i₀ i₁ i₂ j₀ j₁ j₂ : ℕ)
    (hi01 : i₀ < i₁) (hi12 : i₁ < i₂) (hj01 : j₀ < j₁) (hj12 : j₁ < j₂)
    (hadm₀ : j₀ ≤ i₀) (hadm₁ : j₁ ≤ i₁) (hadm₂ : j₂ ≤ i₂) :
    0 < det3 M i₀ i₁ i₂ j₀ j₁ j₂ := by
  by_cases hfirst : j₁ = j₀ + 1
  · by_cases hsecond : j₂ = j₁ + 1
    · subst j₁
      subst j₂
      simpa [Nat.add_assoc] using
        det3_consecutiveColumns_pos M htri hsolid i₀ i₁ i₂ j₀ hi01 hi12 hadm₀
    · let c := j₂ - 1
      have hj₁c : j₁ < c := by dsimp [c]; omega
      have hcj₂ : c < j₂ := by dsimp [c]; omega
      have hc_le_i₂ : c ≤ i₂ := hcj₂.le.trans hadm₂
      have hlocal := det3_admissible_pos M htri hsolid i₀ i₁ i₂ j₀ j₁ c
        hi01 hi12 hj01 hj₁c hadm₀ hadm₁ hc_le_i₂
      have hshift : 0 ≤ det3 M i₀ i₁ i₂ j₁ c j₂ := by
        by_cases ha : j₁ ≤ i₀ ∧ c ≤ i₁
        · exact (det3_admissible_pos M htri hsolid i₀ i₁ i₂ j₁ c j₂
            hi01 hi12 hj₁c hcj₂ ha.1 ha.2 hadm₂).le
        · have hbad : i₀ < j₁ ∨ i₁ < c ∨ i₂ < j₂ := by omega
          rw [det3_eq_zero_of_not_admissible M htri hi01 hi12 hj₁c hcj₂ hbad]
      have hden := det2_admissible_pos M htri hsolid i₁ i₂ j₁ c
        hi12 hj₁c hadm₁ hc_le_i₂
      have hab := det2_admissible_pos M htri hsolid i₁ i₂ j₀ j₁
        hi12 hj01 (hadm₀.trans hi01.le) (hadm₁.trans hi12.le)
      have hbd := det2_admissible_pos M htri hsolid i₁ i₂ j₁ j₂
        hi12 hj12 hadm₁ hadm₂
      have hid := det3_column_delete_identity' M i₀ i₁ i₂ j₀ j₁ c j₂
      have hprod : 0 < det3 M i₀ i₁ i₂ j₀ j₁ j₂ * det2 M i₁ i₂ j₁ c := by
        rw [hid]
        exact add_pos_of_nonneg_of_pos (mul_nonneg hshift hab.le) (mul_pos hlocal hbd)
      rcases mul_pos_iff.mp hprod with h | h
      · exact h.1
      · exact (not_lt_of_ge hden.le h.2).elim
  · let b := j₁ - 1
    have hj₀b : j₀ < b := by dsimp [b]; omega
    have hbj₁ : b < j₁ := by dsimp [b]; omega
    have hb_le_i₁ : b ≤ i₁ := hbj₁.le.trans hadm₁
    have hlocal := det3_admissible_pos M htri hsolid i₀ i₁ i₂ j₀ b j₁
      hi01 hi12 hj₀b hbj₁ hadm₀ hb_le_i₁ (hadm₁.trans hi12.le)
    have hshift : 0 ≤ det3 M i₀ i₁ i₂ b j₁ j₂ := by
      by_cases hb : b ≤ i₀
      · exact (det3_admissible_pos M htri hsolid i₀ i₁ i₂ b j₁ j₂
          hi01 hi12 hbj₁ hj12 hb hadm₁ hadm₂).le
      · have hbad : i₀ < b ∨ i₁ < j₁ ∨ i₂ < j₂ := by omega
        rw [det3_eq_zero_of_not_admissible M htri hi01 hi12 hbj₁ hj12 hbad]
    have hden := det2_admissible_pos M htri hsolid i₁ i₂ b j₁
      hi12 hbj₁ hb_le_i₁ (hadm₁.trans hi12.le)
    have hac := det2_admissible_pos M htri hsolid i₁ i₂ j₀ j₁
      hi12 hj01 (hadm₀.trans hi01.le) (hadm₁.trans hi12.le)
    have hcd := det2_admissible_pos M htri hsolid i₁ i₂ j₁ j₂
      hi12 hj12 hadm₁ hadm₂
    have hid := det3_column_delete_identity M i₀ i₁ i₂ j₀ b j₁ j₂
    have hprod : 0 < det3 M i₀ i₁ i₂ j₀ j₁ j₂ * det2 M i₁ i₂ b j₁ := by
      rw [hid]
      exact add_pos_of_nonneg_of_pos (mul_nonneg hshift hac.le) (mul_pos hlocal hcd)
    rcases mul_pos_iff.mp hprod with h | h
    · exact h.1
    · exact (not_lt_of_ge hden.le h.2).elim
termination_by j₂ - j₀

/-- The explicit order-three lower-triangular Fekete criterion. -/
theorem admissibleStrictUpToThree_of_solid (M : ℕ → ℕ → ℝ)
    (htri : LowerTriangular M) (hsolid : SolidStrictUpToThree M) :
    AdmissibleStrictUpToThree M where
  entry_pos := hsolid.entry_pos
  det2_pos i₀ i₁ j₀ j₁ hi hj hadm₀ hadm₁ :=
    det2_admissible_pos M htri hsolid i₀ i₁ j₀ j₁ hi hj hadm₀ hadm₁
  det3_pos i₀ i₁ i₂ j₀ j₁ j₂ hi01 hi12 hj01 hj12 hadm₀ hadm₁ hadm₂ :=
    det3_admissible_pos M htri hsolid i₀ i₁ i₂ j₀ j₁ j₂
      hi01 hi12 hj01 hj12 hadm₀ hadm₁ hadm₂

/-- Strict positivity on the admissible minors and triangular structural
zeros together imply total nonnegativity through order three. -/
theorem totallyNonnegativeUpToThree_of_admissibleStrict
    (M : ℕ → ℕ → ℝ) (htri : LowerTriangular M)
    (hstrict : AdmissibleStrictUpToThree M) : TotallyNonnegativeUpToThree M where
  entry_nonneg i j := by
    by_cases h : j ≤ i
    · exact (hstrict.entry_pos i j h).le
    · rw [htri i j (by omega)]
  det2_nonneg i₀ i₁ j₀ j₁ hi hj := by
    by_cases h : j₀ ≤ i₀ ∧ j₁ ≤ i₁
    · exact (hstrict.det2_pos i₀ i₁ j₀ j₁ hi hj h.1 h.2).le
    · rw [det2_eq_zero_of_not_admissible M htri hi hj (by omega)]
  det3_nonneg i₀ i₁ i₂ j₀ j₁ j₂ hi01 hi12 hj01 hj12 := by
    by_cases h : j₀ ≤ i₀ ∧ j₁ ≤ i₁ ∧ j₂ ≤ i₂
    · exact (hstrict.det3_pos i₀ i₁ i₂ j₀ j₁ j₂ hi01 hi12 hj01 hj12
        h.1 h.2.1 h.2.2).le
    · rw [det3_eq_zero_of_not_admissible M htri hi01 hi12 hj01 hj12 (by omega)]

theorem totallyNonnegativeUpToThree_of_solid (M : ℕ → ℕ → ℝ)
    (htri : LowerTriangular M) (hsolid : SolidStrictUpToThree M) :
    TotallyNonnegativeUpToThree M :=
  totallyNonnegativeUpToThree_of_admissibleStrict M htri
    (admissibleStrictUpToThree_of_solid M htri hsolid)


end LeanCo.EulerianTP3
