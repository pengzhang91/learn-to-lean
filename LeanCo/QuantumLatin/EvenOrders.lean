import LeanCo.QuantumLatin.Fourier
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/-!
# The character-table construction in orders divisible by four

This file formalizes Construction 3.3 and Lemma 3.5 of Zhang--Cao for
`G = ZMod 2 × ZMod (2 * k)`.  The analytic part is first proved for an
arbitrary finite abelian group using all of its complex additive characters.
-/

open scoped BigOperators ComplexConjugate

namespace LeanCo.QuantumLatin

noncomputable section

section CharacterConstruction

variable {G : Type*} [AddCommGroup G] [Fintype G]

local instance characterCardNeZero : NeZero (Fintype.card G) :=
  ⟨Fintype.card_ne_zero⟩

/-- A noncanonical identification of a finite abelian group with its
Pontryagin dual.  Additivity is not needed: it is only used to give the
coordinate space the same index type as the rows and columns. -/
noncomputable def characterIndexEquiv : G ≃ AddChar G ℂ :=
  Fintype.equivOfCardEq AddChar.card_eq.symm

/-- The character-table ket before reindexing its coordinates by the dual. -/
noncomputable def characterKetRaw (mu : G → G) (a b : AddChar G ℂ) : Ket G :=
  fun t ↦ fourierScale (Fintype.card G) * (a (mu t) * b t)

/-- The literal ket used in the square, with coordinate type `AddChar G ℂ`. -/
noncomputable def characterKet (mu : G → G) (a b : AddChar G ℂ) :
    Ket (AddChar G ℂ) :=
  reindexKet characterIndexEquiv (characterKetRaw mu a b)

theorem dot_characterKetRaw (mu : G → G)
    (a b a' b' : AddChar G ℂ) :
    dot (characterKetRaw mu a b) (characterKetRaw mu a' b') =
      (Fintype.card G : ℂ)⁻¹ * ∑ t : G,
        (a' - a) (mu t) * (b' - b) t := by
  classical
  rw [dot]
  calc
    (∑ t : G, conj (characterKetRaw mu a b t) *
        characterKetRaw mu a' b' t) =
        (conj (fourierScale (Fintype.card G)) *
            fourierScale (Fintype.card G)) *
          ∑ t : G, (a' - a) (mu t) * (b' - b) t := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      simp only [characterKetRaw, map_mul, AddChar.sub_apply',
        div_eq_mul_inv, AddChar.inv_apply_eq_conj]
      ring
    _ = (Fintype.card G : ℂ)⁻¹ * ∑ t : G,
        (a' - a) (mu t) * (b' - b) t := by
      rw [fourierScale_star_mul]

theorem character_sum_normalized (a : AddChar G ℂ) :
    (Fintype.card G : ℂ)⁻¹ * ∑ t : G, a t =
      if a = 0 then 1 else 0 := by
  classical
  rw [AddChar.sum_eq_ite]
  split_ifs <;> simp

private theorem character_sum_comp_bijective
    (f : G → G) (hf : Function.Bijective f) (a : AddChar G ℂ) :
    (Fintype.card G : ℂ)⁻¹ * ∑ t : G, a (f t) =
      if a = 0 then 1 else 0 := by
  let e : G ≃ G := Equiv.ofBijective f hf
  rw [show (∑ t : G, a (f t)) = ∑ u : G, a u by
    simpa [e] using e.sum_comp (fun u ↦ a u)]
  exact character_sum_normalized a

theorem characterKet_row_orthonormal (mu : G → G) (a : AddChar G ℂ) :
    IsOrthonormal (fun b ↦ characterKet mu a b) := by
  classical
  intro b b'
  simp only [characterKet]
  rw [dot_reindexKet, dot_characterKetRaw]
  simp only [sub_self, AddChar.zero_apply, one_mul]
  simpa [sub_eq_zero, eq_comm] using character_sum_normalized (b' - b)

theorem characterKet_col_orthonormal (mu : G → G)
    (hmu : Function.Bijective mu) (b : AddChar G ℂ) :
    IsOrthonormal (fun a ↦ characterKet mu a b) := by
  classical
  intro a a'
  simp only [characterKet]
  rw [dot_reindexKet, dot_characterKetRaw]
  simp only [sub_self, AddChar.zero_apply, mul_one]
  simpa [sub_eq_zero, eq_comm] using
    character_sum_comp_bijective mu hmu (a' - a)

/-- The two algebraic hypotheses on a map used by the character-table
construction: it is complete, and no nonzero pair of characters yields a
constant product. -/
structure CharacterCertificate (mu : G → G) : Prop where
  perm : Function.Bijective mu
  complete : Function.Bijective (fun t ↦ mu t + t)
  separating : ∀ a b : AddChar G ℂ,
    (∀ t, a (mu t) * b t = a (mu 0)) → a = 0 ∧ b = 0

/-- Construction 3.3 over an arbitrary finite abelian group. -/
noncomputable def characterQLS (mu : G → G)
    (hmu : CharacterCertificate mu) : QuantumLatinSquare (AddChar G ℂ) where
  entry := characterKet mu
  row_orthonormal := characterKet_row_orthonormal mu
  col_orthonormal := characterKet_col_orthonormal mu hmu.perm

private theorem characterKet_transversal_orthonormal (mu : G → G)
    (hmu : CharacterCertificate mu) (c : AddChar G ℂ) :
    IsOrthonormal (fun a ↦ characterKet mu a (a + c)) := by
  classical
  intro a a'
  simp only [characterKet]
  rw [dot_reindexKet, dot_characterKetRaw]
  have hs : a' + c - (a + c) = a' - a := by abel
  rw [hs]
  have hprod : ∀ t : G,
      (a' - a) (mu t) * (a' - a) t = (a' - a) (mu t + t) := by
    intro t
    rw [AddChar.map_add_eq_mul]
  simp_rw [hprod]
  simpa [sub_eq_zero, eq_comm] using
    character_sum_comp_bijective (fun t ↦ mu t + t) hmu.complete (a' - a)

/-- The translates of the diagonal resolve the character-table square. -/
noncomputable def characterResolution (mu : G → G)
    (hmu : CharacterCertificate mu) : (characterQLS mu hmu).Resolution where
  column c := Equiv.addRight c
  covers a := by
    change Function.Bijective (fun c : AddChar G ℂ ↦ a + c)
    exact (Equiv.addLeft a).bijective
  orthonormal := characterKet_transversal_orthonormal mu hmu

private theorem addChar_apply_ne_zero (a : AddChar G ℂ) (x : G) : a x ≠ 0 := by
  intro h
  have hn := AddChar.norm_apply a x
  simp [h] at hn

private theorem characterCoeff_of_phase (mu : G → G)
    (i j i' j' : AddChar G ℂ) (z : ℂ)
    (h : ∀ t : G,
      i (mu t) * j t = z * (i' (mu t) * j' t)) :
    ∀ t : G, (i - i') (mu t) * (j - j') t = z := by
  intro t
  rw [AddChar.sub_apply', AddChar.sub_apply']
  calc
    i (mu t) / i' (mu t) * (j t / j' t) =
        (i (mu t) * j t) / (i' (mu t) * j' t) := by
      field_simp [addChar_apply_ne_zero]
      <;> ring
    _ = z := (div_eq_iff (mul_ne_zero (addChar_apply_ne_zero i' (mu t))
      (addChar_apply_ne_zero j' t))).2 (h t)

/-- The separating hypothesis gives the full `|G|²` projective
cardinality of Construction 3.3. -/
theorem characterQLS_maximal (mu : G → G)
    (hmu : CharacterCertificate mu) :
    (characterQLS mu hmu).HasMaximalCardinality := by
  intro i j i' j' hphase
  rcases hphase with ⟨z, _hz, hfun⟩
  have hcoeff : ∀ t : G,
      i (mu t) * j t = z * (i' (mu t) * j' t) := by
    intro t
    have ht := congrFun hfun (characterIndexEquiv t)
    change characterKet mu i j (characterIndexEquiv t) =
      z * characterKet mu i' j' (characterIndexEquiv t) at ht
    simp only [characterKet, reindexKet_apply, Equiv.symm_apply_apply,
      characterKetRaw] at ht
    apply mul_left_cancel₀ (fourierScale_ne_zero (Fintype.card G))
    calc
      fourierScale (Fintype.card G) * (i (mu t) * j t) =
          z * (fourierScale (Fintype.card G) * (i' (mu t) * j' t)) := ht
      _ = fourierScale (Fintype.card G) *
          (z * (i' (mu t) * j' t)) := by ring
  have hconstant : ∀ t : G,
      (i - i') (mu t) * (j - j') t = (i - i') (mu 0) := by
    intro t
    calc
      (i - i') (mu t) * (j - j') t = z :=
        characterCoeff_of_phase mu i j i' j' z hcoeff t
      _ = (i - i') (mu 0) * (j - j') 0 :=
        (characterCoeff_of_phase mu i j i' j' z hcoeff 0).symm
      _ = (i - i') (mu 0) := by simp
  rcases hmu.separating (i - i') (j - j') hconstant with ⟨hi, hj⟩
  exact ⟨sub_eq_zero.mp hi, sub_eq_zero.mp hj⟩

/-- Construction 3.3 packaged as a maximal resolvable QLS. -/
noncomputable def characterMaximalRQLS (mu : G → G)
    (hmu : CharacterCertificate mu) : MaximalRQLS (AddChar G ℂ) where
  square := characterQLS mu hmu
  resolution := characterResolution mu hmu
  maximal := characterQLS_maximal mu hmu

/-- Numerical-order packaging of the generic character construction. -/
theorem existsMaximalRQLS_of_characterCertificate (mu : G → G)
    (hmu : CharacterCertificate mu) :
    ExistsMaximalRQLS (Fintype.card G) := by
  simpa [AddChar.card_eq] using
    existsMaximalRQLS_card (characterMaximalRQLS mu hmu)

end CharacterConstruction

section EvenCompleteMapping

/-- First coordinate of the piecewise map in Lemma 3.5, on least
nonnegative representatives. -/
def evenMuFirstNat (k a x : ℕ) : ℕ :=
  if a = 0 then
    if x = 0 then 1
    else if x < k then 0
    else if x < 2 * k - 1 then 1
    else 0
  else
    if x < k - 1 then 1
    else if x = k - 1 then 0
    else if x = k then 1
    else 0

/-- Second coordinate of the piecewise map in Lemma 3.5, on least
nonnegative representatives. -/
def evenMuSecondNat (k a x : ℕ) : ℕ :=
  if a = 0 then
    if x = 0 then 0
    else if x < k then x
    else if x < 2 * k - 1 then x + 1
    else 0
  else
    if x < k - 1 then x + 1
    else if x = k - 1 then k
    else if x = k then k
    else x

theorem evenMuFirstNat_lt_two {k a x : ℕ} (ha : a < 2) :
    evenMuFirstNat k a x < 2 := by
  simp only [evenMuFirstNat]
  split_ifs <;> omega

theorem evenMuSecondNat_lt {k a x : ℕ} (hk : 3 ≤ k)
    (ha : a < 2) (hx : x < 2 * k) : evenMuSecondNat k a x < 2 * k := by
  simp only [evenMuSecondNat]
  split_ifs <;> omega

/-- The explicit complete mapping from Zhang--Cao, Lemma 3.5. -/
def evenMu (k : ℕ) : ZMod 2 × ZMod (2 * k) → ZMod 2 × ZMod (2 * k) :=
  fun p ↦ (evenMuFirstNat k p.1.val p.2.val,
    evenMuSecondNat k p.1.val p.2.val)

theorem evenMu_fst_val (hk : 3 ≤ k) (p : ZMod 2 × ZMod (2 * k)) :
    (evenMu k p).1.val = evenMuFirstNat k p.1.val p.2.val := by
  exact ZMod.val_cast_of_lt (evenMuFirstNat_lt_two p.1.val_lt)

theorem evenMu_snd_val (hk : 3 ≤ k) (p : ZMod 2 × ZMod (2 * k)) :
    (evenMu k p).2.val = evenMuSecondNat k p.1.val p.2.val := by
  letI : NeZero (2 * k) := ⟨by omega⟩
  exact ZMod.val_cast_of_lt
    (evenMuSecondNat_lt hk p.1.val_lt p.2.val_lt)

theorem evenMu_zero_zero (hk : 3 ≤ k) :
    evenMu k (0, 0) = (1, 0) := by
  letI : NeZero (2 * k) := ⟨by omega⟩
  apply Prod.ext <;> apply ZMod.val_injective
  · rw [evenMu_fst_val hk]
    norm_num [evenMuFirstNat, ZMod.val_one]
  · rw [evenMu_snd_val hk]
    simp [evenMuSecondNat]

theorem evenMu_zero_low (hk : 3 ≤ k) {x : ℕ}
    (hx0 : 0 < x) (hxk : x < k) :
    evenMu k (0, (x : ZMod (2 * k))) = (0, (x : ZMod (2 * k))) := by
  letI : NeZero (2 * k) := ⟨by omega⟩
  have hx2k : x < 2 * k := by omega
  apply Prod.ext <;> apply ZMod.val_injective
  · rw [evenMu_fst_val hk]
    simp [ZMod.val_cast_of_lt hx2k, evenMuFirstNat, hx0.ne', hxk,
      ZMod.val_one]
  · rw [evenMu_snd_val hk]
    simp [ZMod.val_cast_of_lt hx2k, evenMuSecondNat, hx0.ne', hxk]

theorem evenMu_zero_high (hk : 3 ≤ k) {x : ℕ}
    (hxk : k ≤ x) (hxlast : x < 2 * k - 1) :
    evenMu k (0, (x : ZMod (2 * k))) =
      (1, ((x + 1 : ℕ) : ZMod (2 * k))) := by
  letI : NeZero (2 * k) := ⟨by omega⟩
  have hx2k : x < 2 * k := by omega
  have hxp2k : x + 1 < 2 * k := by omega
  have hx0 : x ≠ 0 := by omega
  have hxnotlow : ¬x < k := by omega
  apply Prod.ext <;> apply ZMod.val_injective
  · rw [evenMu_fst_val hk]
    simp [ZMod.val_cast_of_lt hx2k, evenMuFirstNat, hxlast,
      ZMod.val_one, hx0, hxnotlow]
  · rw [evenMu_snd_val hk]
    simp only [Prod.fst, Prod.snd, ZMod.val_zero,
      ZMod.val_cast_of_lt hx2k, ZMod.val_natCast,
      Nat.mod_eq_of_lt hxp2k]
    simp [evenMuSecondNat, hxlast, hx0, hxnotlow]

theorem evenMu_zero_last (hk : 3 ≤ k) :
    evenMu k (0, ((2 * k - 1 : ℕ) : ZMod (2 * k))) = (0, 0) := by
  letI : NeZero (2 * k) := ⟨by omega⟩
  have hlast : 2 * k - 1 < 2 * k := by omega
  have hne0 : 2 * k - 1 ≠ 0 := by omega
  have hnlow : ¬2 * k - 1 < k := by omega
  apply Prod.ext <;> apply ZMod.val_injective
  · rw [evenMu_fst_val hk]
    simp [ZMod.val_cast_of_lt hlast, evenMuFirstNat, hne0, hnlow]
  · rw [evenMu_snd_val hk]
    simp [ZMod.val_cast_of_lt hlast, evenMuSecondNat, hne0, hnlow]

theorem evenMu_one_low (hk : 3 ≤ k) {x : ℕ} (hx : x < k - 1) :
    evenMu k (1, (x : ZMod (2 * k))) =
      (1, ((x + 1 : ℕ) : ZMod (2 * k))) := by
  letI : NeZero (2 * k) := ⟨by omega⟩
  have hx2k : x < 2 * k := by omega
  have hxp2k : x + 1 < 2 * k := by omega
  apply Prod.ext <;> apply ZMod.val_injective
  · rw [evenMu_fst_val hk]
    simp [ZMod.val_cast_of_lt hx2k, evenMuFirstNat, hx, ZMod.val_one]
  · rw [evenMu_snd_val hk]
    simp only [Prod.fst, Prod.snd, ZMod.val_one,
      ZMod.val_cast_of_lt hx2k, ZMod.val_natCast,
      Nat.mod_eq_of_lt hxp2k]
    simp [evenMuSecondNat, hx]

theorem evenMu_one_before_mid (hk : 3 ≤ k) :
    evenMu k (1, ((k - 1 : ℕ) : ZMod (2 * k))) =
      (0, (k : ZMod (2 * k))) := by
  letI : NeZero (2 * k) := ⟨by omega⟩
  have hkm1 : k - 1 < 2 * k := by omega
  have hk2k : k < 2 * k := by omega
  apply Prod.ext <;> apply ZMod.val_injective
  · rw [evenMu_fst_val hk]
    simp [ZMod.val_cast_of_lt hkm1, evenMuFirstNat, ZMod.val_one]
  · rw [evenMu_snd_val hk]
    simp [ZMod.val_cast_of_lt hkm1, ZMod.val_cast_of_lt hk2k,
      evenMuSecondNat]

theorem evenMu_one_mid (hk : 3 ≤ k) :
    evenMu k (1, (k : ZMod (2 * k))) =
      (1, (k : ZMod (2 * k))) := by
  letI : NeZero (2 * k) := ⟨by omega⟩
  have hk2k : k < 2 * k := by omega
  have hnlow : ¬k < k - 1 := by omega
  have hnbefore : k ≠ k - 1 := by omega
  apply Prod.ext <;> apply ZMod.val_injective
  · rw [evenMu_fst_val hk]
    simp [ZMod.val_cast_of_lt hk2k, evenMuFirstNat, ZMod.val_one,
      hnlow, hnbefore]
  · rw [evenMu_snd_val hk]
    simp [ZMod.val_cast_of_lt hk2k, evenMuSecondNat, hnlow, hnbefore]

theorem evenMu_one_high (hk : 3 ≤ k) {x : ℕ}
    (hx : k < x) (hx2k : x < 2 * k) :
    evenMu k (1, (x : ZMod (2 * k))) =
      (0, (x : ZMod (2 * k))) := by
  letI : NeZero (2 * k) := ⟨by omega⟩
  have hnlow : ¬x < k - 1 := by omega
  have hnbefore : x ≠ k - 1 := by omega
  have hnmid : x ≠ k := by omega
  apply Prod.ext <;> apply ZMod.val_injective
  · rw [evenMu_fst_val hk]
    simp [ZMod.val_cast_of_lt hx2k, evenMuFirstNat, ZMod.val_one,
      hnlow, hnbefore, hnmid]
  · rw [evenMu_snd_val hk]
    simp [ZMod.val_cast_of_lt hx2k, evenMuSecondNat,
      hnlow, hnbefore, hnmid]

private theorem zmodTwo_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have ha := a.val_lt
  interval_cases h : a.val
  · left
    apply ZMod.val_injective
    simpa [h]
  · right
    apply ZMod.val_injective
    simpa [h, ZMod.val_one]

/-- The map of Lemma 3.5 is a permutation. -/
theorem evenMu_surjective (hk : 3 ≤ k) : Function.Surjective (evenMu k) := by
  letI : NeZero (2 * k) := ⟨by omega⟩
  rintro ⟨a, y⟩
  have hylt := y.val_lt
  rcases zmodTwo_eq_zero_or_one a with rfl | rfl
  · by_cases hy0 : y.val = 0
    · refine ⟨(0, ((2 * k - 1 : ℕ) : ZMod (2 * k))), ?_⟩
      rw [evenMu_zero_last hk]
      apply Prod.ext
      · rfl
      · apply ZMod.val_injective
        simpa [hy0]
    · by_cases hylow : y.val < k
      · refine ⟨(0, y), ?_⟩
        rw [← ZMod.natCast_zmod_val y]
        exact evenMu_zero_low hk (Nat.pos_of_ne_zero hy0) hylow
      · by_cases hmid : y.val = k
        · refine ⟨(1, ((k - 1 : ℕ) : ZMod (2 * k))), ?_⟩
          rw [evenMu_one_before_mid hk]
          apply Prod.ext
          · rfl
          · apply ZMod.val_injective
            rw [ZMod.val_cast_of_lt (by omega)]
            exact hmid.symm
        · refine ⟨(1, y), ?_⟩
          rw [← ZMod.natCast_zmod_val y]
          apply evenMu_one_high hk <;> omega
  · by_cases hy0 : y.val = 0
    · refine ⟨(0, 0), ?_⟩
      rw [evenMu_zero_zero hk]
      apply Prod.ext
      · rfl
      · apply ZMod.val_injective
        simpa [hy0]
    · by_cases hylow : y.val < k
      · let x := y.val - 1
        have hx : x < k - 1 := by dsimp [x]; omega
        refine ⟨(1, (x : ZMod (2 * k))), ?_⟩
        rw [evenMu_one_low hk hx]
        apply Prod.ext
        · rfl
        · apply ZMod.val_injective
          rw [ZMod.val_cast_of_lt (by dsimp [x]; omega)]
          dsimp [x]
          omega
      · by_cases hmid : y.val = k
        · refine ⟨(1, (k : ZMod (2 * k))), ?_⟩
          rw [evenMu_one_mid hk]
          apply Prod.ext
          · rfl
          · apply ZMod.val_injective
            rw [ZMod.val_cast_of_lt (by omega)]
            exact hmid.symm
        · let x := y.val - 1
          have hxk : k ≤ x := by dsimp [x]; omega
          have hxlast : x < 2 * k - 1 := by dsimp [x]; omega
          refine ⟨(0, (x : ZMod (2 * k))), ?_⟩
          rw [evenMu_zero_high hk hxk hxlast]
          apply Prod.ext
          · rfl
          · apply ZMod.val_injective
            rw [ZMod.val_cast_of_lt (by dsimp [x]; omega)]
            dsimp [x]
            omega

theorem evenMu_bijective (hk : 3 ≤ k) : Function.Bijective (evenMu k) := by
  letI : NeZero (2 * k) := ⟨by omega⟩
  exact (evenMu_surjective hk).bijective_of_finite

/-- The pointwise sum `id + mu` from the definition of a complete mapping. -/
def evenComplete (k : ℕ) :
    ZMod 2 × ZMod (2 * k) → ZMod 2 × ZMod (2 * k) :=
  fun p ↦ evenMu k p + p

theorem evenComplete_zero_zero (hk : 3 ≤ k) :
    evenComplete k (0, 0) = (1, 0) := by
  rw [evenComplete, evenMu_zero_zero hk]
  simp

theorem evenComplete_zero_low (hk : 3 ≤ k) {x : ℕ}
    (hx0 : 0 < x) (hxk : x < k) :
    evenComplete k (0, (x : ZMod (2 * k))) =
      (0, ((2 * x : ℕ) : ZMod (2 * k))) := by
  rw [evenComplete, evenMu_zero_low hk hx0 hxk]
  apply Prod.ext <;> simp
  ring_nf

theorem evenComplete_zero_high (hk : 3 ≤ k) {x : ℕ}
    (hxk : k ≤ x) (hxlast : x < 2 * k - 1) :
    evenComplete k (0, (x : ZMod (2 * k))) =
      (1, ((2 * x + 1 : ℕ) : ZMod (2 * k))) := by
  rw [evenComplete, evenMu_zero_high hk hxk hxlast]
  apply Prod.ext <;> simp
  ring

theorem evenComplete_zero_last (hk : 3 ≤ k) :
    evenComplete k (0, ((2 * k - 1 : ℕ) : ZMod (2 * k))) =
      (0, ((2 * k - 1 : ℕ) : ZMod (2 * k))) := by
  rw [evenComplete, evenMu_zero_last hk]
  simp

theorem evenComplete_one_low (hk : 3 ≤ k) {x : ℕ} (hx : x < k - 1) :
    evenComplete k (1, (x : ZMod (2 * k))) =
      (0, ((2 * x + 1 : ℕ) : ZMod (2 * k))) := by
  rw [evenComplete, evenMu_one_low hk hx]
  apply Prod.ext
  · exact ZMod.natCast_self 2
  · simp
    ring_nf

theorem evenComplete_one_before_mid (hk : 3 ≤ k) :
    evenComplete k (1, ((k - 1 : ℕ) : ZMod (2 * k))) =
      (1, ((2 * k - 1 : ℕ) : ZMod (2 * k))) := by
  rw [evenComplete, evenMu_one_before_mid hk]
  apply Prod.ext
  · simp
  · simp
    rw [← Nat.cast_add]
    congr 1
    omega

theorem evenComplete_one_mid (hk : 3 ≤ k) :
    evenComplete k (1, (k : ZMod (2 * k))) = (0, 0) := by
  rw [evenComplete, evenMu_one_mid hk]
  apply Prod.ext
  · exact ZMod.natCast_self 2
  · simp
    rw [← Nat.cast_add]
    have h : k + k = 2 * k := by omega
    rw [h, ZMod.natCast_self]

theorem evenComplete_one_high (hk : 3 ≤ k) {x : ℕ}
    (hx : k < x) (hx2k : x < 2 * k) :
    evenComplete k (1, (x : ZMod (2 * k))) =
      (1, ((2 * x : ℕ) : ZMod (2 * k))) := by
  rw [evenComplete, evenMu_one_high hk hx hx2k]
  apply Prod.ext <;> simp
  ring_nf

/-- The pointwise sum `id + mu` is also a permutation. -/
theorem evenComplete_surjective (hk : 3 ≤ k) :
    Function.Surjective (evenComplete k) := by
  letI : NeZero (2 * k) := ⟨by omega⟩
  rintro ⟨a, y⟩
  have hylt := y.val_lt
  rcases zmodTwo_eq_zero_or_one a with rfl | rfl
  · by_cases hy0 : y.val = 0
    · refine ⟨(1, (k : ZMod (2 * k))), ?_⟩
      rw [evenComplete_one_mid hk]
      apply Prod.ext
      · rfl
      · apply ZMod.val_injective
        simpa [hy0]
    · by_cases hylast : y.val = 2 * k - 1
      · refine ⟨(0, ((2 * k - 1 : ℕ) : ZMod (2 * k))), ?_⟩
        rw [evenComplete_zero_last hk]
        apply Prod.ext
        · rfl
        · apply ZMod.val_injective
          rw [ZMod.val_cast_of_lt (by omega)]
          exact hylast.symm
      · by_cases heven : y.val % 2 = 0
        · let x := y.val / 2
          have hx0 : 0 < x := by dsimp [x]; omega
          have hxk : x < k := by dsimp [x]; omega
          have hxy : 2 * x = y.val := by dsimp [x]; omega
          refine ⟨(0, (x : ZMod (2 * k))), ?_⟩
          rw [evenComplete_zero_low hk hx0 hxk]
          apply Prod.ext
          · rfl
          · rw [hxy, ZMod.natCast_zmod_val]
        · let x := (y.val - 1) / 2
          have hodd : y.val % 2 = 1 := by omega
          have hx : x < k - 1 := by dsimp [x]; omega
          have hxy : 2 * x + 1 = y.val := by dsimp [x]; omega
          refine ⟨(1, (x : ZMod (2 * k))), ?_⟩
          rw [evenComplete_one_low hk hx]
          apply Prod.ext
          · rfl
          · rw [hxy, ZMod.natCast_zmod_val]
  · by_cases hy0 : y.val = 0
    · refine ⟨(0, 0), ?_⟩
      rw [evenComplete_zero_zero hk]
      apply Prod.ext
      · rfl
      · apply ZMod.val_injective
        simpa [hy0]
    · by_cases hylast : y.val = 2 * k - 1
      · refine ⟨(1, ((k - 1 : ℕ) : ZMod (2 * k))), ?_⟩
        rw [evenComplete_one_before_mid hk]
        apply Prod.ext
        · rfl
        · apply ZMod.val_injective
          rw [ZMod.val_cast_of_lt (by omega)]
          exact hylast.symm
      · by_cases heven : y.val % 2 = 0
        · let x := k + y.val / 2
          have hxk : k < x := by dsimp [x]; omega
          have hx2k : x < 2 * k := by dsimp [x]; omega
          have hxy : 2 * x = 2 * k + y.val := by dsimp [x]; omega
          refine ⟨(1, (x : ZMod (2 * k))), ?_⟩
          rw [evenComplete_one_high hk hxk hx2k]
          apply Prod.ext
          · rfl
          · rw [hxy, Nat.cast_add, ZMod.natCast_self, zero_add,
              ZMod.natCast_zmod_val]
        · let x := k + (y.val - 1) / 2
          have hodd : y.val % 2 = 1 := by omega
          have hxk : k ≤ x := by dsimp [x]; omega
          have hxlast : x < 2 * k - 1 := by dsimp [x]; omega
          have hxy : 2 * x + 1 = 2 * k + y.val := by dsimp [x]; omega
          refine ⟨(0, (x : ZMod (2 * k))), ?_⟩
          rw [evenComplete_zero_high hk hxk hxlast]
          apply Prod.ext
          · rfl
          · rw [hxy, Nat.cast_add, ZMod.natCast_self, zero_add,
              ZMod.natCast_zmod_val]

theorem evenComplete_bijective (hk : 3 ≤ k) :
    Function.Bijective (evenComplete k) := by
  letI : NeZero (2 * k) := ⟨by omega⟩
  exact (evenComplete_surjective hk).bijective_of_finite

private theorem addChar_apply_first_generator (k : ℕ)
    (a : AddChar (ZMod 2 × ZMod (2 * k)) ℂ) (x : ZMod 2) :
    a (x, 0) = a (1, 0) ^ x.val := by
  rw [show (x, (0 : ZMod (2 * k))) = x.val •
      ((1 : ZMod 2), (0 : ZMod (2 * k))) by
    apply Prod.ext
    · simpa using (ZMod.natCast_zmod_val x).symm
    · simp]
  exact AddChar.map_nsmul_eq_pow _ _ _

private theorem addChar_apply_second_generator (k : ℕ) [NeZero (2 * k)]
    (a : AddChar (ZMod 2 × ZMod (2 * k)) ℂ) (x : ZMod (2 * k)) :
    a (0, x) = a (0, 1) ^ x.val := by
  rw [show ((0 : ZMod 2), x) = x.val •
      ((0 : ZMod 2), (1 : ZMod (2 * k))) by
    apply Prod.ext
    · simp
    · simpa using (ZMod.natCast_zmod_val x).symm]
  exact AddChar.map_nsmul_eq_pow _ _ _

private theorem addChar_eq_zero_of_generator_values (k : ℕ) [NeZero (2 * k)]
    (a : AddChar (ZMod 2 × ZMod (2 * k)) ℂ)
    (hfirst : a (1, 0) = 1) (hsecond : a (0, 1) = 1) : a = 0 := by
  apply AddChar.ext
  rintro ⟨x, y⟩
  rw [show (x, y) = (x, 0) + (0, y) by ext <;> simp,
    AddChar.map_add_eq_mul, addChar_apply_first_generator,
    addChar_apply_second_generator, hfirst, hsecond]
  simp

/-- The four evaluations used in Lemma 3.5 force both characters to be
trivial.  This is the paper's maximal-cardinality side condition. -/
theorem evenMu_separating (hk : 3 ≤ k)
    (a b : AddChar (ZMod 2 × ZMod (2 * k)) ℂ)
    (h : ∀ t, a (evenMu k t) * b t = a (evenMu k 0)) :
    a = 0 ∧ b = 0 := by
  letI : NeZero (2 * k) := ⟨by omega⟩
  let e₁ : ZMod 2 × ZMod (2 * k) := (1, 0)
  let e₂ : ZMod 2 × ZMod (2 * k) := (0, 1)
  let e₂₂ : ZMod 2 × ZMod (2 * k) := (0, 2)
  let c : AddChar (ZMod 2 × ZMod (2 * k)) ℂ := a + b
  have hmu₁ : evenMu k e₂ = e₂ := by
    simpa [e₂] using evenMu_zero_low hk (x := 1) (by omega) (by omega)
  have hmu₂ : evenMu k e₂₂ = e₂₂ := by
    simpa [e₂₂] using evenMu_zero_low hk (x := 2) (by omega) (by omega)
  have hc₁ : c e₂ = a (evenMu k 0) := by
    have ht := h e₂
    rw [hmu₁] at ht
    simpa only [c, AddChar.add_apply] using ht
  have hc₂ : c e₂₂ = a (evenMu k 0) := by
    have ht := h e₂₂
    rw [hmu₂] at ht
    simpa only [c, AddChar.add_apply] using ht
  have he₂₂ : e₂₂ = 2 • e₂ := by
    ext <;> simp [e₂₂, e₂]
  have hc_sq : c e₂₂ = c e₂ ^ 2 := by
    rw [he₂₂]
    exact AddChar.map_nsmul_eq_pow c 2 e₂
  have hc_mul : c e₂ = c e₂ * c e₂ := by
    calc
      c e₂ = a (evenMu k 0) := hc₁
      _ = c e₂₂ := hc₂.symm
      _ = c e₂ ^ 2 := hc_sq
      _ = c e₂ * c e₂ := pow_two _
  have hc_ne : c e₂ ≠ 0 := addChar_apply_ne_zero c e₂
  have hc_gen : c e₂ = 1 :=
    mul_left_cancel₀ hc_ne (by simpa using hc_mul.symm)
  have hcommon : a (evenMu k 0) = 1 := hc₁.symm.trans hc_gen
  have hmu_zero : evenMu k (0 : ZMod 2 × ZMod (2 * k)) = e₁ := by
    change evenMu k (0, 0) = (1, 0)
    exact evenMu_zero_zero hk
  have ha_first : a e₁ = 1 := by
    calc
      a e₁ = a (evenMu k 0) := (congrArg a hmu_zero).symm
      _ = 1 := hcommon
  have hc_second (x : ZMod (2 * k)) : c (0, x) = 1 := by
    rw [addChar_apply_second_generator, show c (0, 1) = c e₂ by rfl,
      hc_gen, one_pow]
  let q : ZMod (2 * k) := (k + 1 : ℕ)
  have hmu_q : evenMu k (1, q) = (0, q) := by
    simpa [q] using evenMu_one_high hk (x := k + 1) (by omega) (by omega)
  have hq := h (1, q)
  rw [hmu_q] at hq
  have hc_q : a (0, q) * b (0, q) = 1 := by
    simpa [c, AddChar.add_apply] using hc_second q
  have hb_decomp : b (1, q) = b e₁ * b (0, q) := by
    rw [show (1, q) = e₁ + (0, q) by ext <;> simp [e₁],
      AddChar.map_add_eq_mul]
  have hb_first : b e₁ = 1 := by
    calc
      b e₁ = (a (0, q) * b (0, q)) * b e₁ := by rw [hc_q]; simp
      _ = a (0, q) * (b e₁ * b (0, q)) := by ring
      _ = a (0, q) * b (1, q) := by rw [hb_decomp]
      _ = a (evenMu k 0) := hq
      _ = 1 := hcommon
  let r : ZMod (2 * k) := k
  have hmu_r : evenMu k (0, r) = (1, q) := by
    simpa [q, r] using evenMu_zero_high hk (x := k) (by omega) (by omega)
  have hr := h (0, r)
  rw [hmu_r] at hr
  have hc_r : a (0, r) * b (0, r) = 1 := by
    simpa [c, AddChar.add_apply] using hc_second r
  have ha_q : a (0, q) = a e₂ * a (0, r) := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    apply Prod.ext
    · simp [e₂]
    · simp [q, r]
      ring
  have ha_decomp : a (1, q) = a e₁ * a (0, q) := by
    rw [show (1, q) = e₁ + (0, q) by ext <;> simp [e₁],
      AddChar.map_add_eq_mul]
  have ha_second : a e₂ = 1 := by
    calc
      a e₂ = a e₂ * (a (0, r) * b (0, r)) := by rw [hc_r]; simp
      _ = (a e₂ * a (0, r)) * b (0, r) := by ring
      _ = a (0, q) * b (0, r) := by rw [ha_q]
      _ = (a e₁ * a (0, q)) * b (0, r) := by rw [ha_first]; simp
      _ = a (1, q) * b (0, r) := by rw [ha_decomp]
      _ = a (evenMu k 0) := hr
      _ = 1 := hcommon
  have ha_zero : a = 0 :=
    addChar_eq_zero_of_generator_values k a ha_first ha_second
  have hb_second : b e₂ = 1 := by
    have hc := hc_gen
    change (a + b) e₂ = 1 at hc
    rw [AddChar.add_apply, ha_second, one_mul] at hc
    exact hc
  have hb_zero : b = 0 :=
    addChar_eq_zero_of_generator_values k b hb_first hb_second
  exact ⟨ha_zero, hb_zero⟩

/-- Lemma 3.5, bundled in exactly the form consumed by Construction 3.3. -/
theorem evenMu_characterCertificate (hk : 3 ≤ k) :
    CharacterCertificate (evenMu k) where
  perm := evenMu_bijective hk
  complete := by
    change Function.Bijective (evenComplete k)
    exact evenComplete_bijective hk
  separating := evenMu_separating hk

/-- Zhang--Cao's main complete-mapping family: every order `4 * k`, with
`k ≥ 3`, admits a maximal-cardinality resolvable quantum Latin square. -/
theorem existsMaximalRQLS_four_mul (k : ℕ) (hk : 3 ≤ k) :
    ExistsMaximalRQLS (4 * k) := by
  letI : NeZero (2 * k) := ⟨by omega⟩
  have h :=
    existsMaximalRQLS_of_characterCertificate (evenMu k)
      (evenMu_characterCertificate hk)
  simp only [Fintype.card_prod, ZMod.card] at h
  convert h using 1 <;> omega

end EvenCompleteMapping

end

end LeanCo.QuantumLatin
