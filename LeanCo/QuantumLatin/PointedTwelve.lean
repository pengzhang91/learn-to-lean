import LeanCo.QuantumLatin.Fourier
import LeanCo.QuantumLatin.Incomplete
import LeanCo.QuantumLatin.SeparatedCopies
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Tactic

/-!
# A regular pointed maximal RQLS of order twelve

This file gives a self-contained finite version of the character construction
on `Z/2 × Z/6`.  Coefficients are calculated exactly in `ℚ(ζ₆)`.  An inverse
character transform sends the `(0,0)` entry to basis zero, after which a
rational Householder reflection on the eleven surviving coordinates makes
two fixed coordinates nonzero in all other 143 entries.
-/

open scoped BigOperators ComplexConjugate Matrix

namespace LeanCo.QuantumLatin

attribute [local instance] Fintype.decidableForallFintype

/-! ## Exact sixth-cyclotomic coefficients -/

/-- The canonical expression `a + bζ`, where `ζ² - ζ + 1 = 0`. -/
structure CycloSix where
  rat : ℚ
  zeta : ℚ
deriving DecidableEq

namespace CycloSix

def zero : CycloSix := ⟨0, 0⟩
def one : CycloSix := ⟨1, 0⟩
def ofRat (q : ℚ) : CycloSix := ⟨q, 0⟩
def neg (x : CycloSix) : CycloSix := ⟨-x.rat, -x.zeta⟩
def add (x y : CycloSix) : CycloSix := ⟨x.rat + y.rat, x.zeta + y.zeta⟩
def sub (x y : CycloSix) : CycloSix := add x (neg y)

/-- Multiplication reduced using `ζ² = ζ - 1`. -/
def mul (x y : CycloSix) : CycloSix :=
  ⟨x.rat * y.rat - x.zeta * y.zeta,
    x.rat * y.zeta + x.zeta * y.rat + x.zeta * y.zeta⟩

/-- Complex conjugation uses `conj ζ = 1 - ζ`. -/
def conjugate (x : CycloSix) : CycloSix :=
  ⟨x.rat + x.zeta, -x.zeta⟩

def scaleRat (q : ℚ) (x : CycloSix) : CycloSix :=
  ⟨q * x.rat, q * x.zeta⟩

/-- The embedding with `ζ = (1 + i√3)/2`. -/
noncomputable def embed (x : CycloSix) : ℂ :=
  ⟨(x.rat : ℝ) + (x.zeta : ℝ) / 2,
    (x.zeta : ℝ) * Real.sqrt 3 / 2⟩

@[simp] theorem embed_zero : embed zero = 0 := by
  apply Complex.ext <;> simp [embed, zero]

@[simp] theorem embed_one : embed one = 1 := by
  apply Complex.ext <;> simp [embed, one]

@[simp] theorem embed_ofRat (q : ℚ) : embed (ofRat q) = (q : ℂ) := by
  apply Complex.ext <;> simp [embed, ofRat]

@[simp] theorem embed_neg (x : CycloSix) : embed (neg x) = -embed x := by
  apply Complex.ext <;> simp [embed, neg] <;> ring

@[simp] theorem embed_add (x y : CycloSix) : embed (add x y) = embed x + embed y := by
  apply Complex.ext <;> simp [embed, add] <;> ring

@[simp] theorem embed_sub (x y : CycloSix) : embed (sub x y) = embed x - embed y := by
  rw [sub, embed_add, embed_neg]
  ring

@[simp] theorem embed_scaleRat (q : ℚ) (x : CycloSix) :
    embed (scaleRat q x) = (q : ℂ) * embed x := by
  apply Complex.ext <;> simp [embed, scaleRat] <;> ring

@[simp] theorem embed_mul (x y : CycloSix) : embed (mul x y) = embed x * embed y := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by positivity)
  apply Complex.ext <;>
    simp [embed, mul, Complex.mul_re, Complex.mul_im] <;> ring_nf
  all_goals simp only [hs]
  all_goals ring

@[simp] theorem embed_conjugate (x : CycloSix) :
    embed (conjugate x) = star (embed x) := by
  apply Complex.ext <;> simp [embed, conjugate] <;> ring

theorem embed_injective : Function.Injective embed := by
  intro x y hxy
  have hsqrt : Real.sqrt 3 ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
  have him := congrArg Complex.im hxy
  dsimp [embed] at him
  have hzetaR : (x.zeta : ℝ) = (y.zeta : ℝ) := by
    apply (mul_right_cancel₀ hsqrt)
    linarith
  have hzeta : x.zeta = y.zeta := by exact_mod_cast hzetaR
  have hre := congrArg Complex.re hxy
  dsimp [embed] at hre
  have hratR : (x.rat : ℝ) = (y.rat : ℝ) := by
    rw [hzeta] at hre
    linarith
  have hrat : x.rat = y.rat := by exact_mod_cast hratR
  cases x
  cases y
  simp_all

theorem embed_ne_zero {x : CycloSix} (hx : x ≠ zero) : embed x ≠ 0 := by
  intro h
  apply hx
  apply embed_injective
  simpa using h

end CycloSix

/-! ## The concrete group `Z/2 × Z/6`, encoded by `Fin 12` -/

def twelveDecode (x : Fin 12) : Fin 2 × Fin 6 :=
  finProdFinEquiv.symm x

def twelveEncode (x : Fin 2 × Fin 6) : Fin 12 :=
  finProdFinEquiv x

def twelveMk (a x : ℕ) : Fin 12 :=
  twelveEncode
    (⟨a % 2, Nat.mod_lt _ (by decide)⟩,
      ⟨x % 6, Nat.mod_lt _ (by decide)⟩)

/-- Addition in the encoded product group. -/
def twelveAdd (x y : Fin 12) : Fin 12 :=
  twelveMk ((twelveDecode x).1.1 + (twelveDecode y).1.1)
    ((twelveDecode x).2.1 + (twelveDecode y).2.1)

def twelveNeg (x : Fin 12) : Fin 12 :=
  twelveMk (2 - (twelveDecode x).1.1) (6 - (twelveDecode x).2.1)

/-- The order-twelve specialization of the complete mapping in Lemma 3.5. -/
def twelveMu (p : Fin 12) : Fin 12 :=
  let a := (twelveDecode p).1.1
  let x := (twelveDecode p).2.1
  if a = 0 then
    if x = 0 then twelveMk 1 0
    else if x < 3 then twelveMk 0 x
    else if x < 5 then twelveMk 1 (x + 1)
    else twelveMk 0 0
  else
    if x < 2 then twelveMk 1 (x + 1)
    else if x = 2 then twelveMk 0 3
    else if x = 3 then twelveMk 1 3
    else twelveMk 0 x

theorem twelveMu_bijective : Function.Bijective twelveMu := by
  decide +kernel

theorem twelveComplete_bijective :
    Function.Bijective (fun t ↦ twelveAdd (twelveMu t) t) := by
  decide +kernel

/-- Exponent of the product character indexed by `a`, evaluated at `x`.
The `Z/2` character contributes either exponent zero or three modulo six. -/
def twelveCharacterExponent (a x : Fin 12) : ℕ :=
  (3 * (((twelveDecode a).1.1 * (twelveDecode x).1.1) % 2) +
    (twelveDecode a).2.1 * (twelveDecode x).2.1) % 6

theorem twelveMu_separating :
    ∀ a b : Fin 12,
      (∀ t : Fin 12,
        (twelveCharacterExponent a (twelveMu t) +
          twelveCharacterExponent b t) % 6 =
        twelveCharacterExponent a (twelveMu 0)) →
      a = 0 ∧ b = 0 := by
  intro a
  fin_cases a <;> decide +kernel

/-- Exact powers of `ζ₆`. -/
def sixthRootExact (k : ℕ) : CycloSix :=
  match k % 6 with
  | 0 => ⟨1, 0⟩
  | 1 => ⟨0, 1⟩
  | 2 => ⟨-1, 1⟩
  | 3 => ⟨-1, 0⟩
  | 4 => ⟨0, -1⟩
  | _ => ⟨1, -1⟩

/-- The unnormalized exact character coefficient in cell `(i,j)` at `t`. -/
def twelveExactEntry (i j t : Fin 12) : CycloSix :=
  sixthRootExact
    (twelveCharacterExponent i (twelveMu t) +
      twelveCharacterExponent j t)

/-! ## The exact order-twelve Fourier square -/

/-- Twelve-term Hermitian product in `ℚ(ζ₆)`. -/
def cycloSixDot12 (x y : Fin 12 → CycloSix) : CycloSix :=
  let term (k : Fin 12) := CycloSix.mul (CycloSix.conjugate (x k)) (y k)
  CycloSix.add (term ⟨0, by decide⟩)
    (CycloSix.add (term ⟨1, by decide⟩)
      (CycloSix.add (term ⟨2, by decide⟩)
        (CycloSix.add (term ⟨3, by decide⟩)
          (CycloSix.add (term ⟨4, by decide⟩)
            (CycloSix.add (term ⟨5, by decide⟩)
              (CycloSix.add (term ⟨6, by decide⟩)
                (CycloSix.add (term ⟨7, by decide⟩)
                  (CycloSix.add (term ⟨8, by decide⟩)
                    (CycloSix.add (term ⟨9, by decide⟩)
                      (CycloSix.add (term ⟨10, by decide⟩)
                        (term ⟨11, by decide⟩)))))))))))

theorem dot_embed_cycloSix12 (x y : Fin 12 → CycloSix) :
    dot (fun k ↦ CycloSix.embed (x k)) (fun k ↦ CycloSix.embed (y k)) =
      CycloSix.embed (cycloSixDot12 x y) := by
  simp [dot, cycloSixDot12, Fin.sum_univ_succ]

/-- Every ket has the common normalization `1/√12`. -/
noncomputable def twelveEntry (i j : Fin 12) : Ket (Fin 12) :=
  fun t ↦ fourierScale 12 * CycloSix.embed (twelveExactEntry i j t)

theorem dot_twelveEntry_exact (x y : Fin 12 → CycloSix) :
    dot
        (fun k ↦ fourierScale 12 * CycloSix.embed (x k))
        (fun k ↦ fourierScale 12 * CycloSix.embed (y k)) =
      (12 : ℂ)⁻¹ * CycloSix.embed (cycloSixDot12 x y) := by
  rw [dot]
  calc
    (∑ k : Fin 12,
        conj (fourierScale 12 * CycloSix.embed (x k)) *
          (fourierScale 12 * CycloSix.embed (y k))) =
        (conj (fourierScale 12) * fourierScale 12) *
          ∑ k : Fin 12,
            conj (CycloSix.embed (x k)) * CycloSix.embed (y k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      simp only [map_mul]
      ring
    _ = (12 : ℂ)⁻¹ * CycloSix.embed (cycloSixDot12 x y) := by
      rw [fourierScale_star_mul, ← dot, dot_embed_cycloSix12]
      norm_num

theorem twelve_rowGram_exact :
    ∀ i a b : Fin 12,
      cycloSixDot12 (twelveExactEntry i a) (twelveExactEntry i b) =
        if a = b then CycloSix.ofRat 12 else CycloSix.zero := by
  intro i
  fin_cases i <;> decide +kernel

theorem twelve_colGram_exact :
    ∀ j a b : Fin 12,
      cycloSixDot12 (twelveExactEntry a j) (twelveExactEntry b j) =
        if a = b then CycloSix.ofRat 12 else CycloSix.zero := by
  intro j
  fin_cases j <;> decide +kernel

theorem twelveAdd_right_inverse :
    ∀ a b : Fin 12, twelveAdd (twelveAdd a b) (twelveNeg b) = a := by
  decide +kernel

theorem twelveAdd_right_inverse' :
    ∀ a b : Fin 12, twelveAdd (twelveAdd a (twelveNeg b)) b = a := by
  decide +kernel

theorem twelveAdd_comm : ∀ a b : Fin 12, twelveAdd a b = twelveAdd b a := by
  decide +kernel

def twelveAddPerm (b : Fin 12) : Equiv.Perm (Fin 12) where
  toFun a := twelveAdd a b
  invFun a := twelveAdd a (twelveNeg b)
  left_inv a := twelveAdd_right_inverse a b
  right_inv a := twelveAdd_right_inverse' a b

theorem twelve_transversalGram_exact :
    ∀ s a b : Fin 12,
      cycloSixDot12
          (twelveExactEntry a (twelveAdd a s))
          (twelveExactEntry b (twelveAdd b s)) =
        if a = b then CycloSix.ofRat 12 else CycloSix.zero := by
  intro s
  fin_cases s <;> decide +kernel

noncomputable def twelveQLS : QuantumLatinSquare (Fin 12) where
  entry := twelveEntry
  row_orthonormal := by
    intro i a b
    change dot
        (fun k ↦ fourierScale 12 * CycloSix.embed (twelveExactEntry i a k))
        (fun k ↦ fourierScale 12 * CycloSix.embed (twelveExactEntry i b k)) = _
    rw [dot_twelveEntry_exact, twelve_rowGram_exact]
    by_cases h : a = b <;> simp [h]
  col_orthonormal := by
    intro j a b
    change dot
        (fun k ↦ fourierScale 12 * CycloSix.embed (twelveExactEntry a j k))
        (fun k ↦ fourierScale 12 * CycloSix.embed (twelveExactEntry b j k)) = _
    rw [dot_twelveEntry_exact, twelve_colGram_exact]
    by_cases h : a = b <;> simp [h]

set_option maxHeartbeats 0 in
noncomputable def twelveResolution : twelveQLS.Resolution where
  column := twelveAddPerm
  covers i := by
    have hfun : (fun s : Fin 12 ↦ twelveAddPerm s i) = twelveAddPerm i := by
      funext s
      exact twelveAdd_comm i s
    rw [hfun]
    exact (twelveAddPerm i).bijective
  orthonormal := by
    intro s a b
    change dot
        (fun k ↦ fourierScale 12 * CycloSix.embed
          (twelveExactEntry a (twelveAdd a s) k))
        (fun k ↦ fourierScale 12 * CycloSix.embed
          (twelveExactEntry b (twelveAdd b s) k)) = _
    rw [dot_twelveEntry_exact, twelve_transversalGram_exact]
    by_cases h : a = b <;> simp [h]

set_option maxHeartbeats 0 in
/-- Distinct cells have a coordinate witnessing failure of projective
proportionality, after cross-multiplication by coordinate zero. -/
theorem twelve_distinct_crossSeparated :
    ∀ i j i' j' : Fin 12, (i, j) ≠ (i', j') →
      ∃ t : Fin 12,
        CycloSix.mul (twelveExactEntry i j t)
            (twelveExactEntry i' j' 0) ≠
          CycloSix.mul (twelveExactEntry i j 0)
            (twelveExactEntry i' j' t) := by
  intro i
  fin_cases i <;> decide +kernel

theorem twelveQLS_maximal : twelveQLS.HasMaximalCardinality := by
  intro i j i' j' hphase
  change PhaseEquivalent
      (fun k ↦ fourierScale 12 * CycloSix.embed (twelveExactEntry i j k))
      (fun k ↦ fourierScale 12 * CycloSix.embed (twelveExactEntry i' j' k))
    at hphase
  rcases hphase with ⟨z, _hz, hfun⟩
  have hs : fourierScale 12 ≠ 0 := fourierScale_ne_zero 12
  have hcoeff : ∀ t : Fin 12,
      CycloSix.embed (twelveExactEntry i j t) =
        z * CycloSix.embed (twelveExactEntry i' j' t) := by
    intro t
    apply mul_left_cancel₀ hs
    have ht := congrFun hfun t
    change fourierScale 12 * CycloSix.embed (twelveExactEntry i j t) =
      z * (fourierScale 12 * CycloSix.embed (twelveExactEntry i' j' t)) at ht
    calc
      fourierScale 12 * CycloSix.embed (twelveExactEntry i j t) =
          z * (fourierScale 12 *
            CycloSix.embed (twelveExactEntry i' j' t)) := ht
      _ = fourierScale 12 *
          (z * CycloSix.embed (twelveExactEntry i' j' t)) := by ring
  have hcell : (i, j) = (i', j') := by
    by_contra hne
    obtain ⟨t, ht⟩ := twelve_distinct_crossSeparated i j i' j' hne
    apply ht
    apply CycloSix.embed_injective
    rw [CycloSix.embed_mul, CycloSix.embed_mul]
    rw [hcoeff t, hcoeff 0]
    ring
  exact ⟨congrArg Prod.fst hcell, congrArg Prod.snd hcell⟩

noncomputable def twelveMaximalRQLS : MaximalRQLS (Fin 12) where
  square := twelveQLS
  resolution := twelveResolution
  maximal := twelveQLS_maximal

/-! ## Sending the constant entry to basis zero -/

def twelveCharacterExact (a t : Fin 12) : CycloSix :=
  sixthRootExact (twelveCharacterExponent a t)

theorem fourierScale_twelve_conj :
    conj (fourierScale 12) = fourierScale 12 := by
  simp [fourierScale]

/-- The inverse character matrix of the encoded product group. -/
noncomputable def twelveInverseFourier : Matrix (Fin 12) (Fin 12) ℂ :=
  fun a t ↦ fourierScale 12 *
    CycloSix.embed (CycloSix.conjugate (twelveCharacterExact a t))

theorem twelveInverseFourier_colGram_exact :
    ∀ a b : Fin 12,
      cycloSixDot12
          (fun k ↦ CycloSix.conjugate (twelveCharacterExact k a))
          (fun k ↦ CycloSix.conjugate (twelveCharacterExact k b)) =
        if a = b then CycloSix.ofRat 12 else CycloSix.zero := by
  intro a
  fin_cases a <;> decide +kernel

theorem twelveInverseFourier_conjTranspose_mul :
    twelveInverseFourierᴴ * twelveInverseFourier = 1 := by
  ext a b
  change dot
      (fun k ↦ fourierScale 12 * CycloSix.embed
        (CycloSix.conjugate (twelveCharacterExact k a)))
      (fun k ↦ fourierScale 12 * CycloSix.embed
        (CycloSix.conjugate (twelveCharacterExact k b))) =
    if a = b then 1 else 0
  rw [dot_twelveEntry_exact, twelveInverseFourier_colGram_exact]
  by_cases h : a = b <;> simp [h]

noncomputable def twelveInverseFourierIsometry :
    CommonCoordinateIsometry (Fin 12) where
  toFun x := twelveInverseFourier *ᵥ x
  map_smul := by
    intro z x
    funext a
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm]
  dot_map := by
    intro x y
    change star (twelveInverseFourier *ᵥ x) ⬝ᵥ
        (twelveInverseFourier *ᵥ y) = star x ⬝ᵥ y
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_vecMul, twelveInverseFourier_conjTranspose_mul]
    simp
  injective := by
    intro x y hxy
    have h := congrArg (fun v ↦ twelveInverseFourierᴴ *ᵥ v) hxy
    simpa [Matrix.mulVec_mulVec,
      twelveInverseFourier_conjTranspose_mul] using h

/-- Exact coefficients after applying the inverse character matrix. -/
def twelveAfterFourierExact
    (x : Fin 12 → CycloSix) (a : Fin 12) : CycloSix :=
  CycloSix.scaleRat (1 / 12) (cycloSixDot12 (twelveCharacterExact a) x)

theorem twelveInverseFourier_apply_exact
    (x : Fin 12 → CycloSix) (a : Fin 12) :
    (twelveInverseFourier *ᵥ
      (fun k ↦ fourierScale 12 * CycloSix.embed (x k))) a =
      CycloSix.embed (twelveAfterFourierExact x a) := by
  calc
    (twelveInverseFourier *ᵥ
        (fun k ↦ fourierScale 12 * CycloSix.embed (x k))) a =
        dot
          (fun k ↦ fourierScale 12 *
            CycloSix.embed (twelveCharacterExact a k))
          (fun k ↦ fourierScale 12 * CycloSix.embed (x k)) := by
      simp [twelveInverseFourier, Matrix.mulVec, dotProduct, dot,
        fourierScale_twelve_conj]
    _ = (12 : ℂ)⁻¹ *
        CycloSix.embed (cycloSixDot12 (twelveCharacterExact a) x) :=
      dot_twelveEntry_exact _ _
    _ = CycloSix.embed (twelveAfterFourierExact x a) := by
      rw [twelveAfterFourierExact, CycloSix.embed_scaleRat]
      norm_num

/-! ## A rational reflection on the eleven-dimensional complement -/

/-- Complement weights `(2,1,1,1,2,2,1,2,2,1,1)`, of squared length 26. -/
def twelvePointedWeight (i : Fin 12) : ℚ :=
  match i.1 with
  | 1 => 2
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 2
  | 6 => 2
  | 7 => 1
  | 8 => 2
  | 9 => 2
  | 10 => 1
  | 11 => 1
  | _ => 0

/-- The Householder matrix `I - wwᵀ/13`, fixing coordinate zero. -/
def twelveHouseholderExact (a b : Fin 12) : CycloSix :=
  if a.1 = 0 then
    if b.1 = 0 then CycloSix.one else CycloSix.zero
  else if b.1 = 0 then
    CycloSix.zero
  else
    CycloSix.ofRat
      ((if a = b then 1 else 0) -
        twelvePointedWeight a * twelvePointedWeight b / 13)

noncomputable def twelveHouseholder : Matrix (Fin 12) (Fin 12) ℂ :=
  fun a b ↦ CycloSix.embed (twelveHouseholderExact a b)

theorem twelveHouseholder_colGram_exact :
    ∀ a b : Fin 12,
      cycloSixDot12
          (fun k ↦ twelveHouseholderExact k a)
          (fun k ↦ twelveHouseholderExact k b) =
        if a = b then CycloSix.one else CycloSix.zero := by
  intro a
  fin_cases a <;> decide +kernel

theorem twelveHouseholder_conjTranspose_mul :
    twelveHouseholderᴴ * twelveHouseholder = 1 := by
  ext a b
  change dot
      (fun k ↦ CycloSix.embed (twelveHouseholderExact k a))
      (fun k ↦ CycloSix.embed (twelveHouseholderExact k b)) =
    if a = b then 1 else 0
  rw [dot_embed_cycloSix12, twelveHouseholder_colGram_exact]
  by_cases h : a = b <;> simp [h]

def twelveHouseholderExactApply
    (x : Fin 12 → CycloSix) (a : Fin 12) : CycloSix :=
  cycloSixDot12
    (fun k ↦ CycloSix.conjugate (twelveHouseholderExact a k)) x

theorem twelveHouseholder_apply_exact
    (x : Fin 12 → CycloSix) (a : Fin 12) :
    (twelveHouseholder *ᵥ (fun k ↦ CycloSix.embed (x k))) a =
      CycloSix.embed (twelveHouseholderExactApply x a) := by
  unfold twelveHouseholderExactApply
  rw [← dot_embed_cycloSix12]
  simp [twelveHouseholder, dot, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ]

noncomputable def twelveHouseholderIsometry :
    CommonCoordinateIsometry (Fin 12) where
  toFun x := twelveHouseholder *ᵥ x
  map_smul := by
    intro z x
    funext a
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm]
  dot_map := by
    intro x y
    change star (twelveHouseholder *ᵥ x) ⬝ᵥ
        (twelveHouseholder *ᵥ y) = star x ⬝ᵥ y
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_vecMul, twelveHouseholder_conjTranspose_mul]
    simp
  injective := by
    intro x y hxy
    have h := congrArg (fun v ↦ twelveHouseholderᴴ *ᵥ v) hxy
    simpa [Matrix.mulVec_mulVec,
      twelveHouseholder_conjTranspose_mul] using h

/-- Exact coefficients after both unitary transformations. -/
def twelvePointedExactEntry (i j a : Fin 12) : CycloSix :=
  twelveHouseholderExactApply
    (fun k ↦ twelveAfterFourierExact (twelveExactEntry i j) k) a

/-- Exhaustive finite avoidance certificate for both surviving coordinates. -/
theorem twelvePointed_regular_exact :
    ∀ i j : Fin 12, (i, j) ≠ (0, 0) →
      twelvePointedExactEntry i j 1 ≠ CycloSix.zero ∧
        twelvePointedExactEntry i j 2 ≠ CycloSix.zero := by
  intro i
  fin_cases i <;> decide +kernel

/-- The composed unitary: inverse character transform, then Householder
reflection on the complement of basis zero. -/
noncomputable def twelvePointedIsometry : CommonCoordinateIsometry (Fin 12) where
  toFun x := twelveHouseholderIsometry (twelveInverseFourierIsometry x)
  map_smul z x := by
    rw [twelveInverseFourierIsometry.map_smul,
      twelveHouseholderIsometry.map_smul]
  dot_map x y := by
    rw [twelveHouseholderIsometry.dot_map,
      twelveInverseFourierIsometry.dot_map]
  injective := twelveHouseholderIsometry.injective.comp
    twelveInverseFourierIsometry.injective

theorem twelvePointedIsometry_apply_exact (i j a : Fin 12) :
    twelvePointedIsometry (twelveEntry i j) a =
      CycloSix.embed (twelvePointedExactEntry i j a) := by
  change (twelveHouseholder *ᵥ
    (twelveInverseFourier *ᵥ
      (fun k ↦ fourierScale 12 * CycloSix.embed (twelveExactEntry i j k)))) a = _
  have hFourier :
      twelveInverseFourier *ᵥ
          (fun k ↦ fourierScale 12 * CycloSix.embed (twelveExactEntry i j k)) =
        fun k ↦ CycloSix.embed
          (twelveAfterFourierExact (twelveExactEntry i j) k) := by
    funext k
    exact twelveInverseFourier_apply_exact _ _
  rw [hFourier]
  exact twelveHouseholder_apply_exact _ _

/-! ## Pointing and regularity -/

theorem twelvePointed_hole_exact :
    ∀ a : Fin 12, twelvePointedExactEntry 0 0 a =
      if a = 0 then CycloSix.one else CycloSix.zero := by
  decide +kernel

theorem twelvePointedIsometry_entry_zero_zero :
    twelvePointedIsometry (twelveEntry 0 0) = basis (0 : Fin 12) := by
  funext a
  rw [twelvePointedIsometry_apply_exact, twelvePointed_hole_exact]
  by_cases ha : a = 0
  · subst a
    simp [basis_apply]
  · have hzero : (0 : Fin 12) ≠ a := Ne.symm ha
    simp [ha, hzero, basis_apply]

noncomputable def transformedMaximalRQLSTwelve : MaximalRQLS (Fin 12) :=
  twelvePointedIsometry.mapMaximalRQLS twelveMaximalRQLS

def finTwelveEquivOptionEleven : Fin 12 ≃ Option (Fin 11) :=
  finSuccEquiv 11

noncomputable def pointedTwelveFull : MaximalRQLS (Option (Fin 11)) :=
  transformedMaximalRQLSTwelve.reindex finTwelveEquivOptionEleven

theorem transformedMaximalRQLSTwelve_entry_zero_zero :
    transformedMaximalRQLSTwelve.square.entry 0 0 = basis (0 : Fin 12) := by
  change twelvePointedIsometry (twelveMaximalRQLS.square.entry 0 0) = basis 0
  change twelvePointedIsometry (twelveEntry 0 0) = basis 0
  exact twelvePointedIsometry_entry_zero_zero

theorem pointedTwelveFull_hole_entry :
    pointedTwelveFull.square.entry none none = basis none := by
  change reindexKet finTwelveEquivOptionEleven
      (transformedMaximalRQLSTwelve.square.entry
        (finTwelveEquivOptionEleven.symm none)
        (finTwelveEquivOptionEleven.symm none)) = basis none
  rw [show finTwelveEquivOptionEleven.symm none = (0 : Fin 12) by
    simp [finTwelveEquivOptionEleven]]
  rw [transformedMaximalRQLSTwelve_entry_zero_zero]
  funext k
  cases k with
  | none => simp [reindexKet, finTwelveEquivOptionEleven, basis_apply]
  | some k =>
      have hzero : (0 : Fin 12) ≠ k.succ := Ne.symm (Fin.succ_ne_zero k)
      simp [reindexKet, finTwelveEquivOptionEleven, basis_apply, hzero]

theorem transformedMaximalRQLSTwelve_column_zero :
    transformedMaximalRQLSTwelve.resolution.column 0 0 = 0 := by
  change twelveMaximalRQLS.resolution.column 0 0 = 0
  rfl

theorem pointedTwelveFull_hole_transversal :
    pointedTwelveFull.resolution.column none none = none := by
  change finTwelveEquivOptionEleven
      (transformedMaximalRQLSTwelve.resolution.column
        (finTwelveEquivOptionEleven.symm none)
        (finTwelveEquivOptionEleven.symm none)) = none
  rw [show finTwelveEquivOptionEleven.symm none = (0 : Fin 12) by
    simp [finTwelveEquivOptionEleven]]
  rw [transformedMaximalRQLSTwelve_column_zero]
  simp [finTwelveEquivOptionEleven]

noncomputable def pointedMaximalRQLSTwelve :
    PointedMaximalRQLS (Fin 11) where
  full := pointedTwelveFull
  hole_entry := pointedTwelveFull_hole_entry
  hole_transversal := pointedTwelveFull_hole_transversal

theorem pointedTwelveFull_entry_exact (r c k : Option (Fin 11)) :
    pointedTwelveFull.square.entry r c k =
      CycloSix.embed
        (twelvePointedExactEntry
          (finTwelveEquivOptionEleven.symm r)
          (finTwelveEquivOptionEleven.symm c)
          (finTwelveEquivOptionEleven.symm k)) := by
  change twelvePointedIsometry
      (twelveEntry
        (finTwelveEquivOptionEleven.symm r)
        (finTwelveEquivOptionEleven.symm c))
      (finTwelveEquivOptionEleven.symm k) = _
  exact twelvePointedIsometry_apply_exact _ _ _

theorem twelve_nonhole_preimages_ne_zero {r c : Option (Fin 11)}
    (h : PointedMaximalRQLS.IsNonholeCell r c) :
    (finTwelveEquivOptionEleven.symm r,
      finTwelveEquivOptionEleven.symm c) ≠ ((0 : Fin 12), 0) := by
  intro hpair
  have hr : finTwelveEquivOptionEleven.symm r = (0 : Fin 12) :=
    congrArg Prod.fst hpair
  have hc : finTwelveEquivOptionEleven.symm c = (0 : Fin 12) :=
    congrArg Prod.snd hpair
  have hrnone : r = none := by
    calc
      r = finTwelveEquivOptionEleven (finTwelveEquivOptionEleven.symm r) :=
        (finTwelveEquivOptionEleven.apply_symm_apply r).symm
      _ = finTwelveEquivOptionEleven 0 :=
        congrArg finTwelveEquivOptionEleven hr
      _ = none := by simp [finTwelveEquivOptionEleven]
  have hcnone : c = none := by
    calc
      c = finTwelveEquivOptionEleven (finTwelveEquivOptionEleven.symm c) :=
        (finTwelveEquivOptionEleven.apply_symm_apply c).symm
      _ = finTwelveEquivOptionEleven 0 :=
        congrArg finTwelveEquivOptionEleven hc
      _ = none := by simp [finTwelveEquivOptionEleven]
  subst r
  subst c
  simp [PointedMaximalRQLS.IsNonholeCell] at h

theorem pointedMaximalRQLSTwelve_regular :
    pointedMaximalRQLSTwelve.RegularAt (0 : Fin 11) (1 : Fin 11) := by
  constructor
  · decide
  · intro r c hnonhole
    have hcert := twelvePointed_regular_exact
      (finTwelveEquivOptionEleven.symm r)
      (finTwelveEquivOptionEleven.symm c)
      (twelve_nonhole_preimages_ne_zero hnonhole)
    constructor
    · change pointedTwelveFull.square.entry r c (some (0 : Fin 11)) ≠ 0
      rw [pointedTwelveFull_entry_exact]
      simpa [finTwelveEquivOptionEleven] using
        CycloSix.embed_ne_zero hcert.1
    · change pointedTwelveFull.square.entry r c (some (1 : Fin 11)) ≠ 0
      rw [pointedTwelveFull_entry_exact]
      simpa [finTwelveEquivOptionEleven] using
        CycloSix.embed_ne_zero hcert.2

/-- The regular pointed order-twelve input used by the singular construction. -/
theorem regularPointedTwelve :
    ∃ (P : PointedMaximalRQLS (Fin 11)) (d e : Fin 11), P.RegularAt d e := by
  exact ⟨pointedMaximalRQLSTwelve, 0, 1,
    pointedMaximalRQLSTwelve_regular⟩

end LeanCo.QuantumLatin
