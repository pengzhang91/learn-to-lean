import LeanCo.QuantumLatin.Defs
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic

/-!
# The maximal resolvable quantum Latin square of order eight

This file is a literal finite-coordinate formalization of Example 2.3
(labelled Example 3.3 in the supplied arXiv source) of Zhang--Cao.  The
sixty-four vectors are recorded below, together with the eight displayed
transversals.  Their coefficients are first evaluated in the exact field
`ℚ(√2, i)` and only then embedded into `ℂ`; consequently all finite Gram
matrices and all non-proportionality certificates are checked by kernel
reduction rather than floating-point computation.
-/

open scoped BigOperators ComplexConjugate

namespace LeanCo.QuantumLatin

attribute [local instance] Fintype.decidableForallFintype

/-! ## Exact coefficients in `ℚ(√2, i)` -/

/-- A canonical formal expression `a + b√2`, with rational coefficients. -/
structure SqrtTwo where
  rat : ℚ
  sqrt : ℚ
deriving DecidableEq

namespace SqrtTwo

def zero : SqrtTwo := ⟨0, 0⟩
def one : SqrtTwo := ⟨1, 0⟩
def neg (x : SqrtTwo) : SqrtTwo := ⟨-x.rat, -x.sqrt⟩
def add (x y : SqrtTwo) : SqrtTwo := ⟨x.rat + y.rat, x.sqrt + y.sqrt⟩
def sub (x y : SqrtTwo) : SqrtTwo := add x (neg y)

/-- Multiplication reduced by the relation `(√2)² = 2`. -/
def mul (x y : SqrtTwo) : SqrtTwo :=
  ⟨x.rat * y.rat + 2 * x.sqrt * y.sqrt,
    x.rat * y.sqrt + x.sqrt * y.rat⟩

/-- The intended real value of an exact coefficient. -/
noncomputable def embed (x : SqrtTwo) : ℝ :=
  (x.rat : ℝ) + (x.sqrt : ℝ) * Real.sqrt 2

@[simp] theorem embed_zero : embed zero = 0 := by
  simp [embed, zero]

@[simp] theorem embed_one : embed one = 1 := by
  simp [embed, one]

@[simp] theorem embed_neg (x : SqrtTwo) : embed (neg x) = -embed x := by
  simp [embed, neg]
  ring

@[simp] theorem embed_add (x y : SqrtTwo) : embed (add x y) = embed x + embed y := by
  simp [embed, add]
  ring

@[simp] theorem embed_sub (x y : SqrtTwo) : embed (sub x y) = embed x - embed y := by
  rw [sub, embed_add, embed_neg]
  ring

@[simp] theorem embed_mul (x y : SqrtTwo) : embed (mul x y) = embed x * embed y := by
  have hs : (Real.sqrt 2) * Real.sqrt 2 = 2 := by
    exact Real.mul_self_sqrt (by positivity)
  simp only [embed, mul]
  push_cast
  ring_nf
  rw [show Real.sqrt 2 ^ 2 = 2 by rw [pow_two, hs]]

/-- The presentation `a+b√2` is canonical. -/
theorem embed_injective : Function.Injective embed := by
  intro x y hxy
  have hsqrt : x.sqrt = y.sqrt := by
    by_contra hne
    have hdenQ : x.sqrt - y.sqrt ≠ 0 := sub_ne_zero.mpr hne
    have hdenR : ((x.sqrt - y.sqrt : ℚ) : ℝ) ≠ 0 := by
      exact_mod_cast hdenQ
    have hs : Real.sqrt 2 =
        (((y.rat - x.rat) / (x.sqrt - y.sqrt) : ℚ) : ℝ) := by
      rw [Rat.cast_div]
      apply (eq_div_iff hdenR).2
      push_cast
      dsimp [embed] at hxy
      linarith
    exact irrational_sqrt_two ⟨_, hs.symm⟩
  have hrat : x.rat = y.rat := by
    have : (x.rat : ℝ) = (y.rat : ℝ) := by
      dsimp [embed] at hxy
      rw [hsqrt] at hxy
      linarith
    exact_mod_cast this
  cases x
  cases y
  simp_all

end SqrtTwo

/-- A canonical exact complex number with real and imaginary parts in
`ℚ(√2)`. -/
structure ExactComplex where
  re : SqrtTwo
  im : SqrtTwo
deriving DecidableEq

namespace ExactComplex

def mk4 (reRat reSqrt imRat imSqrt : ℚ) : ExactComplex :=
  ⟨⟨reRat, reSqrt⟩, ⟨imRat, imSqrt⟩⟩

def zero : ExactComplex := ⟨SqrtTwo.zero, SqrtTwo.zero⟩
def one : ExactComplex := ⟨SqrtTwo.one, SqrtTwo.zero⟩
def neg (x : ExactComplex) : ExactComplex :=
  ⟨SqrtTwo.neg x.re, SqrtTwo.neg x.im⟩
def add (x y : ExactComplex) : ExactComplex :=
  ⟨SqrtTwo.add x.re y.re, SqrtTwo.add x.im y.im⟩
def sub (x y : ExactComplex) : ExactComplex := add x (neg y)
def mul (x y : ExactComplex) : ExactComplex :=
  ⟨SqrtTwo.sub (SqrtTwo.mul x.re y.re) (SqrtTwo.mul x.im y.im),
    SqrtTwo.add (SqrtTwo.mul x.re y.im) (SqrtTwo.mul x.im y.re)⟩
def conjugate (x : ExactComplex) : ExactComplex :=
  ⟨x.re, SqrtTwo.neg x.im⟩

/-- The exact embedding into the complex Hilbert space used by `Defs`. -/
noncomputable def embed (x : ExactComplex) : ℂ :=
  ⟨SqrtTwo.embed x.re, SqrtTwo.embed x.im⟩

@[simp] theorem embed_zero : embed zero = 0 := by
  apply Complex.ext <;> simp [embed, zero]

@[simp] theorem embed_one : embed one = 1 := by
  apply Complex.ext <;> simp [embed, one]

@[simp] theorem embed_neg (x : ExactComplex) : embed (neg x) = -embed x := by
  apply Complex.ext <;> simp [embed, neg]

@[simp] theorem embed_add (x y : ExactComplex) : embed (add x y) = embed x + embed y := by
  apply Complex.ext <;> simp [embed, add]

@[simp] theorem embed_sub (x y : ExactComplex) : embed (sub x y) = embed x - embed y := by
  rw [sub, embed_add, embed_neg]
  ring

@[simp] theorem embed_mul (x y : ExactComplex) : embed (mul x y) = embed x * embed y := by
  apply Complex.ext <;> simp [embed, mul, Complex.mul_re, Complex.mul_im]

@[simp] theorem embed_conjugate (x : ExactComplex) :
    embed (conjugate x) = star (embed x) := by
  apply Complex.ext <;> simp [embed, conjugate]

theorem embed_injective : Function.Injective embed := by
  intro x y hxy
  have hre : x.re = y.re := SqrtTwo.embed_injective (congrArg Complex.re hxy)
  have him : x.im = y.im := SqrtTwo.embed_injective (congrArg Complex.im hxy)
  cases x
  cases y
  simp_all

theorem embed_ne_zero {x : ExactComplex} (hx : x ≠ zero) : embed x ≠ 0 := by
  intro h
  apply hx
  apply embed_injective
  simpa using h

end ExactComplex

/-! ## Literal transcription of the sixty-four vectors -/

/-- The three magnitudes which occur in the displayed square. -/
inductive EightMagnitude where
  | one
  | half
  | sqrtHalf
deriving DecidableEq

/-- One nonzero coordinate: coordinate number, magnitude, and power of
`ω = exp(πi/4)`. -/
structure EightTerm where
  coordinate : ℕ
  magnitude : EightMagnitude
  phase : ℕ
deriving DecidableEq

/-- The exact eighth roots of unity, in increasing powers. -/
def omega8Exact (phase : ℕ) : ExactComplex :=
  match phase % 8 with
  | 0 => ExactComplex.mk4 1 0 0 0
  | 1 => ExactComplex.mk4 0 (1 / 2) 0 (1 / 2)
  | 2 => ExactComplex.mk4 0 0 1 0
  | 3 => ExactComplex.mk4 0 (-(1 / 2)) 0 (1 / 2)
  | 4 => ExactComplex.mk4 (-1) 0 0 0
  | 5 => ExactComplex.mk4 0 (-(1 / 2)) 0 (-(1 / 2))
  | 6 => ExactComplex.mk4 0 0 (-1) 0
  | _ => ExactComplex.mk4 0 (1 / 2) 0 (-(1 / 2))

def magnitude8Exact : EightMagnitude → ExactComplex
  | .one => ExactComplex.mk4 1 0 0 0
  | .half => ExactComplex.mk4 (1 / 2) 0 0 0
  | .sqrtHalf => ExactComplex.mk4 0 (1 / 2) 0 0

def EightTerm.coefficient (term : EightTerm) : ExactComplex :=
  ExactComplex.mul (magnitude8Exact term.magnitude) (omega8Exact term.phase)

/-- Short constructors used to keep the transcription legible. -/
def unitTerm (coordinate : ℕ) : EightTerm := ⟨coordinate, .one, 0⟩
def halfTerm (coordinate phase : ℕ) : EightTerm := ⟨coordinate, .half, phase⟩
def sqrtHalfTerm (coordinate phase : ℕ) : EightTerm :=
  ⟨coordinate, .sqrtHalf, phase⟩

/-- Exact vector obtained by summing its listed nonzero coordinates. -/
def exactVector8 (terms : List EightTerm) (k : Fin 8) : ExactComplex :=
  terms.foldl
    (fun acc term ↦
      if term.coordinate % 8 = k.1 then
        ExactComplex.add acc term.coefficient
      else
        acc)
    ExactComplex.zero

/-- The displayed `8 × 8` array, flattened in row-major order.  `halfTerm`
means `ω^phase/2`, and `sqrtHalfTerm` means `ω^phase/√2`; thus these lines
are a term-for-term transcription of the paper's kets. -/
def orderEightTerms : Array (List EightTerm) := #[
  -- row 0
  [unitTerm 0],
  [unitTerm 1],
  [unitTerm 2],
  [unitTerm 3],
  [unitTerm 4],
  [unitTerm 5],
  [unitTerm 6],
  [unitTerm 7],

  -- row 1
  [sqrtHalfTerm 2 0, sqrtHalfTerm 3 3],
  [sqrtHalfTerm 2 0, sqrtHalfTerm 3 7],
  [sqrtHalfTerm 0 0, sqrtHalfTerm 1 6],
  [sqrtHalfTerm 0 0, sqrtHalfTerm 1 2],
  [sqrtHalfTerm 6 0, sqrtHalfTerm 7 4],
  [sqrtHalfTerm 6 0, sqrtHalfTerm 7 0],
  [sqrtHalfTerm 4 0, sqrtHalfTerm 5 6],
  [sqrtHalfTerm 4 0, sqrtHalfTerm 5 2],

  -- row 2
  [halfTerm 4 0, halfTerm 5 0, halfTerm 6 7, halfTerm 7 5],
  [halfTerm 4 0, halfTerm 5 0, halfTerm 6 3, halfTerm 7 1],
  [halfTerm 4 0, halfTerm 5 4, halfTerm 6 3, halfTerm 7 5],
  [halfTerm 4 0, halfTerm 5 4, halfTerm 6 7, halfTerm 7 1],
  [halfTerm 0 0, halfTerm 1 0, halfTerm 2 2, halfTerm 3 7],
  [halfTerm 0 0, halfTerm 1 0, halfTerm 2 6, halfTerm 3 3],
  [halfTerm 0 0, halfTerm 1 4, halfTerm 2 6, halfTerm 3 7],
  [halfTerm 0 0, halfTerm 1 4, halfTerm 2 2, halfTerm 3 3],

  -- row 3
  [halfTerm 4 0, halfTerm 5 4, halfTerm 6 1, halfTerm 7 3],
  [halfTerm 4 0, halfTerm 5 4, halfTerm 6 5, halfTerm 7 7],
  [halfTerm 4 0, halfTerm 5 0, halfTerm 6 5, halfTerm 7 3],
  [halfTerm 4 0, halfTerm 5 0, halfTerm 6 1, halfTerm 7 7],
  [halfTerm 0 0, halfTerm 1 4, halfTerm 2 4, halfTerm 3 5],
  [halfTerm 0 0, halfTerm 1 4, halfTerm 2 0, halfTerm 3 1],
  [halfTerm 0 0, halfTerm 1 0, halfTerm 2 0, halfTerm 3 5],
  [halfTerm 0 0, halfTerm 1 0, halfTerm 2 4, halfTerm 3 1],

  -- row 4
  [sqrtHalfTerm 1 0, halfTerm 2 7, halfTerm 3 6],
  [sqrtHalfTerm 0 0, halfTerm 2 5, halfTerm 3 0],
  [halfTerm 0 0, halfTerm 1 2, sqrtHalfTerm 3 4],
  [halfTerm 0 0, halfTerm 1 6, sqrtHalfTerm 2 1],
  [sqrtHalfTerm 5 0, halfTerm 6 4, halfTerm 7 4],
  [sqrtHalfTerm 4 0, halfTerm 6 2, halfTerm 7 6],
  [halfTerm 4 0, halfTerm 5 2, sqrtHalfTerm 7 2],
  [halfTerm 4 0, halfTerm 5 6, sqrtHalfTerm 6 6],

  -- row 5
  [sqrtHalfTerm 1 0, halfTerm 2 3, halfTerm 3 2],
  [sqrtHalfTerm 0 0, halfTerm 2 1, halfTerm 3 4],
  [halfTerm 0 0, halfTerm 1 2, sqrtHalfTerm 3 0],
  [halfTerm 0 0, halfTerm 1 6, sqrtHalfTerm 2 5],
  [sqrtHalfTerm 5 0, halfTerm 6 0, halfTerm 7 0],
  [sqrtHalfTerm 4 0, halfTerm 6 6, halfTerm 7 2],
  [halfTerm 4 0, halfTerm 5 2, sqrtHalfTerm 7 6],
  [halfTerm 4 0, halfTerm 5 6, sqrtHalfTerm 6 2],

  -- row 6
  [halfTerm 4 0, halfTerm 5 6, sqrtHalfTerm 7 0],
  [halfTerm 4 0, halfTerm 5 2, sqrtHalfTerm 6 0],
  [sqrtHalfTerm 5 0, halfTerm 6 2, halfTerm 7 6],
  [sqrtHalfTerm 4 0, halfTerm 6 4, halfTerm 7 4],
  [halfTerm 0 0, halfTerm 1 6, sqrtHalfTerm 3 2],
  [halfTerm 0 0, halfTerm 1 2, sqrtHalfTerm 2 3],
  [sqrtHalfTerm 1 0, halfTerm 2 5, halfTerm 3 0],
  [sqrtHalfTerm 0 0, halfTerm 2 7, halfTerm 3 6],

  -- row 7
  [halfTerm 4 0, halfTerm 5 2, sqrtHalfTerm 6 4],
  [halfTerm 4 0, halfTerm 5 6, sqrtHalfTerm 7 4],
  [sqrtHalfTerm 4 0, halfTerm 6 0, halfTerm 7 0],
  [sqrtHalfTerm 5 0, halfTerm 6 6, halfTerm 7 2],
  [halfTerm 0 0, halfTerm 1 2, sqrtHalfTerm 2 7],
  [halfTerm 0 0, halfTerm 1 6, sqrtHalfTerm 3 6],
  [sqrtHalfTerm 0 0, halfTerm 2 3, halfTerm 3 2],
  [sqrtHalfTerm 1 0, halfTerm 2 1, halfTerm 3 4]
]

theorem orderEightTerms_size : orderEightTerms.size = 64 := by decide +kernel

def orderEightEntryTerms (i j : Fin 8) : List EightTerm :=
  match orderEightTerms[i.1 * 8 + j.1]? with
  | some terms => terms
  | none => []

/-- The exact symbolic entry in cell `(i,j)`. -/
def orderEightExactEntry (i j : Fin 8) : Fin 8 → ExactComplex :=
  exactVector8 (orderEightEntryTerms i j)

/-- The literal complex ket in cell `(i,j)`. -/
noncomputable def orderEightEntry (i j : Fin 8) : Ket (Fin 8) :=
  fun k ↦ ExactComplex.embed (orderEightExactEntry i j k)

/-! ## Exact Gram matrices -/

/-- Eight-term Hermitian product in the exact coefficient model. -/
def exactDot8 (x y : Fin 8 → ExactComplex) : ExactComplex :=
  let term (k : Fin 8) :=
    ExactComplex.mul (ExactComplex.conjugate (x k)) (y k)
  ExactComplex.add (term ⟨0, by decide⟩)
    (ExactComplex.add (term ⟨1, by decide⟩)
      (ExactComplex.add (term ⟨2, by decide⟩)
        (ExactComplex.add (term ⟨3, by decide⟩)
          (ExactComplex.add (term ⟨4, by decide⟩)
            (ExactComplex.add (term ⟨5, by decide⟩)
              (ExactComplex.add (term ⟨6, by decide⟩)
                (term ⟨7, by decide⟩)))))))

theorem dot_embed_exact8 (x y : Fin 8 → ExactComplex) :
    dot (fun k ↦ ExactComplex.embed (x k))
        (fun k ↦ ExactComplex.embed (y k)) =
      ExactComplex.embed (exactDot8 x y) := by
  simp [dot, exactDot8, Fin.sum_univ_succ]

/-! ## Machine-checked QLS and transversal Gram matrices -/

theorem orderEight_rowGram_exact :
    ∀ i a b : Fin 8,
      exactDot8 (orderEightExactEntry i a) (orderEightExactEntry i b) =
        if a = b then ExactComplex.one else ExactComplex.zero := by
  intro i
  fin_cases i <;> decide +kernel

theorem orderEight_colGram_exact :
    ∀ j a b : Fin 8,
      exactDot8 (orderEightExactEntry a j) (orderEightExactEntry b j) =
        if a = b then ExactComplex.one else ExactComplex.zero := by
  intro j
  fin_cases j <;> decide +kernel

/-- Bitwise xor on the three-bit labels `Fin 8`. -/
def xor8 (a b : Fin 8) : Fin 8 :=
  ⟨Nat.xor a.1 b.1 % 8, Nat.mod_lt _ (by decide)⟩

theorem xor8_involutive :
    ∀ a b : Fin 8, xor8 (xor8 a b) b = a := by
  decide +kernel

theorem xor8_comm : ∀ a b : Fin 8, xor8 a b = xor8 b a := by
  decide +kernel

/-- The column numbers in the eight transversals, copied in the order printed
in the paper.  Row `t` lists the selected column in square rows `0,...,7`. -/
def paperTransversalColumns : Array (Array ℕ) := #[
  #[0, 1, 2, 3, 4, 5, 6, 7],
  #[1, 0, 3, 2, 5, 4, 7, 6],
  #[2, 3, 0, 1, 6, 7, 4, 5],
  #[3, 2, 1, 0, 7, 6, 5, 4],
  #[4, 5, 6, 7, 0, 1, 2, 3],
  #[5, 4, 7, 6, 1, 0, 3, 2],
  #[6, 7, 4, 5, 2, 3, 0, 1],
  #[7, 6, 5, 4, 3, 2, 1, 0]
]

def paperTransversalColumnNat (t i : Fin 8) : ℕ :=
  match paperTransversalColumns[t.1]? with
  | none => 0
  | some row =>
      match row[i.1]? with
      | none => 0
      | some j => j

/-- The compact xor description is exactly the eight displayed lists. -/
theorem paperTransversalColumns_eq_xor :
    ∀ t i : Fin 8, paperTransversalColumnNat t i = (xor8 i t).1 := by
  decide +kernel

/-- The column permutation in transversal `b`; it sends row `a` to `a xor b`. -/
def xorPerm8 (b : Fin 8) : Equiv.Perm (Fin 8) where
  toFun a := xor8 a b
  invFun a := xor8 a b
  left_inv a := xor8_involutive a b
  right_inv a := xor8_involutive a b

theorem orderEight_transversalGram_exact :
    ∀ t a b : Fin 8,
      exactDot8
          (orderEightExactEntry a (xor8 a t))
          (orderEightExactEntry b (xor8 b t)) =
        if a = b then ExactComplex.one else ExactComplex.zero := by
  intro t
  fin_cases t <;> decide +kernel

/-- The literal quantum Latin square from the paper. -/
noncomputable def orderEightQLS : QuantumLatinSquare (Fin 8) where
  entry := orderEightEntry
  row_orthonormal := by
    intro i a b
    change dot
        (fun k ↦ ExactComplex.embed (orderEightExactEntry i a k))
        (fun k ↦ ExactComplex.embed (orderEightExactEntry i b k)) = _
    rw [dot_embed_exact8, orderEight_rowGram_exact]
    by_cases h : a = b <;> simp [h]
  col_orthonormal := by
    intro j a b
    change dot
        (fun k ↦ ExactComplex.embed (orderEightExactEntry a j k))
        (fun k ↦ ExactComplex.embed (orderEightExactEntry b j k)) = _
    rw [dot_embed_exact8, orderEight_colGram_exact]
    by_cases h : a = b <;> simp [h]

/-- The eight transversals printed below Example 3.3: the cell in row `i`
of transversal `t` has column `i xor t`. -/
noncomputable def orderEightResolution : orderEightQLS.Resolution where
  column := xorPerm8
  covers := by
    intro i
    have hfun : (fun t : Fin 8 ↦ (xorPerm8 t) i) = xorPerm8 i := by
      funext t
      exact xor8_comm i t
    rw [hfun]
    exact (xorPerm8 i).bijective
  orthonormal := by
    intro t a b
    change dot
        (fun k ↦ ExactComplex.embed
          (orderEightExactEntry a (xor8 a t) k))
        (fun k ↦ ExactComplex.embed
          (orderEightExactEntry b (xor8 b t) k)) = _
    rw [dot_embed_exact8, orderEight_transversalGram_exact]
    by_cases h : a = b <;> simp [h]

/-! ## Maximal cardinality -/

/-- A purely exact witness that two symbolic vectors cannot be proportional:
either their zero supports differ, or a common nonzero coordinate fixes the
phase while another coordinate differs. -/
def ExactSeparated (x y : Fin 8 → ExactComplex) : Prop :=
  (∃ k, x k = ExactComplex.zero ∧ y k ≠ ExactComplex.zero) ∨
  (∃ k, y k = ExactComplex.zero ∧ x k ≠ ExactComplex.zero) ∨
  ∃ anchor witness,
    x anchor = y anchor ∧ x anchor ≠ ExactComplex.zero ∧
      x witness ≠ y witness

/-- Exhaustive exact certificate for the 2016 unordered pairs of distinct
cells. -/
theorem orderEight_distinct_exactSeparated :
    ∀ i j i' j' : Fin 8,
      (i, j) ≠ (i', j') →
        ExactSeparated (orderEightExactEntry i j)
          (orderEightExactEntry i' j') := by
  unfold ExactSeparated
  intro i
  fin_cases i <;> decide +kernel

theorem not_phaseEquivalent_of_exactSeparated
    {x y : Fin 8 → ExactComplex} (hsep : ExactSeparated x y) :
    ¬PhaseEquivalent
      (fun k ↦ ExactComplex.embed (x k))
      (fun k ↦ ExactComplex.embed (y k)) := by
  rintro ⟨z, hz, hxy⟩
  have hz0 : z ≠ 0 := by
    intro hzero
    subst z
    simp at hz
  rcases hsep with hsupport | hsupport | hcoeff
  · rcases hsupport with ⟨k, hxzero, hyzero⟩
    have hk := congrFun hxy k
    change ExactComplex.embed (x k) = z * ExactComplex.embed (y k) at hk
    have hyEmbed : ExactComplex.embed (y k) ≠ 0 :=
      ExactComplex.embed_ne_zero hyzero
    rw [hxzero, ExactComplex.embed_zero] at hk
    exact (mul_ne_zero hz0 hyEmbed) hk.symm
  · rcases hsupport with ⟨k, hyzero, hxzero⟩
    have hk := congrFun hxy k
    change ExactComplex.embed (x k) = z * ExactComplex.embed (y k) at hk
    have hxEmbed : ExactComplex.embed (x k) ≠ 0 :=
      ExactComplex.embed_ne_zero hxzero
    rw [hyzero, ExactComplex.embed_zero, mul_zero] at hk
    exact hxEmbed hk
  · rcases hcoeff with ⟨anchor, witness, hanchor, hanchor0, hwitness⟩
    have hanchorEmbed : ExactComplex.embed (x anchor) =
        ExactComplex.embed (y anchor) := congrArg ExactComplex.embed hanchor
    have hyAnchor0 : ExactComplex.embed (y anchor) ≠ 0 := by
      apply ExactComplex.embed_ne_zero
      simpa [hanchor] using hanchor0
    have ha := congrFun hxy anchor
    change ExactComplex.embed (x anchor) =
      z * ExactComplex.embed (y anchor) at ha
    have hz1 : z = 1 := by
      apply mul_right_cancel₀ hyAnchor0
      calc
        z * ExactComplex.embed (y anchor) =
            ExactComplex.embed (x anchor) := ha.symm
        _ = ExactComplex.embed (y anchor) := hanchorEmbed
        _ = 1 * ExactComplex.embed (y anchor) := by simp
    have hw := congrFun hxy witness
    change ExactComplex.embed (x witness) =
      z * ExactComplex.embed (y witness) at hw
    rw [hz1, one_mul] at hw
    exact hwitness (ExactComplex.embed_injective hw)

theorem orderEightQLS_maximal : orderEightQLS.HasMaximalCardinality := by
  intro i j i' j' hphase
  change PhaseEquivalent
      (fun k ↦ ExactComplex.embed (orderEightExactEntry i j k))
      (fun k ↦ ExactComplex.embed (orderEightExactEntry i' j' k)) at hphase
  have hcell : (i, j) = (i', j') := by
    by_contra hne
    exact (not_phaseEquivalent_of_exactSeparated
      (orderEight_distinct_exactSeparated i j i' j' hne)) hphase
  exact ⟨congrArg Prod.fst hcell, congrArg Prod.snd hcell⟩

/-- Example 3.3 packaged as a maximal-cardinality resolvable QLS. -/
noncomputable def maximalRQLSEight : MaximalRQLS (Fin 8) where
  square := orderEightQLS
  resolution := orderEightResolution
  maximal := orderEightQLS_maximal

/-- The literal order-eight existence theorem used by the global result. -/
theorem existsMaximalRQLS_eight : ExistsMaximalRQLS 8 :=
  ⟨maximalRQLSEight⟩

end LeanCo.QuantumLatin
