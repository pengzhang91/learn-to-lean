import LeanCo.SizeRamsey.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.FinRange
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic

/-!
# The Beke--Li--Sahasrabudhe path lower bound

This file internalises the lower-bound half of Beke--Li--Sahasrabudhe,
*The multicolour size Ramsey number of a path*, arXiv:2511.16656v1.
The paper-facing target below deliberately retains the v1 admissibility
condition `n >= 100 log r`.

## Proof DAG

The proof is organised so that no cited result is accepted as a hypothesis.

1. Turn a finite cover of the edge set by `P_n`-free graphs into an avoiding
   edge colouring (`coloringOfCover`).
2. Prove the two deterministic clean-up colourings from Lemmas 2.2 and 2.3
   (low-degree/Vizing-type and small-vertex-cover/star-type colourings).
3. Formalise the balls-and-bins variable `M(q,d)` and its normalised
   expectation `W(q,d)`; prove Appendix A.1 monotonicity.
4. Prove the second-moment lower tail estimate in Appendix A.2 and hence
   Lemmas 4.1 and 4.2.
5. Build the random maximising-bin subgraph and prove the subgraph-finding
   Lemma 4.5, including the Chernoff exceptional-event estimate.
6. Perform the approximately-regular edge decomposition and prove the key
   Lemma 2.1 (`BLSKeyLemmaV1`).
7. Iterate the deterministic round lemma, discharge both stopping cases, and
   close `BLSPathLowerBoundV1` without an external lower-bound assumption.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open Finset SimpleGraph

noncomputable section

universe u v w

variable {V : Type u} {K : Type v} {W : Type w}

/-! ## Exact paper-facing statements -/

/-- Integer scale used to state the lower bound without silently rounding a
real number. -/
def pathLowerScale (c : ℝ) (r n : ℕ) : ℕ :=
  ⌊c * (r : ℝ) ^ 2 * Real.log (r : ℝ) * n⌋₊

/-- The lower-bound assertion advertised in Theorem 1.1 of arXiv:2511.16656v1.
The quantifier over `r >= 2` includes the bounded-colour cases; the proof's
"sufficiently large `r`" reduction must therefore be discharged rather than
being hidden in this statement. -/
def BLSPathLowerBoundV1 : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ r n : ℕ, 2 ≤ r →
      100 * Real.log (r : ℝ) ≤ (n : ℝ) →
      IsPathSizeRamseyLowerBound r n (pathLowerScale c r n)

/-- The literal finite-graph content of the paper's key Lemma 2.1 at fixed
parameters.  Decimal exponent `0.9` is represented exactly as `9 / 10`.
This is a proposition to be proved below, not an imported assumption. -/
def BLSKeyLemmaAt [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (r n : ℕ) (β β₀ : ℝ) : Prop :=
  (7 * Real.log (r : ℝ))⁻¹ ≤ β →
  β ≤ β₀ →
  (G.maxDegree : ℝ) = β * r * Real.log (r : ℝ) →
  (Fintype.card V : ℝ) ≤ (r * Real.log (r : ℝ) * n) / 4 →
  Real.rpow (r : ℝ) (7 / 4 : ℝ) * n ≤ (edgeCount G : ℝ) →
  (edgeCount G : ℝ) ≤ (r : ℝ) ^ 2 * Real.log (r : ℝ) * n →
  ∃ H : SimpleGraph V,
    H ≤ G ∧ (pathGraph n).Free H ∧
      60 * edgeCount G /
          (Real.rpow β (9 / 10 : ℝ) * r) ≤ (edgeCount H : ℝ)

/-- Exact asymptotic quantifier package of Lemma 2.1 in v1.  In particular,
`n >= 100 log r` is present here as well as in the final theorem. -/
def BLSKeyLemmaV1 : Prop :=
  ∃ β₀ : ℝ, β₀ ∈ Set.Ioc (0 : ℝ) 1 ∧
    ∃ r₀ : ℕ, ∀ r : ℕ, r₀ ≤ r →
      ∀ n : ℕ, 100 * Real.log (r : ℝ) ≤ (n : ℝ) →
        ∀ N : ℕ, ∀ G : SimpleGraph (Fin N), ∀ β : ℝ,
          @BLSKeyLemmaAt (Fin N) inferInstance G (Classical.decRel _)
            r n β β₀

/-- The number of bins used in Lemma 4.5:
`floor ((6/n) * ceil (v/2))`. -/
def subgraphFindingBinCount (n v : ℕ) : ℕ :=
  (6 * ((v + 1) / 2)) / n

/-- Lower floor inequality for the bin count used in Lemma 4.5. -/
theorem mul_subgraphFindingBinCount_le (n v : ℕ) :
    n * subgraphFindingBinCount n v ≤ 6 * ((v + 1) / 2) := by
  exact Nat.mul_div_le _ _

/-- Upper floor inequality for the bin count used in Lemma 4.5. -/
theorem six_half_lt_mul_succ_subgraphFindingBinCount {n v : ℕ}
    (hn : 0 < n) :
    6 * ((v + 1) / 2) < n * (subgraphFindingBinCount n v + 1) := by
  exact Nat.lt_mul_div_succ _ hn

theorem subgraphFindingBinCount_eq_zero_iff {n v : ℕ} (hn : 0 < n) :
    subgraphFindingBinCount n v = 0 ↔ 6 * ((v + 1) / 2) < n := by
  rw [subgraphFindingBinCount, Nat.div_eq_zero_iff]
  simp only [Nat.ne_of_gt hn, false_or]

/-- The floor in the bin count needs an explicit small-bin split.  Once the
quotient has at least two bins, its actual mean is uniformly below `n/4`.
This repairs the informal `n/5` estimate in the paper for the cases where
the quotient is `2`, `3`, or `4`. -/
theorem quotientSix_mean_lt_quarter {n a : ℕ} (hn : 0 < n)
    (hq : 2 ≤ (6 * a) / n) :
    (a : ℝ) / ((6 * a) / n : ℕ) < (n : ℝ) / 4 := by
  let q := (6 * a) / n
  have hupperNat : 6 * a < n * (q + 1) := by
    dsimp only [q]
    exact Nat.lt_mul_div_succ _ hn
  have hratioNat : 2 * (q + 1) ≤ 3 * q := by omega
  have hupper : (6 : ℝ) * a < n * (q + 1) := by
    exact_mod_cast hupperNat
  have hratio : (2 : ℝ) * (q + 1) ≤ 3 * q := by
    exact_mod_cast hratioNat
  have hscaled : (n : ℝ) * (2 * (q + 1)) ≤ n * (3 * q) :=
    mul_le_mul_of_nonneg_left hratio (by positivity)
  have hfour : (4 : ℝ) * a < n * q := by
    nlinarith
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le (by omega) hq)
  change (a : ℝ) / q < (n : ℝ) / 4
  rw [div_lt_iff₀ hqpos]
  nlinarith

/-- Numerical exponent used for the exceptional-event estimate in
Lemma 4.5.  We retain the literal floored bin count and use the exact
`exp(1)` moment, obtaining a decay slightly stronger than the paper needs. -/
theorem quotientSix_chernoff_exponent_lt {n a : ℕ} (hn : 0 < n)
    (hq : 2 ≤ (6 * a) / n) :
    -(((n / 2 : ℕ) : ℝ)) +
        a * ((Real.exp 1 - 1) / ((6 * a) / n : ℕ)) <
      (1 : ℝ) / 2 - n / 16 := by
  let q := (6 * a) / n
  have hmean : (a : ℝ) / q < (n : ℝ) / 4 := by
    dsimp only [q]
    exact quotientSix_mean_lt_quarter hn hq
  have hexpNonneg : 0 ≤ Real.exp 1 - 1 :=
    sub_nonneg.mpr (Real.one_le_exp (by norm_num))
  have hexpLt : Real.exp 1 - 1 < (7 : ℝ) / 4 := by
    have := Real.exp_one_lt_d9
    norm_num at this ⊢
    linarith
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  have hmoment :
      ((a : ℝ) / q) * (Real.exp 1 - 1) <
        ((n : ℝ) / 4) * ((7 : ℝ) / 4) := by
    calc
      ((a : ℝ) / q) * (Real.exp 1 - 1) ≤
          ((n : ℝ) / 4) * (Real.exp 1 - 1) :=
        mul_le_mul_of_nonneg_right hmean.le hexpNonneg
      _ < ((n : ℝ) / 4) * ((7 : ℝ) / 4) :=
        mul_lt_mul_of_pos_left hexpLt (by positivity)
  have hfloorNat : n ≤ 2 * (n / 2) + 1 := by omega
  have hfloor : (n : ℝ) / 2 - 1 / 2 ≤ ((n / 2 : ℕ) : ℝ) := by
    have hfloorCast : (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 1 := by
      exact_mod_cast hfloorNat
    linarith
  change -(((n / 2 : ℕ) : ℝ)) +
      (a : ℝ) * ((Real.exp 1 - 1) / q) <
    (1 : ℝ) / 2 - n / 16
  have hrearrange :
      (a : ℝ) * ((Real.exp 1 - 1) / q) =
        ((a : ℝ) / q) * (Real.exp 1 - 1) := by ring
  rw [hrearrange]
  nlinarith

/-- Converting the v1 threshold `n ≥ 100 log r` into the polynomial tail
needed by Lemma 4.5.  The deliberately coarse exponent `6` leaves enough
room to absorb all floor errors and the factor `exp(1/2)`. -/
theorem exp_half_sub_six_log_le {r n : ℕ} (hr : 2 ≤ r)
    (hn : 100 * Real.log (r : ℝ) ≤ (n : ℝ)) :
    Real.exp ((1 : ℝ) / 2 - n / 16) ≤ 3 / (r : ℝ) ^ 6 := by
  have hrReal : (0 : ℝ) < r := by positivity
  have hlog : 0 ≤ Real.log (r : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ r by omega))
  have hexponent :
      (1 : ℝ) / 2 - n / 16 ≤
        (1 : ℝ) / 2 - 6 * Real.log (r : ℝ) := by
    nlinarith
  have hexpHalf : Real.exp ((1 : ℝ) / 2) ≤ 3 := by
    calc
      Real.exp ((1 : ℝ) / 2) ≤ Real.exp 1 :=
        Real.exp_monotone (by norm_num)
      _ ≤ 3 := Real.exp_one_lt_three.le
  have hden : Real.exp (6 * Real.log (r : ℝ)) = (r : ℝ) ^ 6 := by
    calc
      Real.exp (6 * Real.log (r : ℝ)) =
          (Real.exp (Real.log (r : ℝ))) ^ 6 := by
        simpa only [Nat.cast_ofNat] using
          Real.exp_nat_mul (Real.log (r : ℝ)) 6
      _ = (r : ℝ) ^ 6 := by rw [Real.exp_log hrReal]
  calc
    Real.exp ((1 : ℝ) / 2 - n / 16) ≤
        Real.exp ((1 : ℝ) / 2 - 6 * Real.log (r : ℝ)) :=
      Real.exp_monotone hexponent
    _ = Real.exp ((1 : ℝ) / 2) / (r : ℝ) ^ 6 := by
      rw [Real.exp_sub, hden]
    _ ≤ 3 / (r : ℝ) ^ 6 :=
      div_le_div_of_nonneg_right hexpHalf (by positivity)

/-- At the v1 threshold, a polynomial upper bound on the number of bins
makes the Chernoff exceptional probability at most `1/(3q)`. -/
theorem binCount_mul_exp_le_one_div_three {r n q : ℕ}
    (hr : 21 ≤ r)
    (hn : 100 * Real.log (r : ℝ) ≤ (n : ℝ))
    (hqpos : 0 < q)
    (hq : (q : ℝ) ≤ 7 * r * Real.log (r : ℝ)) :
    (q : ℝ) * Real.exp ((1 : ℝ) / 2 - n / 16) ≤
      ((1 : ℝ) / q) / 3 := by
  have hrTwo : 2 ≤ r := by omega
  have hrReal : (0 : ℝ) < r := by positivity
  have hqReal : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hlogLe : Real.log (r : ℝ) ≤ r :=
    (Real.log_le_sub_one_of_pos hrReal).trans (by linarith)
  have hqPoly : (q : ℝ) ≤ 7 * (r : ℝ) ^ 2 := by
    calc
      (q : ℝ) ≤ 7 * r * Real.log (r : ℝ) := hq
      _ ≤ 7 * (r : ℝ) ^ 2 := by
        calc
          7 * (r : ℝ) * Real.log (r : ℝ) ≤ 7 * r * r :=
            mul_le_mul_of_nonneg_left hlogLe (by positivity)
          _ = 7 * (r : ℝ) ^ 2 := by ring
  have hqSq : (q : ℝ) ^ 2 ≤ 49 * (r : ℝ) ^ 4 := by
    calc
      (q : ℝ) ^ 2 ≤ (7 * (r : ℝ) ^ 2) ^ 2 := by gcongr
      _ = 49 * (r : ℝ) ^ 4 := by ring
  have htail := exp_half_sub_six_log_le hrTwo hn
  have hproduct :
      3 * (q : ℝ) ^ 2 *
          Real.exp ((1 : ℝ) / 2 - n / 16) ≤ 1 := by
    calc
      3 * (q : ℝ) ^ 2 *
          Real.exp ((1 : ℝ) / 2 - n / 16) ≤
        3 * (49 * (r : ℝ) ^ 4) * (3 / (r : ℝ) ^ 6) := by
          gcongr
      _ = 441 / (r : ℝ) ^ 2 := by
        field_simp
        ring
      _ ≤ 1 := by
        rw [div_le_one (by positivity)]
        have hrCast : (21 : ℝ) ≤ r := by exact_mod_cast hr
        nlinarith [sq_nonneg ((r : ℝ) - 21)]
  rw [div_div, le_div_iff₀ (mul_pos hqReal (by norm_num))]
  nlinarith

/-- The vertex-side size hypothesis in Lemma 4.5 implies the polynomial bin
bound used above.  The constant `7` honestly absorbs both `ceil (v/2)` and
the integer quotient; the paper writes `4` at this point, which does not
follow from its displayed hypotheses. -/
theorem subgraphFindingBinCount_le_seven_mul {r n v : ℕ}
    (hr : 21 ≤ r)
    (hn : 100 * Real.log (r : ℝ) ≤ (n : ℝ))
    (hv : (v : ℝ) ≤ 2 * (r * Real.log (r : ℝ)) * n) :
    (subgraphFindingBinCount n v : ℝ) ≤
      7 * r * Real.log (r : ℝ) := by
  let a := (v + 1) / 2
  let q := subgraphFindingBinCount n v
  have hrReal : (0 : ℝ) < r := by positivity
  have hexpLt : Real.exp 1 < (r : ℝ) := by
    exact Real.exp_one_lt_three.trans_le (by exact_mod_cast (show 3 ≤ r by omega))
  have hlogOne : (1 : ℝ) < Real.log (r : ℝ) :=
    (Real.lt_log_iff_exp_lt hrReal).mpr hexpLt
  have hnReal : (0 : ℝ) < n := by
    have : (0 : ℝ) < 100 * Real.log (r : ℝ) := by positivity
    exact this.trans_le hn
  have hnOne : (1 : ℝ) ≤ n := by
    exact_mod_cast (show 1 ≤ n by exact_mod_cast hnReal)
  have hthree : (3 : ℝ) ≤ r * Real.log (r : ℝ) * n := by
    calc
      (3 : ℝ) ≤ r := by exact_mod_cast (show 3 ≤ r by omega)
      _ = (r : ℝ) * 1 * 1 := by ring
      _ ≤ r * Real.log (r : ℝ) * n := by gcongr
  have hceilNat : 2 * a ≤ v + 1 := by
    dsimp only [a]
    exact Nat.mul_div_le _ _
  have hqNat : n * q ≤ 6 * a := by
    dsimp only [q, a]
    exact mul_subgraphFindingBinCount_le n v
  have hceil : (2 : ℝ) * a ≤ v + 1 := by exact_mod_cast hceilNat
  have hqCast : (n : ℝ) * q ≤ 6 * a := by exact_mod_cast hqNat
  have htotal : (q : ℝ) * n ≤
      (7 * r * Real.log (r : ℝ)) * n := by
    calc
      (q : ℝ) * n = n * q := by ring
      _ ≤ 6 * a := hqCast
      _ ≤ 3 * (v + 1) := by nlinarith
      _ ≤ 6 * (r * Real.log (r : ℝ)) * n + 3 := by
        nlinarith
      _ ≤ 7 * (r * Real.log (r : ℝ)) * n := by
        nlinarith
      _ = (7 * r * Real.log (r : ℝ)) * n := by ring
  change (q : ℝ) ≤ 7 * r * Real.log (r : ℝ)
  nlinarith

/-- Maximum degree restricted to a specified finite side of a vertex
partition. -/
def maxDegreeOn [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : ℕ :=
  S.sup fun x ↦ G.degree x

/-! ## The finite balls-and-bins model from Appendix A -/

/-- Number of balls sent to bin `i` by an allocation `f`. -/
def binLoad {q d : ℕ} (f : Fin d → Fin q) (i : Fin q) : ℕ :=
  #{j ∈ (Finset.univ : Finset (Fin d)) | f j = i}

/-- Maximum occupancy of a bin.  This is the paper's random variable
`M_{q,d}`, evaluated at one allocation. -/
def maxBinLoad {q d : ℕ} (f : Fin d → Fin q) : ℕ :=
  (Finset.univ : Finset (Fin q)).sup (binLoad f)

/-- Uniform expectation of `M_{q,d}`, written as a literal average over the
finite function space. -/
def expectedMaxBinLoad (q d : ℕ) : ℝ :=
  (∑ f : Fin d → Fin q, (maxBinLoad f : ℝ)) /
    Fintype.card (Fin d → Fin q)

/-- Normalised expected maximum occupancy, the paper's `W(q,d)`. -/
def ballsBinsWeight (q d : ℕ) : ℝ :=
  expectedMaxBinLoad q d / d

/-- The same occupancy statistic on an arbitrary finite labelled set of
balls.  This form is needed for restricting a global vertex partition to a
neighbourhood. -/
def binLoadOn {D : Type*} [Fintype D] [DecidableEq D] {q : ℕ}
    (f : D → Fin q) (i : Fin q) : ℕ :=
  #{x ∈ (Finset.univ : Finset D) | f x = i}

def maxBinLoadOn {D : Type*} [Fintype D] [DecidableEq D] {q : ℕ}
    (f : D → Fin q) : ℕ :=
  (Finset.univ : Finset (Fin q)).sup (binLoadOn f)

/-- Relabelling the balls does not change any bin load. -/
theorem binLoadOn_comp_equiv {D E : Type*} [Fintype D] [Fintype E]
    [DecidableEq D] [DecidableEq E] {q : ℕ}
    (e : D ≃ E) (f : E → Fin q) (i : Fin q) :
    binLoadOn (f ∘ e) i = binLoadOn f i := by
  unfold binLoadOn
  apply Finset.card_bij (fun x _ ↦ e x)
  · intro x hx
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
      Function.comp_apply] using (Finset.mem_filter.mp hx).2
  · intro x _ y _ hxy
    exact e.injective hxy
  · intro y hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
      Function.comp_apply, e.apply_symm_apply] using
      (Finset.mem_filter.mp hy).2

theorem maxBinLoadOn_comp_equiv {D E : Type*} [Fintype D] [Fintype E]
    [DecidableEq D] [DecidableEq E] {q : ℕ}
    (e : D ≃ E) (f : E → Fin q) :
    maxBinLoadOn (f ∘ e) = maxBinLoadOn f := by
  unfold maxBinLoadOn
  apply congrArg (Finset.sup Finset.univ)
  funext i
  exact binLoadOn_comp_equiv e f i

/-- No bin contains more than the total number of labels in an arbitrary
finite domain. -/
theorem maxBinLoadOn_le_card {D : Type*} [Fintype D] [DecidableEq D]
    {q : ℕ} (f : D → Fin q) : maxBinLoadOn f ≤ Fintype.card D := by
  apply Finset.sup_le
  intro i _
  simpa only [binLoadOn, Finset.card_univ] using
    Finset.card_le_card (Finset.filter_subset
      (fun x ↦ f x = i) (Finset.univ : Finset D))

@[simp]
theorem binLoadOn_fin_eq_binLoad {q d : ℕ} (f : Fin d → Fin q)
    (i : Fin q) : binLoadOn f i = binLoad f i := rfl

@[simp]
theorem maxBinLoadOn_fin_eq_maxBinLoad {q d : ℕ} (f : Fin d → Fin q) :
    maxBinLoadOn f = maxBinLoad f := rfl

/-- Split an assignment into its restrictions to a predicate and its
complement. -/
def splitAssignmentEquiv {D : Type*} (p : D → Prop) [DecidablePred p]
    (q : ℕ) :
    (D → Fin q) ≃
      (({x // p x} → Fin q) × ({x // ¬p x} → Fin q)) :=
  (Equiv.piCongrLeft (fun _ : D ↦ Fin q) (Equiv.sumCompl p)).symm.trans
    (Equiv.sumArrowEquivProdArrow _ _ _)

@[simp]
theorem splitAssignmentEquiv_fst_apply {D : Type*} (p : D → Prop)
    [DecidablePred p] (q : ℕ) (f : D → Fin q) (x : {x // p x}) :
    (splitAssignmentEquiv p q f).1 x = f x := by
  rfl

/-- Maximum load after restricting a global assignment to a predicate. -/
def restrictedMaxBinLoad {D : Type*} [Fintype D] [DecidableEq D]
    (p : D → Prop) [DecidablePred p] {q : ℕ} (f : D → Fin q) : ℕ :=
  maxBinLoadOn (fun x : {x // p x} ↦ f x)

/-- Exact restriction-fibre identity: summing a statistic depending only on
the labels in `p` multiplies it by the number of assignments outside `p`. -/
theorem sum_restrictedMaxBinLoad {D : Type*} [Fintype D] [DecidableEq D]
    (p : D → Prop) [DecidablePred p] (q : ℕ) :
    (∑ f : D → Fin q, restrictedMaxBinLoad p f) =
      Fintype.card ({x // ¬p x} → Fin q) *
        ∑ g : {x // p x} → Fin q, maxBinLoadOn g := by
  let e := splitAssignmentEquiv p q
  calc
    (∑ f : D → Fin q, restrictedMaxBinLoad p f) =
        ∑ f : D → Fin q, maxBinLoadOn (e f).1 := by
      apply Finset.sum_congr rfl
      intro f _
      apply congrArg maxBinLoadOn
      funext x
      exact (splitAssignmentEquiv_fst_apply p q f x).symm
    _ = ∑ z : ({x // p x} → Fin q) × ({x // ¬p x} → Fin q),
          maxBinLoadOn z.1 := Equiv.sum_comp e (fun z ↦ maxBinLoadOn z.1)
    _ = ∑ g : {x // p x} → Fin q,
          ∑ _h : {x // ¬p x} → Fin q, maxBinLoadOn g := by
      rw [Fintype.sum_prod_type]
    _ = Fintype.card ({x // ¬p x} → Fin q) *
        ∑ g : {x // p x} → Fin q, maxBinLoadOn g := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [Finset.mul_sum]
      rfl

/-- The arbitrary-domain maximum-load sum is the paper's standard
`Fin d` sum after relabelling by `Fintype.equivFin`. -/
theorem sum_maxBinLoadOn_eq_fin {D : Type*} [Fintype D] [DecidableEq D]
    (q : ℕ) :
    (∑ g : D → Fin q, maxBinLoadOn g) =
      ∑ f : Fin (Fintype.card D) → Fin q, maxBinLoad f := by
  let e : D ≃ Fin (Fintype.card D) := Fintype.equivFin D
  let E : (D → Fin q) ≃ (Fin (Fintype.card D) → Fin q) :=
    Equiv.arrowCongr e (Equiv.refl (Fin q))
  calc
    (∑ g : D → Fin q, maxBinLoadOn g) =
        ∑ g : D → Fin q, maxBinLoad (E g) := by
      apply Finset.sum_congr rfl
      intro g _
      have h := maxBinLoadOn_comp_equiv e.symm g
      change maxBinLoadOn g = maxBinLoad (g ∘ e.symm)
      simpa only [maxBinLoadOn_fin_eq_maxBinLoad] using h.symm
    _ = ∑ f : Fin (Fintype.card D) → Fin q, maxBinLoad f :=
      Equiv.sum_comp E maxBinLoad

/-- A global uniform assignment restricts to a uniform assignment on every
fixed finite predicate.  This is the exact finite-fibre statement needed to
turn the per-vertex balls-and-bins expectation into one global partition of
`A`; no independence between different neighbourhoods is assumed. -/
theorem uniformAverage_restrictedMaxBinLoad
    {D : Type*} [Fintype D] [DecidableEq D]
    (p : D → Prop) [DecidablePred p] {q : ℕ} (hq : 0 < q) :
    (∑ f : D → Fin q, (restrictedMaxBinLoad p f : ℝ)) /
        Fintype.card (D → Fin q) =
      expectedMaxBinLoad q (Fintype.card {x // p x}) := by
  let P := {x // p x}
  let C := {x // ¬p x}
  have hsumNat := sum_restrictedMaxBinLoad p q
  have hsum :
      (∑ f : D → Fin q, (restrictedMaxBinLoad p f : ℝ)) =
        Fintype.card (C → Fin q) *
          ∑ g : P → Fin q, (maxBinLoadOn g : ℝ) := by
    exact_mod_cast hsumNat
  have hcardNat :
      Fintype.card (D → Fin q) =
        Fintype.card (P → Fin q) * Fintype.card (C → Fin q) := by
    calc
      Fintype.card (D → Fin q) =
          Fintype.card ((P → Fin q) × (C → Fin q)) :=
        Fintype.card_congr (splitAssignmentEquiv p q)
      _ = Fintype.card (P → Fin q) * Fintype.card (C → Fin q) :=
        Fintype.card_prod _ _
  have hcard :
      (Fintype.card (D → Fin q) : ℝ) =
        Fintype.card (P → Fin q) * Fintype.card (C → Fin q) := by
    exact_mod_cast hcardNat
  have hlocalSum :
      (∑ g : P → Fin q, (maxBinLoadOn g : ℝ)) =
        ∑ f : Fin (Fintype.card P) → Fin q, (maxBinLoad f : ℝ) := by
    exact_mod_cast sum_maxBinLoadOn_eq_fin (D := P) q
  have hlocalCard :
      Fintype.card (P → Fin q) =
        Fintype.card (Fin (Fintype.card P) → Fin q) := by
    simp only [Fintype.card_fun, Fintype.card_fin]
  have hcompPos : (0 : ℝ) < Fintype.card (C → Fin q) := by
    have : Nonempty (C → Fin q) :=
      ⟨fun _ ↦ ⟨0, hq⟩⟩
    exact_mod_cast Fintype.card_pos
  rw [expectedMaxBinLoad, hsum, hcard, hlocalSum, ← hlocalCard]
  field_simp
  rfl

/-- Remove one labelled ball from an allocation.  The order-preserving
embedding `j.succAbove` identifies the remaining `d` labels with all labels
other than `j`. -/
def deleteBall {q d : ℕ} (f : Fin (d + 1) → Fin q) (j : Fin (d + 1)) :
    Fin d → Fin q :=
  fun x ↦ f (j.succAbove x)

/-- Allocations forcing every ball in `S` into the fixed bin `i`. -/
def fixedBinEvent {q d : ℕ} (i : Fin q) (S : Finset (Fin d)) :
    Finset (Fin d → Fin q) :=
  Finset.univ.filter fun f ↦ ∀ x ∈ S, f x = i

/-- Allocations forcing two disjoint labelled sets into two specified bins. -/
def fixedTwoBinEvent {q d : ℕ} (i j : Fin q)
    (S T : Finset (Fin d)) : Finset (Fin d → Fin q) :=
  Finset.univ.filter fun f ↦
    (∀ x ∈ S, f x = i) ∧ (∀ x ∈ T, f x = j)

/-- A witness for an allocation with load exactly `t` in bin `i`: choose
the fibre of `i`, and label every point outside it by a different bin. -/
def ExactLoadWitness {q d : ℕ} (i : Fin q) (t : ℕ) :=
  Σ S : ↑((Finset.univ : Finset (Fin d)).powersetCard t),
    (↑(Finset.univ \ S.1) → {j : Fin q // j ≠ i})

/-- The allocation encoded by an exact-load witness. -/
def ExactLoadWitness.assignment {q d : ℕ} {i : Fin q} {t : ℕ}
    (w : ExactLoadWitness (d := d) i t) : Fin d → Fin q :=
  fun x ↦ if hx : x ∈ w.1.1 then i else
    (w.2 ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩⟩).1

noncomputable instance instFintypeExactLoadWitness {q d : ℕ}
    (i : Fin q) (t : ℕ) : Fintype (ExactLoadWitness (d := d) i t) := by
  classical
  unfold ExactLoadWitness
  infer_instance

/-! The following generic named-bin model is used only for conditioning on
one distinguished bin.  The remaining colours form a subtype rather than a
literal `Fin`, so phrasing the load for an arbitrary finite codomain avoids
any choice of relabelling. -/

/-- Cardinality of a named fibre for functions between arbitrary finite
types. -/
def namedBinLoad {D B : Type*} [Fintype D] [DecidableEq B]
    (f : D → B) (b : B) : ℕ :=
  Fintype.card {x : D // f x = b}

/-- Uniform finite event that a named bin reaches a threshold. -/
def namedBinTailEvent (B : Type*) [Fintype B] [DecidableEq B]
    (b : B) (d t : ℕ) : Finset (Fin d → B) :=
  Finset.univ.filter fun f ↦ t ≤ namedBinLoad f b

/-- Type-valued version of `namedBinTailEvent`, convenient under changes
of the finite trial type. -/
abbrev NamedBinTailType (D B : Type*) [Fintype D] [DecidableEq D]
    [Fintype B]
    [DecidableEq B] (b : B) (t : ℕ) :=
  {f : D → B // t ≤ namedBinLoad f b}

/-- Tail probability written as a literal finite quotient. -/
def namedBinTailFraction (B : Type*) [Fintype B] [DecidableEq B]
    (b : B) (d t : ℕ) : ℝ :=
  ((namedBinTailEvent B b d t).card : ℝ) /
    (Fintype.card B : ℝ) ^ d

/-- Add one labelled trial at the front of an allocation. -/
def prependAllocation {B : Type*} {d : ℕ} (c : B) (f : Fin d → B) :
    Fin (d + 1) → B :=
  Fin.cases c f

/-- The upper-tail event that bin `i` contains at least `t` balls. -/
def binLoadAtLeastEvent {q d : ℕ} (i : Fin q) (t : ℕ) :
  Finset (Fin d → Fin q) :=
  Finset.univ.filter fun f ↦ t ≤ binLoad f i

/-- Exact slice of the allocation space by the load of one named bin. -/
def binLoadEqEvent {q d : ℕ} (i : Fin q) (a : ℕ) :
    Finset (Fin d → Fin q) :=
  Finset.univ.filter fun f ↦ binLoad f i = a

/-- One exact load together with an upper tail in a second named bin. -/
def binLoadEqTailEvent {q d : ℕ} (i j : Fin q) (a t : ℕ) :
    Finset (Fin d → Fin q) :=
  Finset.univ.filter fun f ↦ binLoad f i = a ∧ t ≤ binLoad f j

/-- Joint tail event for two named bins. -/
def twoBinLoadAtLeastEvent {q d : ℕ} (i j : Fin q) (t : ℕ) :
    Finset (Fin d → Fin q) :=
  Finset.univ.filter fun f ↦ t ≤ binLoad f i ∧ t ≤ binLoad f j

/-- The event that some bin has load at least `t`. -/
def maxBinLoadAtLeastEvent (q d t : ℕ) : Finset (Fin d → Fin q) :=
  Finset.univ.filter fun f ↦ t ≤ maxBinLoad f

/-- Allocations whose every bin is a valid vertex cover for a `P_n`-free
bipartite colour class.  The division-free inequality matches
`pathGraph_free_of_small_vertexCover` exactly. -/
def pathSafeAllocationEvent (q d n : ℕ) : Finset (Fin d → Fin q) :=
  Finset.univ.filter fun f ↦ ∀ i, 2 * binLoad f i + 1 < n

/-- Number of bins whose load reaches the threshold `t`; this is the
integer random variable `B_t` in Appendix A.2. -/
def heavyBinCount {q d : ℕ} (f : Fin d → Fin q) (t : ℕ) : ℕ :=
  #{i ∈ (Finset.univ : Finset (Fin q)) | t ≤ binLoad f i}

/-- The statement printed as Lemma 4.5 in v1.  It only bounds degrees on
`V₀`, although the proof later applies the bound to vertices of `U`.  We
retain it as an auditable record of the source, but do not use it as a proof
interface.  Version 2 repairs this by controlling the side whose
neighbourhoods enter the balls-and-bins calculation. -/
def BLSSubgraphFindingAtV1Printed [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r n : ℕ) (V₀ U : Finset V) : Prop :=
  Disjoint V₀ U → V₀ ∪ U = Finset.univ →
  (∀ ⦃x⦄, x ∈ U → ∀ ⦃y⦄, y ∈ U → ¬G.Adj x y) →
  (V₀.card : ℝ) ≤ 2 * (r * Real.log (r : ℝ)) * n →
  maxDegreeOn G V₀ ≤ ⌊r * Real.log (r : ℝ)⌋₊ →
  ∃ H : SimpleGraph V,
    H ≤ G ∧ (pathGraph n).Free H ∧
      (edgeCount G : ℝ) / 3 *
          ballsBinsWeight (subgraphFindingBinCount n V₀.card)
            (maxDegreeOn G V₀) ≤ (edgeCount H : ℝ)

/-- Repaired subgraph-finding interface used by the formal proof.  The
residual graphs in the v1 proof of the key lemma have exactly this global
degree bound, so the repair does not strengthen the hypotheses at the
actual call sites. -/
def BLSSubgraphFindingAt [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r n Δ : ℕ) (V₀ U : Finset V) : Prop :=
  Disjoint V₀ U → V₀ ∪ U = Finset.univ →
  (∀ ⦃x⦄, x ∈ U → ∀ ⦃y⦄, y ∈ U → ¬G.Adj x y) →
  (V₀.card : ℝ) ≤ 2 * (r * Real.log (r : ℝ)) * n →
  (∀ x, G.degree x ≤ Δ) →
  Δ ≤ ⌊r * Real.log (r : ℝ)⌋₊ →
  ∃ H : SimpleGraph V,
    H ≤ G ∧ (pathGraph n).Free H ∧
      (edgeCount G : ℝ) / 3 *
          ballsBinsWeight (subgraphFindingBinCount n V₀.card) Δ ≤
        (edgeCount H : ℝ)

/-- Quantifier package for the repaired Lemma 4.5 interface, retaining the
v1 threshold `n ≥ 100 log r`. -/
def BLSSubgraphFindingV1 : Prop :=
  ∃ r₀ : ℕ, ∀ r : ℕ, r₀ ≤ r →
    ∀ n : ℕ, 100 * Real.log (r : ℝ) ≤ (n : ℝ) →
      ∀ N : ℕ, ∀ G : SimpleGraph (Fin N),
        ∀ Δ : ℕ, ∀ V₀ U : Finset (Fin N),
          @BLSSubgraphFindingAt (Fin N) inferInstance inferInstance G
            (Classical.decRel _) r n Δ V₀ U

/-- Every ball is counted in exactly one bin. -/
theorem sum_binLoad {q d : ℕ} (f : Fin d → Fin q) :
    ∑ i, binLoad f i = d := by
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Fin d)))
    (t := (Finset.univ : Finset (Fin q)))
    (f := f) (fun _ _ ↦ Finset.mem_univ _)
  simpa only [binLoad, Finset.card_univ, Fintype.card_fin] using h.symm

/-- The load of any fixed bin is at most the maximum load. -/
theorem binLoad_le_maxBinLoad {q d : ℕ} (f : Fin d → Fin q) (i : Fin q) :
    binLoad f i ≤ maxBinLoad f := by
  exact Finset.le_sup (f := binLoad f) (Finset.mem_univ i)

/-- Failure of path-safety is literally the maximum-load upper-tail event
at threshold `floor (n/2)`.  This removes the paper's ambiguous real-valued
notation `k/2 - 1` from the discrete proof. -/
theorem complement_pathSafeAllocationEvent {q d n : ℕ} (hn : 2 ≤ n) :
    (Finset.univ : Finset (Fin d → Fin q)) \
        pathSafeAllocationEvent q d n =
      maxBinLoadAtLeastEvent q d (n / 2) := by
  ext f
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
    pathSafeAllocationEvent, maxBinLoadAtLeastEvent, Finset.mem_filter]
  constructor
  · intro hbad
    push Not at hbad
    obtain ⟨i, hi⟩ := hbad
    exact (show n / 2 ≤ binLoad f i by omega).trans
      (binLoad_le_maxBinLoad f i)
  · intro hmax hsafe
    have hmaxLt : maxBinLoad f < n / 2 := by
      rw [maxBinLoad, Finset.sup_lt_iff (show (0 : ℕ) < n / 2 by omega)]
      intro i _
      have hi := hsafe i
      omega
    omega

theorem heavyBinCount_ne_zero_iff_mem_maxEvent {q d t : ℕ}
    (hq : 0 < q) (f : Fin d → Fin q) :
    heavyBinCount f t ≠ 0 ↔ f ∈ maxBinLoadAtLeastEvent q d t := by
  constructor
  · intro hnonzero
    have hnonempty :
        (Finset.univ.filter fun i : Fin q ↦ t ≤ binLoad f i).Nonempty :=
      Finset.card_ne_zero.mp hnonzero
    obtain ⟨i, hi⟩ := hnonempty
    rw [maxBinLoadAtLeastEvent, Finset.mem_filter]
    exact ⟨Finset.mem_univ f,
      (Finset.mem_filter.mp hi).2.trans (binLoad_le_maxBinLoad f i)⟩
  · intro hf
    have hmax : t ≤ maxBinLoad f := (Finset.mem_filter.mp hf).2
    obtain ⟨i, _hi, himax⟩ := Finset.exists_mem_eq_sup
      (s := (Finset.univ : Finset (Fin q)))
      (Finset.univ_nonempty_iff.mpr ⟨0, hq⟩) (binLoad f)
    apply Finset.card_ne_zero.mpr
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩⟩
    exact himax ▸ hmax

theorem support_heavyBinCount_eq_maxEvent {q d t : ℕ} (hq : 0 < q) :
    (Finset.univ : Finset (Fin d → Fin q)).filter
        (fun f ↦ (heavyBinCount f t : ℝ) ≠ 0) =
      maxBinLoadAtLeastEvent q d t := by
  ext f
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, Nat.cast_ne_zero]
  exact heavyBinCount_ne_zero_iff_mem_maxEvent hq f

/-- First moment of `B_t`, written as a sum of the fixed-bin tail counts. -/
theorem sum_heavyBinCount {q d t : ℕ} :
    ∑ f : Fin d → Fin q, heavyBinCount f t =
      ∑ i : Fin q, (binLoadAtLeastEvent (d := d) i t).card := by
  calc
    (∑ f : Fin d → Fin q, heavyBinCount f t) =
        ∑ f : Fin d → Fin q,
          ∑ i : Fin q, if t ≤ binLoad f i then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro f _
      exact Finset.card_filter _ _
    _ = ∑ i : Fin q,
        ∑ f : Fin d → Fin q, if t ≤ binLoad f i then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ i : Fin q, (binLoadAtLeastEvent (d := d) i t).card := by
      apply Finset.sum_congr rfl
      intro i _
      symm
      exact Finset.card_filter _ _

theorem heavyBinCount_sq {q d t : ℕ} (f : Fin d → Fin q) :
    (heavyBinCount f t) ^ 2 =
      ∑ i : Fin q, ∑ j : Fin q,
        if t ≤ binLoad f i ∧ t ≤ binLoad f j then 1 else 0 := by
  have hcount : heavyBinCount f t =
      ∑ i : Fin q, if t ≤ binLoad f i then 1 else 0 :=
    Finset.card_filter _ _
  rw [hcount, pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hi : t ≤ binLoad f i <;>
    by_cases hj : t ≤ binLoad f j <;> simp [hi, hj]

/-- Second moment of `B_t` as the sum of all ordered two-bin joint-tail
counts. -/
theorem sum_sq_heavyBinCount {q d t : ℕ} :
    ∑ f : Fin d → Fin q, (heavyBinCount f t) ^ 2 =
      ∑ i : Fin q, ∑ j : Fin q,
        (twoBinLoadAtLeastEvent (d := d) i j t).card := by
  calc
    (∑ f : Fin d → Fin q, (heavyBinCount f t) ^ 2) =
        ∑ f : Fin d → Fin q, ∑ i : Fin q, ∑ j : Fin q,
          if t ≤ binLoad f i ∧ t ≤ binLoad f j then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro f _
      exact heavyBinCount_sq f
    _ = ∑ i : Fin q, ∑ j : Fin q, ∑ f : Fin d → Fin q,
          if t ≤ binLoad f i ∧ t ≤ binLoad f j then 1 else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ i : Fin q, ∑ j : Fin q,
        (twoBinLoadAtLeastEvent (d := d) i j t).card := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      symm
      exact Finset.card_filter _ _

theorem binLoad_comp_swap {q d : ℕ} (i j : Fin q)
    (f : Fin d → Fin q) :
    binLoad (Equiv.swap i j ∘ f) j = binLoad f i := by
  unfold binLoad
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Function.comp_apply, Equiv.swap_apply_eq_iff,
    Equiv.swap_apply_right]

/-- Uniform bin labels make every fixed-bin upper-tail event equicardinal. -/
theorem card_binLoadAtLeastEvent_eq {q d t : ℕ} (i j : Fin q) :
    (binLoadAtLeastEvent (d := d) i t).card =
      (binLoadAtLeastEvent (d := d) j t).card := by
  let swapAssignment : (Fin d → Fin q) → (Fin d → Fin q) :=
    fun f ↦ Equiv.swap i j ∘ f
  apply Finset.card_bij (fun f _ ↦ swapAssignment f)
  · intro f hf
    rw [binLoadAtLeastEvent, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [binLoad_comp_swap]
    exact (Finset.mem_filter.mp hf).2
  · intro f _ g _ hfg
    funext x
    apply (Equiv.swap i j).injective
    exact congrFun hfg x
  · intro g hg
    refine ⟨swapAssignment g, ?_, ?_⟩
    · rw [binLoadAtLeastEvent, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have hj : t ≤ binLoad g j := (Finset.mem_filter.mp hg).2
      have hload := binLoad_comp_swap j i g
      calc
        t ≤ binLoad g j := hj
        _ = binLoad (Equiv.swap j i ∘ g) i := hload.symm
        _ = binLoad (swapAssignment g) i := by
          rw [Equiv.swap_comm]
    · funext x
      simp only [swapAssignment, Function.comp_apply, Equiv.swap_apply_self]

theorem sum_heavyBinCount_eq_mul_fixed {q d t : ℕ} (i : Fin q) :
    ∑ f : Fin d → Fin q, heavyBinCount f t =
      q * (binLoadAtLeastEvent (d := d) i t).card := by
  rw [sum_heavyBinCount]
  calc
    (∑ j : Fin q, (binLoadAtLeastEvent (d := d) j t).card) =
        ∑ _j : Fin q, (binLoadAtLeastEvent (d := d) i t).card := by
      apply Finset.sum_congr rfl
      intro j _
      exact card_binLoadAtLeastEvent_eq j i
    _ = q * (binLoadAtLeastEvent (d := d) i t).card := by simp

@[simp]
theorem twoBinLoadAtLeastEvent_self {q d t : ℕ} (i : Fin q) :
    twoBinLoadAtLeastEvent (d := d) i i t =
      binLoadAtLeastEvent (d := d) i t := by
  ext f
  simp only [twoBinLoadAtLeastEvent, binLoadAtLeastEvent,
    Finset.mem_filter, Finset.mem_univ, true_and, and_self]

/-- Abstract second-moment estimate after supplying a uniform off-diagonal
two-bin correlation bound.  Appendix A.2 reduces precisely to proving the
`hpair` inequality with a small constant `C`. -/
theorem sum_sq_heavyBinCount_le_of_pair_bound {q d t : ℕ}
    (i₀ : Fin q) {C : ℝ}
    (hpair : ∀ i j : Fin q, i ≠ j →
      ((twoBinLoadAtLeastEvent (d := d) i j t).card : ℝ) ≤
        C * ((binLoadAtLeastEvent (d := d) i₀ t).card : ℝ) ^ 2 /
          Fintype.card (Fin d → Fin q)) :
    ∑ f : Fin d → Fin q, (heavyBinCount f t : ℝ) ^ 2 ≤
      q * (binLoadAtLeastEvent (d := d) i₀ t).card +
        q * (q - 1) *
          (C * ((binLoadAtLeastEvent (d := d) i₀ t).card : ℝ) ^ 2 /
            Fintype.card (Fin d → Fin q)) := by
  let A : ℝ := (binLoadAtLeastEvent (d := d) i₀ t).card
  let J : ℝ := C * A ^ 2 / Fintype.card (Fin d → Fin q)
  have hqOne : 1 ≤ q := by
    exact (Nat.succ_le_iff).mpr (lt_of_le_of_lt (Nat.zero_le _) i₀.isLt)
  have hsecond :
      (∑ f : Fin d → Fin q, (heavyBinCount f t : ℝ) ^ 2) =
        ∑ i : Fin q, ∑ j : Fin q,
          ((twoBinLoadAtLeastEvent (d := d) i j t).card : ℝ) := by
    exact_mod_cast sum_sq_heavyBinCount (q := q) (d := d) (t := t)
  rw [hsecond]
  have hinner : ∀ i : Fin q,
      (∑ j : Fin q,
          ((twoBinLoadAtLeastEvent (d := d) i j t).card : ℝ)) ≤
        A + (q - 1) * J := by
    intro i
    have hdiag :
        ((twoBinLoadAtLeastEvent (d := d) i i t).card : ℝ) = A := by
      rw [twoBinLoadAtLeastEvent_self]
      dsimp only [A]
      exact_mod_cast card_binLoadAtLeastEvent_eq i i₀
    calc
      (∑ j : Fin q,
          ((twoBinLoadAtLeastEvent (d := d) i j t).card : ℝ)) =
        (∑ j ∈ (Finset.univ : Finset (Fin q)).erase i,
          ((twoBinLoadAtLeastEvent (d := d) i j t).card : ℝ)) +
            ((twoBinLoadAtLeastEvent (d := d) i i t).card : ℝ) := by
          exact (Finset.sum_erase_add (Finset.univ : Finset (Fin q))
            (fun j ↦ ((twoBinLoadAtLeastEvent (d := d) i j t).card : ℝ))
            (Finset.mem_univ i)).symm
      _ ≤ (∑ _j ∈ (Finset.univ : Finset (Fin q)).erase i, J) + A := by
        apply add_le_add
        · apply Finset.sum_le_sum
          intro j hj
          dsimp only [J, A]
          apply hpair i j
          exact (Finset.ne_of_mem_erase hj).symm
        · exact hdiag.le
      _ = A + (q - 1) * J := by
        simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [Nat.cast_sub hqOne]
        ring
  calc
    (∑ i : Fin q, ∑ j : Fin q,
        ((twoBinLoadAtLeastEvent (d := d) i j t).card : ℝ)) ≤
      ∑ _i : Fin q, (A + (q - 1) * J) :=
        Finset.sum_le_sum fun i _ ↦ hinner i
    _ = q * A + q * (q - 1) * J := by simp; ring
    _ = q * (binLoadAtLeastEvent (d := d) i₀ t).card +
        q * (q - 1) *
          (C * ((binLoadAtLeastEvent (d := d) i₀ t).card : ℝ) ^ 2 /
            Fintype.card (Fin d → Fin q)) := by rfl

/-- Fixing the colours of `|S|` balls leaves at most `q^(d-|S|)`
allocations. -/
theorem card_fixedBinEvent_le {q d : ℕ} (i : Fin q)
    (S : Finset (Fin d)) :
    (fixedBinEvent i S).card ≤ q ^ (d - S.card) := by
  classical
  let C : Finset (Fin d) := Finset.univ \ S
  let restrict : ↑(fixedBinEvent i S) → (↑C → Fin q) :=
    fun f x ↦ f.1 x.1
  have hrestrict : Function.Injective restrict := by
    intro f g hfg
    apply Subtype.ext
    funext x
    by_cases hx : x ∈ S
    · have hf : f.1 x = i :=
        (Finset.mem_filter.mp f.2).2 x hx
      have hg : g.1 x = i :=
        (Finset.mem_filter.mp g.2).2 x hx
      exact hf.trans hg.symm
    · have hxC : x ∈ C := by
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩
      have := congrFun hfg (⟨x, hxC⟩ : ↑C)
      exact this
  have hcard := Fintype.card_le_of_injective restrict hrestrict
  have hCcard : C.card = d - S.card := by
    change (Finset.univ \ S).card = d - S.card
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ,
      Fintype.card_fin]
  simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin,
    hCcard] using hcard

/-- Two disjoint forced fibres leave at most
`q^(d-|S|-|T|)` free assignments. -/
theorem card_fixedTwoBinEvent_le {q d : ℕ} (i j : Fin q)
    (S T : Finset (Fin d)) (hST : Disjoint S T) :
    (fixedTwoBinEvent i j S T).card ≤
      q ^ (d - (S.card + T.card)) := by
  classical
  let C : Finset (Fin d) := Finset.univ \ (S ∪ T)
  let restrict : ↑(fixedTwoBinEvent i j S T) → (↑C → Fin q) :=
    fun f x ↦ f.1 x.1
  have hrestrict : Function.Injective restrict := by
    intro f g hfg
    apply Subtype.ext
    funext x
    by_cases hxS : x ∈ S
    · have hf : f.1 x = i :=
        (Finset.mem_filter.mp f.2).2.1 x hxS
      have hg : g.1 x = i :=
        (Finset.mem_filter.mp g.2).2.1 x hxS
      exact hf.trans hg.symm
    · by_cases hxT : x ∈ T
      · have hf : f.1 x = j :=
          (Finset.mem_filter.mp f.2).2.2 x hxT
        have hg : g.1 x = j :=
          (Finset.mem_filter.mp g.2).2.2 x hxT
        exact hf.trans hg.symm
      · have hxC : x ∈ C := by
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x,
            by simpa only [Finset.mem_union, not_or] using ⟨hxS, hxT⟩⟩
        exact congrFun hfg (⟨x, hxC⟩ : ↑C)
  have hcard := Fintype.card_le_of_injective restrict hrestrict
  have hUnionCard : (S ∪ T).card = S.card + T.card :=
    Finset.card_union_of_disjoint hST
  have hCcard : C.card = d - (S.card + T.card) := by
    change (Finset.univ \ (S ∪ T)).card = d - (S.card + T.card)
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ (S ∪ T)),
      Finset.card_univ, Fintype.card_fin, hUnionCard]
  simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin,
    hCcard] using hcard

@[simp]
theorem exactLoadWitness_assignment_eq_iff_mem {q d : ℕ} {i : Fin q}
    {t : ℕ} (w : ExactLoadWitness i t) (x : Fin d) :
    w.assignment x = i ↔ x ∈ w.1.1 := by
  classical
  by_cases hx : x ∈ w.1.1
  · simp [ExactLoadWitness.assignment, hx]
  · simp [ExactLoadWitness.assignment, hx,
      (w.2 ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩⟩).2]

/-- Exact-load witnesses encode distinct allocations.  This is the
disjointness bookkeeping behind the usual binomial point-mass formula. -/
theorem exactLoadWitness_assignment_injective {q d : ℕ} (i : Fin q)
    (t : ℕ) :
    Function.Injective
      (ExactLoadWitness.assignment : ExactLoadWitness i t → Fin d → Fin q) := by
  classical
  rintro ⟨S, g⟩ ⟨T, h⟩ heq
  have hSTval : S.1 = T.1 := by
    ext x
    rw [← exactLoadWitness_assignment_eq_iff_mem (⟨S, g⟩ :
      ExactLoadWitness i t) x,
      ← exactLoadWitness_assignment_eq_iff_mem (⟨T, h⟩ :
        ExactLoadWitness i t) x]
    rw [congrFun heq x]
  have hST : S = T := Subtype.ext hSTval
  subst T
  congr 1
  funext x
  apply Subtype.ext
  have hx : x.1 ∉ S.1 := (Finset.mem_sdiff.mp x.2).2
  simpa [ExactLoadWitness.assignment, hx] using congrFun heq x.1

/-- Every exact-load witness lies in the corresponding upper-tail event. -/
theorem exactLoadWitness_assignment_mem_tail {q d : ℕ} (i : Fin q)
    (t : ℕ) (w : ExactLoadWitness i t) :
    w.assignment ∈ binLoadAtLeastEvent (d := d) i t := by
  rw [binLoadAtLeastEvent, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  calc
    t = w.1.1.card :=
      (Finset.mem_powersetCard.mp w.1.2).2.symm
    _ ≤ #{x ∈ (Finset.univ : Finset (Fin d)) |
        w.assignment x = i} := by
      apply Finset.card_le_card
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (exactLoadWitness_assignment_eq_iff_mem w x).2 hx
    _ = binLoad w.assignment i := rfl

/-- The distinguished bin has exactly the witness fibre. -/
theorem binLoad_exactLoadWitness_assignment {q d : ℕ} (i : Fin q)
    (t : ℕ) (w : ExactLoadWitness (d := d) i t) :
    binLoad w.assignment i = t := by
  have hfibre :
      (Finset.univ.filter fun x : Fin d ↦ w.assignment x = i) = w.1.1 := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact exactLoadWitness_assignment_eq_iff_mem w x
  rw [binLoad, hfibre, (Finset.mem_powersetCard.mp w.1.2).2]

/-- Exact-load witnesses as elements of the corresponding slice. -/
def exactLoadWitnessToEqEvent {q d : ℕ} (i : Fin q) (t : ℕ) :
    ExactLoadWitness (d := d) i t → ↑(binLoadEqEvent (d := d) i t) :=
  fun w ↦ ⟨w.assignment, by
    rw [binLoadEqEvent, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, binLoad_exactLoadWitness_assignment i t w⟩⟩

/-- Every allocation of exact load `t` has a unique exact-load witness. -/
theorem exactLoadWitnessToEqEvent_surjective {q d : ℕ} (i : Fin q)
    (t : ℕ) : Function.Surjective
      (exactLoadWitnessToEqEvent (d := d) i t) := by
  classical
  intro f
  let fibre : Finset (Fin d) :=
    Finset.univ.filter fun x ↦ f.1 x = i
  have hfcard : fibre.card = t := by
    have hf := (Finset.mem_filter.mp f.2).2
    simpa only [binLoad, fibre] using hf
  have hfibreMem : fibre ∈
      (Finset.univ : Finset (Fin d)).powersetCard t := by
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ fibre, hfcard⟩
  let S : ↑((Finset.univ : Finset (Fin d)).powersetCard t) :=
    ⟨fibre, hfibreMem⟩
  let g : ↑(Finset.univ \ fibre) → {j : Fin q // j ≠ i} :=
    fun x ↦ ⟨f.1 x.1, by
      intro hxi
      exact (Finset.mem_sdiff.mp x.2).2 (by
        simp only [fibre, Finset.mem_filter, Finset.mem_univ, true_and, hxi])⟩
  let w : ExactLoadWitness (d := d) i t := ⟨S, g⟩
  refine ⟨w, ?_⟩
  apply Subtype.ext
  funext x
  by_cases hx : x ∈ fibre
  · have hfx : f.1 x = i := by
      simpa only [fibre, Finset.mem_filter, Finset.mem_univ, true_and] using hx
    simp [exactLoadWitnessToEqEvent, ExactLoadWitness.assignment, w, S,
      hx, hfx]
  · simp [exactLoadWitnessToEqEvent, ExactLoadWitness.assignment, w, S,
      g, hx]

/-- Exact-load witnesses are a concrete equivalence with an exact slice of
the allocation space. -/
noncomputable def exactLoadWitnessEquivEqEvent {q d : ℕ}
    (i : Fin q) (t : ℕ) :
    ExactLoadWitness (d := d) i t ≃ ↑(binLoadEqEvent (d := d) i t) :=
  Equiv.ofBijective (exactLoadWitnessToEqEvent (d := d) i t)
    ⟨(fun _ _ h ↦ exactLoadWitness_assignment_injective i t
        (congrArg Subtype.val h)),
      exactLoadWitnessToEqEvent_surjective i t⟩

/-- The generic fibre-cardinality definition agrees with `binLoad` on a
literal finite allocation space. -/
theorem namedBinLoad_fin_eq_binLoad {q d : ℕ}
    (f : Fin d → Fin q) (i : Fin q) :
    namedBinLoad f i = binLoad f i := by
  unfold namedBinLoad binLoad
  rw [Fintype.card_of_subtype
    (Finset.univ.filter fun x : Fin d ↦ f x = i)]
  intro x
  simp

/-- After conditioning on the exact fibre of `i`, the load of another bin
is exactly its named load in the residual codomain `{j // j ≠ i}`. -/
theorem namedBinLoad_exactLoadWitness_residual {q d : ℕ}
    (i j : Fin q) (hij : i ≠ j) (a : ℕ)
    (w : ExactLoadWitness (d := d) i a) :
    namedBinLoad w.2 ⟨j, fun h ↦ hij h.symm⟩ =
      binLoad w.assignment j := by
  classical
  let jb : {k : Fin q // k ≠ i} := ⟨j, fun h ↦ hij h.symm⟩
  let fibreEquiv :
      {y : ↑(Finset.univ \ w.1.1) // w.2 y = jb} ≃
        {x : Fin d // w.assignment x = j} :=
    { toFun := fun y ↦ ⟨y.1.1, by
        have hyNot : y.1.1 ∉ w.1.1 := (Finset.mem_sdiff.mp y.1.2).2
        have hyVal : (w.2 y.1).1 = j := congrArg Subtype.val y.2
        simpa [ExactLoadWitness.assignment, hyNot] using hyVal⟩
      invFun := fun x ↦ by
        have hxNot : x.1 ∉ w.1.1 := by
          intro hx
          have hxi : w.assignment x.1 = i :=
            (exactLoadWitness_assignment_eq_iff_mem w x.1).2 hx
          exact hij (hxi.symm.trans x.2)
        refine ⟨⟨x.1, Finset.mem_sdiff.mpr
          ⟨Finset.mem_univ x.1, hxNot⟩⟩, ?_⟩
        apply Subtype.ext
        have hxVal : (w.2 ⟨x.1, Finset.mem_sdiff.mpr
            ⟨Finset.mem_univ x.1, hxNot⟩⟩).1 = j := by
          simpa [ExactLoadWitness.assignment, hxNot] using x.2
        exact hxVal
      left_inv := fun y ↦ by
        apply Subtype.ext
        apply Subtype.ext
        rfl
      right_inv := fun x ↦ by
        apply Subtype.ext
        rfl }
  calc
    namedBinLoad w.2 ⟨j, fun h ↦ hij h.symm⟩ =
        namedBinLoad w.2 jb := rfl
    _ = namedBinLoad w.assignment j := Fintype.card_congr fibreEquiv
    _ = binLoad w.assignment j := namedBinLoad_fin_eq_binLoad _ _

/-- Conditioning equivalence: an exact first-bin fibre together with a
residual named-bin tail is precisely an exact/upper two-bin slice. -/
noncomputable def exactLoadTailWitnessEquiv {q d : ℕ}
    (i j : Fin q) (hij : i ≠ j) (a t : ℕ) :
    {w : ExactLoadWitness (d := d) i a //
      t ≤ namedBinLoad w.2 ⟨j, fun h ↦ hij h.symm⟩} ≃
      ↑(binLoadEqTailEvent (d := d) i j a t) := by
  classical
  let E := exactLoadWitnessEquivEqEvent (d := d) i a
  let E₁ :
      {w : ExactLoadWitness (d := d) i a //
        t ≤ namedBinLoad w.2 ⟨j, fun h ↦ hij h.symm⟩} ≃
        {f : ↑(binLoadEqEvent (d := d) i a) // t ≤ binLoad f.1 j} :=
    E.subtypeEquiv fun w ↦ by
      change t ≤ namedBinLoad w.2 ⟨j, fun h ↦ hij h.symm⟩ ↔
        t ≤ binLoad w.assignment j
      rw [namedBinLoad_exactLoadWitness_residual i j hij a w]
  let E₂ : {f : ↑(binLoadEqEvent (d := d) i a) //
        t ≤ binLoad f.1 j} ≃
      ↑(binLoadEqTailEvent (d := d) i j a t) :=
    { toFun := fun f ↦ ⟨f.1.1, by
        rw [binLoadEqTailEvent, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_, f.2⟩
        exact (Finset.mem_filter.mp f.1.2).2⟩
      invFun := fun f ↦
        ⟨⟨f.1, by
          rw [binLoadEqEvent, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, (Finset.mem_filter.mp f.2).2.1⟩⟩,
          (Finset.mem_filter.mp f.2).2.2⟩
      left_inv := fun f ↦ by apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := fun f ↦ by apply Subtype.ext; rfl }
  exact E₁.trans E₂

/-- Move the tail predicate inside the sigma type of exact-load witnesses. -/
def exactLoadTailWitnessSigmaEquiv {q d : ℕ}
    (i j : Fin q) (hij : i ≠ j) (a t : ℕ) :
    {w : ExactLoadWitness (d := d) i a //
      t ≤ namedBinLoad w.2 ⟨j, fun h ↦ hij h.symm⟩} ≃
      (Σ S : ↑((Finset.univ : Finset (Fin d)).powersetCard a),
        NamedBinTailType ↑(Finset.univ \ S.1)
          {k : Fin q // k ≠ i} ⟨j, fun h ↦ hij h.symm⟩ t) where
  toFun w := ⟨w.1.1, ⟨w.1.2, w.2⟩⟩
  invFun w := ⟨⟨w.1, w.2.1⟩, w.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Cardinality of the exact-load witness space. -/
theorem card_exactLoadWitness {q d : ℕ} (i : Fin q) (t : ℕ) :
    Fintype.card (ExactLoadWitness (d := d) i t) =
      Nat.choose d t * (q - 1) ^ (d - t) := by
  classical
  change Fintype.card
      (Σ S : ↑((Finset.univ : Finset (Fin d)).powersetCard t),
        (↑(Finset.univ \ S.1) → {j : Fin q // j ≠ i})) = _
  rw [Fintype.card_sigma]
  have hterm (S : ↑((Finset.univ : Finset (Fin d)).powersetCard t)) :
      Fintype.card (↑(Finset.univ \ S.1) → {j : Fin q // j ≠ i}) =
        (q - 1) ^ (d - t) := by
    rw [Fintype.card_fun]
    have hdomain : Fintype.card ↑(Finset.univ \ S.1) = d - t := by
      simp only [Fintype.card_coe]
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ S.1),
        Finset.card_univ, Fintype.card_fin,
        (Finset.mem_powersetCard.mp S.2).2]
    have hcodomain : Fintype.card {j : Fin q // j ≠ i} = q - 1 := by
      rw [Fintype.card_subtype_compl (fun j : Fin q ↦ j = i)]
      simp
    rw [hdomain, hcodomain]
  simp_rw [hterm]
  rw [Finset.sum_const, nsmul_eq_mul]
  simp only [Fintype.card_coe, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_fin]
  rfl

/-- Exact binomial point-mass count for one named bin. -/
theorem card_binLoadEqEvent {q d : ℕ} (i : Fin q) (a : ℕ) :
    (binLoadEqEvent (d := d) i a).card =
      Nat.choose d a * (q - 1) ^ (d - a) := by
  calc
    (binLoadEqEvent (d := d) i a).card =
        Fintype.card ↑(binLoadEqEvent (d := d) i a) := by simp
    _ = Fintype.card (ExactLoadWitness (d := d) i a) :=
      (Fintype.card_congr (exactLoadWitnessEquivEqEvent (d := d) i a)).symm
    _ = Nat.choose d a * (q - 1) ^ (d - a) :=
      card_exactLoadWitness i a

/-- A single-bin tail contains the full point mass at its threshold. -/
theorem choose_mul_pow_le_card_binLoadAtLeastEvent {q d : ℕ}
    (i : Fin q) (t : ℕ) :
    Nat.choose d t * (q - 1) ^ (d - t) ≤
      (binLoadAtLeastEvent (d := d) i t).card := by
  let intoTail : ExactLoadWitness (d := d) i t →
      ↑(binLoadAtLeastEvent (d := d) i t) :=
    fun w ↦ ⟨w.assignment, exactLoadWitness_assignment_mem_tail i t w⟩
  have hinj : Function.Injective intoTail := by
    intro a b hab
    exact exactLoadWitness_assignment_injective i t
      (congrArg Subtype.val hab)
  have hcard := Fintype.card_le_of_injective intoTail hinj
  rw [Fintype.card_coe, card_exactLoadWitness] at hcard
  exact hcard

/-- The old named fibre injects into the same fibre after prepending one
trial. -/
theorem namedBinLoad_le_prependAllocation {B : Type*} [Fintype B]
    [DecidableEq B] {d : ℕ} (b c : B) (f : Fin d → B) :
    namedBinLoad f b ≤ namedBinLoad (prependAllocation c f) b := by
  let lift : {x : Fin d // f x = b} →
      {x : Fin (d + 1) // prependAllocation c f x = b} :=
    fun x ↦ ⟨x.1.succ, by simpa [prependAllocation] using x.2⟩
  exact Fintype.card_le_of_injective lift (by
    intro x y hxy
    apply Subtype.ext
    exact Fin.succ_injective d (congrArg Subtype.val hxy))

/-- Counting form of stochastic monotonicity: every heavy allocation on
`d` trials has `|B|` distinct heavy extensions to `d+1` trials. -/
theorem card_namedBinTailEvent_mul_card_le_succ
    {B : Type*} [Fintype B] [DecidableEq B]
    (b : B) (d t : ℕ) :
    (namedBinTailEvent B b d t).card * Fintype.card B ≤
      (namedBinTailEvent B b (d + 1) t).card := by
  let extend : ↑(namedBinTailEvent B b d t) × B →
      ↑(namedBinTailEvent B b (d + 1) t) := fun z ↦
    ⟨prependAllocation z.2 z.1.1, by
      rw [namedBinTailEvent, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      exact ((Finset.mem_filter.mp z.1.2).2).trans
        (namedBinLoad_le_prependAllocation b z.2 z.1.1)⟩
  have hextend : Function.Injective extend := by
    rintro ⟨f, c⟩ ⟨g, e⟩ h
    have hfun : prependAllocation c f.1 = prependAllocation e g.1 :=
      congrArg Subtype.val h
    have hc : c = e := by
      simpa [prependAllocation] using congrFun hfun 0
    have hfg : f = g := by
      apply Subtype.ext
      funext x
      simpa [prependAllocation] using congrFun hfun x.succ
    exact Prod.ext hfg hc
  have hcard := Fintype.card_le_of_injective extend hextend
  simpa only [Fintype.card_prod, Fintype.card_coe] using hcard

/-- Normalised named-bin upper tails are monotone in the number of trials. -/
theorem namedBinTailFraction_le_succ
    {B : Type*} [Fintype B] [DecidableEq B] [Nonempty B]
    (b : B) (d t : ℕ) :
    namedBinTailFraction B b d t ≤
      namedBinTailFraction B b (d + 1) t := by
  have hBnat : 0 < Fintype.card B := Fintype.card_pos
  have hB : (0 : ℝ) < Fintype.card B := by exact_mod_cast hBnat
  have hcount :
      ((namedBinTailEvent B b d t).card : ℝ) * Fintype.card B ≤
        ((namedBinTailEvent B b (d + 1) t).card : ℝ) := by
    exact_mod_cast card_namedBinTailEvent_mul_card_le_succ b d t
  rw [namedBinTailFraction, namedBinTailFraction]
  apply (div_le_div_iff₀ (pow_pos hB d) (pow_pos hB (d + 1))).2
  rw [pow_succ]
  calc
    ((namedBinTailEvent B b d t).card : ℝ) *
          ((Fintype.card B : ℝ) ^ d * Fintype.card B) =
        (((namedBinTailEvent B b d t).card : ℝ) * Fintype.card B) *
          (Fintype.card B : ℝ) ^ d := by ring
    _ ≤ ((namedBinTailEvent B b (d + 1) t).card : ℝ) *
          (Fintype.card B : ℝ) ^ d :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = ((namedBinTailEvent B b (d + 1) t).card : ℝ) *
          (Fintype.card B : ℝ) ^ d := rfl

/-- Multi-step version of named-bin tail monotonicity. -/
theorem namedBinTailFraction_mono_trials
    {B : Type*} [Fintype B] [DecidableEq B] [Nonempty B]
    (b : B) (t : ℕ) {d₁ d₂ : ℕ} (h : d₁ ≤ d₂) :
    namedBinTailFraction B b d₁ t ≤
      namedBinTailFraction B b d₂ t := by
  induction d₂, h using Nat.le_induction with
  | base => exact le_rfl
  | succ d₂ _ ih => exact ih.trans (namedBinTailFraction_le_succ b d₂ t)

/-- Renaming the finite trial type preserves a named fibre cardinality. -/
theorem namedBinLoad_arrowCongr
    {D E B : Type*} [Fintype D] [Fintype E] [DecidableEq B]
    (e : D ≃ E) (f : D → B) (b : B) :
    namedBinLoad (e.arrowCongr (Equiv.refl B) f) b =
      namedBinLoad f b := by
  let fibreEquiv :
      {y : E // (e.arrowCongr (Equiv.refl B) f) y = b} ≃
        {x : D // f x = b} :=
    { toFun := fun y ↦ ⟨e.symm y.1, by simpa using y.2⟩
      invFun := fun x ↦ ⟨e x.1, by simpa using x.2⟩
      left_inv := fun y ↦ by apply Subtype.ext; simp
      right_inv := fun x ↦ by apply Subtype.ext; simp }
  exact Fintype.card_congr fibreEquiv

/-- The type-valued tail count only depends on the cardinality of the trial
type. -/
theorem card_namedBinTailType_eq_of_equiv
    {D E B : Type*} [Fintype D] [DecidableEq D]
    [Fintype E] [DecidableEq E] [Fintype B]
    [DecidableEq B] (e : D ≃ E) (b : B) (t : ℕ) :
    Fintype.card (NamedBinTailType D B b t) =
      Fintype.card (NamedBinTailType E B b t) := by
  let F : (D → B) ≃ (E → B) := e.arrowCongr (Equiv.refl B)
  let tailEquiv : NamedBinTailType D B b t ≃
      NamedBinTailType E B b t := F.subtypeEquiv fun f ↦ by
    change t ≤ namedBinLoad f b ↔ t ≤ namedBinLoad (F f) b
    rw [namedBinLoad_arrowCongr e f b]
  exact Fintype.card_congr tailEquiv

/-- The finset event and its type-valued counterpart have the same size. -/
theorem card_namedBinTailEvent_eq_type
    {B : Type*} [Fintype B] [DecidableEq B] (b : B) (d t : ℕ) :
    (namedBinTailEvent B b d t).card =
      Fintype.card (NamedBinTailType (Fin d) B b t) := by
  symm
  change Fintype.card {f : Fin d → B // t ≤ namedBinLoad f b} = _
  apply Fintype.card_of_subtype
  intro f
  simp [namedBinTailEvent]

/-- Canonical reduction of an arbitrary finite trial type to `Fin card`. -/
theorem card_namedBinTailType_eq_event
    {D B : Type*} [Fintype D] [DecidableEq D]
    [Fintype B] [DecidableEq B]
    (b : B) (t : ℕ) :
    Fintype.card (NamedBinTailType D B b t) =
      (namedBinTailEvent B b (Fintype.card D) t).card := by
  rw [card_namedBinTailType_eq_of_equiv (Fintype.equivFin D),
    card_namedBinTailEvent_eq_type]

/-- Exact conditional-slice count.  Given load `a` in bin `i`, the other
bin is a named bin among the `q-1` residual colours on `d-a` trials. -/
theorem card_binLoadEqTailEvent {q d : ℕ}
    (i j : Fin q) (hij : i ≠ j) (a t : ℕ) :
    (binLoadEqTailEvent (d := d) i j a t).card =
      Nat.choose d a *
        (namedBinTailEvent {k : Fin q // k ≠ i}
          ⟨j, fun h ↦ hij h.symm⟩ (d - a) t).card := by
  classical
  let B := {k : Fin q // k ≠ i}
  let jb : B := ⟨j, fun h ↦ hij h.symm⟩
  let P : Finset (Finset (Fin d)) :=
    (Finset.univ : Finset (Fin d)).powersetCard a
  calc
    (binLoadEqTailEvent (d := d) i j a t).card =
        Fintype.card ↑(binLoadEqTailEvent (d := d) i j a t) := by simp
    _ = Fintype.card
        {w : ExactLoadWitness (d := d) i a //
          t ≤ namedBinLoad w.2 ⟨j, fun h ↦ hij h.symm⟩} :=
      (Fintype.card_congr (exactLoadTailWitnessEquiv
        (d := d) i j hij a t)).symm
    _ = Fintype.card
        (Σ S : ↑P, NamedBinTailType ↑(Finset.univ \ S.1)
          B jb t) :=
      Fintype.card_congr
        (exactLoadTailWitnessSigmaEquiv (d := d) i j hij a t)
    _ = ∑ S : ↑P, Fintype.card
        (NamedBinTailType ↑(Finset.univ \ S.1) B jb t) :=
      Fintype.card_sigma
    _ = ∑ _S : ↑P,
        (namedBinTailEvent B jb (d - a) t).card := by
      apply Finset.sum_congr rfl
      intro S _hS
      have hD : Fintype.card ↑(Finset.univ \ S.1) = d - a := by
        simp only [Fintype.card_coe]
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ S.1),
          Finset.card_univ, Fintype.card_fin,
          (Finset.mem_powersetCard.mp S.2).2]
      rw [card_namedBinTailType_eq_event, hD]
    _ = Nat.choose d a *
        (namedBinTailEvent B jb (d - a) t).card := by
      rw [Finset.sum_const, nsmul_eq_mul]
      simp only [P, Fintype.card_coe, Finset.card_powersetCard,
        Finset.card_univ, Fintype.card_fin]
      rfl
    _ = Nat.choose d a *
        (namedBinTailEvent {k : Fin q // k ≠ i}
          ⟨j, fun h ↦ hij h.symm⟩ (d - a) t).card := rfl

/-- A named load cannot exceed the number of balls. -/
theorem binLoad_le_numberOfBalls {q d : ℕ}
    (f : Fin d → Fin q) (i : Fin q) : binLoad f i ≤ d := by
  unfold binLoad
  calc
    #{x ∈ (Finset.univ : Finset (Fin d)) | f x = i} ≤
        (Finset.univ : Finset (Fin d)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = d := by simp

/-- Partition a one-bin upper tail by its exact load. -/
theorem card_binLoadAtLeastEvent_eq_sum_eqSlices {q d t : ℕ}
    (i : Fin q) :
    (binLoadAtLeastEvent (d := d) i t).card =
      ∑ a ∈ Finset.Icc t d, (binLoadEqEvent (d := d) i a).card := by
  classical
  have hmaps :
      ((binLoadAtLeastEvent (d := d) i t : Finset (Fin d → Fin q)) :
          Set (Fin d → Fin q)).MapsTo (fun f ↦ binLoad f i)
        (Finset.Icc t d : Finset ℕ) := by
    intro f hf
    rw [Finset.mem_coe, Finset.mem_Icc]
    exact ⟨(Finset.mem_filter.mp hf).2, binLoad_le_numberOfBalls f i⟩
  calc
    (binLoadAtLeastEvent (d := d) i t).card =
        ∑ a ∈ Finset.Icc t d,
          #{f ∈ binLoadAtLeastEvent (d := d) i t | binLoad f i = a} :=
      Finset.card_eq_sum_card_fiberwise hmaps
    _ = ∑ a ∈ Finset.Icc t d,
        (binLoadEqEvent (d := d) i a).card := by
      apply Finset.sum_congr rfl
      intro a ha
      congr 1
      ext f
      have hta : t ≤ a := (Finset.mem_Icc.mp ha).1
      simp only [binLoadAtLeastEvent, binLoadEqEvent, Finset.mem_filter,
        Finset.mem_univ, true_and]
      omega

/-- Partition a joint upper tail by the exact load of its first bin. -/
theorem card_twoBinLoadAtLeastEvent_eq_sum_eqTailSlices
    {q d t : ℕ} (i j : Fin q) :
    (twoBinLoadAtLeastEvent (d := d) i j t).card =
      ∑ a ∈ Finset.Icc t d,
        (binLoadEqTailEvent (d := d) i j a t).card := by
  classical
  have hmaps :
      ((twoBinLoadAtLeastEvent (d := d) i j t :
          Finset (Fin d → Fin q)) : Set (Fin d → Fin q)).MapsTo
        (fun f ↦ binLoad f i) (Finset.Icc t d : Finset ℕ) := by
    intro f hf
    rw [Finset.mem_coe, Finset.mem_Icc]
    exact ⟨(Finset.mem_filter.mp hf).2.1,
      binLoad_le_numberOfBalls f i⟩
  calc
    (twoBinLoadAtLeastEvent (d := d) i j t).card =
        ∑ a ∈ Finset.Icc t d,
          #{f ∈ twoBinLoadAtLeastEvent (d := d) i j t |
            binLoad f i = a} :=
      Finset.card_eq_sum_card_fiberwise hmaps
    _ = ∑ a ∈ Finset.Icc t d,
        (binLoadEqTailEvent (d := d) i j a t).card := by
      apply Finset.sum_congr rfl
      intro a ha
      congr 1
      ext f
      have hta : t ≤ a := (Finset.mem_Icc.mp ha).1
      simp only [twoBinLoadAtLeastEvent, binLoadEqTailEvent,
        Finset.mem_filter, Finset.mem_univ, true_and]
      omega

/-- Partition the second-bin tail by every possible exact load of the first
bin. -/
theorem card_binLoadAtLeastEvent_eq_sum_eqTailSlices
    {q d t : ℕ} (i j : Fin q) :
    (binLoadAtLeastEvent (d := d) j t).card =
      ∑ a ∈ Finset.range (d + 1),
        (binLoadEqTailEvent (d := d) i j a t).card := by
  classical
  have hmaps :
      ((binLoadAtLeastEvent (d := d) j t : Finset (Fin d → Fin q)) :
          Set (Fin d → Fin q)).MapsTo (fun f ↦ binLoad f i)
        (Finset.range (d + 1) : Finset ℕ) := by
    intro f _hf
    rw [Finset.mem_coe, Finset.mem_range]
    change binLoad f i < d + 1
    have hle := binLoad_le_numberOfBalls f i
    omega
  calc
    (binLoadAtLeastEvent (d := d) j t).card =
        ∑ a ∈ Finset.range (d + 1),
          #{f ∈ binLoadAtLeastEvent (d := d) j t | binLoad f i = a} :=
      Finset.card_eq_sum_card_fiberwise hmaps
    _ = ∑ a ∈ Finset.range (d + 1),
        (binLoadEqTailEvent (d := d) i j a t).card := by
      apply Finset.sum_congr rfl
      intro a _ha
      congr 1
      ext f
      simp only [binLoadAtLeastEvent, binLoadEqTailEvent,
        Finset.mem_filter, Finset.mem_univ, true_and]
      tauto

/-- The exact-load slices partition the whole allocation space. -/
theorem sum_card_binLoadEqEvent {q d : ℕ} (i : Fin q) :
    ∑ a ∈ Finset.range (d + 1),
      (binLoadEqEvent (d := d) i a).card = q ^ d := by
  classical
  have hmaps :
      ((Finset.univ : Finset (Fin d → Fin q)) :
          Set (Fin d → Fin q)).MapsTo (fun f ↦ binLoad f i)
        (Finset.range (d + 1) : Finset ℕ) := by
    intro f _hf
    rw [Finset.mem_coe, Finset.mem_range]
    change binLoad f i < d + 1
    have hle := binLoad_le_numberOfBalls f i
    omega
  have hpartition := Finset.card_eq_sum_card_fiberwise hmaps
  calc
    ∑ a ∈ Finset.range (d + 1),
        (binLoadEqEvent (d := d) i a).card =
        ∑ a ∈ Finset.range (d + 1),
          #{f ∈ (Finset.univ : Finset (Fin d → Fin q)) |
            binLoad f i = a} := by
      apply Finset.sum_congr rfl
      intro a _ha
      rfl
    _ = (Finset.univ : Finset (Fin d → Fin q)).card := hpartition.symm
    _ = q ^ d := by simp

@[simp]
theorem card_otherBins {q : ℕ} (i : Fin q) :
    Fintype.card {k : Fin q // k ≠ i} = q - 1 := by
  rw [Fintype.card_subtype_compl (fun k : Fin q ↦ k = i)]
  simp

/-- Cast form of the exact-load weight. -/
theorem cast_card_binLoadEqEvent {q d : ℕ} (i : Fin q) (a : ℕ) :
    ((binLoadEqEvent (d := d) i a).card : ℝ) =
      (Nat.choose d a : ℝ) * ((q - 1 : ℕ) : ℝ) ^ (d - a) := by
  rw [card_binLoadEqEvent]
  norm_cast

/-- Multiplying a slice weight by its conditional residual tail fraction
recovers the exact/tail slice count. -/
theorem sliceWeight_mul_namedTailFraction {q d : ℕ}
    (i j : Fin q) (hij : i ≠ j) (a t : ℕ) :
    (Nat.choose d a : ℝ) * ((q - 1 : ℕ) : ℝ) ^ (d - a) *
        namedBinTailFraction {k : Fin q // k ≠ i}
          ⟨j, fun h ↦ hij h.symm⟩ (d - a) t =
      ((binLoadEqTailEvent (d := d) i j a t).card : ℝ) := by
  letI : Nonempty {k : Fin q // k ≠ i} :=
    ⟨⟨j, fun h ↦ hij h.symm⟩⟩
  have hBpow : (0 : ℝ) <
      (Fintype.card {k : Fin q // k ≠ i} : ℝ) ^ (d - a) := by
    positivity
  rw [card_binLoadEqTailEvent i j hij a t]
  rw [namedBinTailFraction]
  simp only [Nat.cast_mul]
  rw [← card_otherBins i]
  field_simp [ne_of_gt hBpow]

/-- Finite weighted antitone covariance, in the exact upper-set form needed
for conditioning.  If every value on `U` is at most every value on `L`,
then conditioning the weight distribution on `U` cannot increase the
average of `g`.  The division-free statement also covers zero total
weight. -/
theorem weighted_upper_average_le_of_cross_antitone
    {α : Type*} [DecidableEq α]
    (U L : Finset α) (w g : α → ℝ) (hUL : Disjoint U L)
    (hw : ∀ x ∈ U ∪ L, 0 ≤ w x)
    (hcross : ∀ u ∈ U, ∀ l ∈ L, g u ≤ g l) :
    (∑ u ∈ U, w u * g u) * (∑ x ∈ U ∪ L, w x) ≤
      (∑ u ∈ U, w u) * (∑ x ∈ U ∪ L, w x * g x) := by
  have hpair :
      (∑ u ∈ U, w u * g u) * (∑ l ∈ L, w l) ≤
        (∑ u ∈ U, w u) * (∑ l ∈ L, w l * g l) := by
    calc
      (∑ u ∈ U, w u * g u) * (∑ l ∈ L, w l) =
          ∑ u ∈ U, ∑ l ∈ L, (w u * g u) * w l := by
        simp_rw [Finset.sum_mul, Finset.mul_sum]
      _ ≤ ∑ u ∈ U, ∑ l ∈ L, w u * (w l * g l) := by
        apply Finset.sum_le_sum
        intro u hu
        apply Finset.sum_le_sum
        intro l hl
        have hwu : 0 ≤ w u := hw u (Finset.mem_union_left L hu)
        have hwl : 0 ≤ w l := hw l (Finset.mem_union_right U hl)
        calc
          (w u * g u) * w l = w u * (w l * g u) := by ring
          _ ≤ w u * (w l * g l) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (hcross u hu l hl) hwl) hwu
      _ = (∑ u ∈ U, w u) * (∑ l ∈ L, w l * g l) := by
        simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_union hUL, Finset.sum_union hUL]
  nlinarith

/-- Two distinct multinomial occupancy upper tails are negatively
correlated.  This finite counting theorem is stronger than Claim A.6 in
the paper (constant `1` instead of its exponential loss). -/
theorem twoBinLoadAtLeastEvent_negative_correlation
    {q d t : ℕ} (i j : Fin q) (hij : i ≠ j) (htd : t ≤ d) :
    ((twoBinLoadAtLeastEvent (d := d) i j t).card : ℝ) *
        ((q ^ d : ℕ) : ℝ) ≤
      ((binLoadAtLeastEvent (d := d) i t).card : ℝ) *
        ((binLoadAtLeastEvent (d := d) j t).card : ℝ) := by
  classical
  let B := {k : Fin q // k ≠ i}
  let jb : B := ⟨j, fun h ↦ hij h.symm⟩
  letI : Nonempty B := ⟨jb⟩
  let U : Finset ℕ := Finset.Icc t d
  let L : Finset ℕ := Finset.range t
  let w : ℕ → ℝ := fun a ↦
    (Nat.choose d a : ℝ) * (Fintype.card B : ℝ) ^ (d - a)
  let g : ℕ → ℝ := fun a ↦
    namedBinTailFraction B jb (d - a) t
  have hBcard : Fintype.card B = q - 1 := card_otherBins i
  have hUL : Disjoint U L := by
    rw [Finset.disjoint_left]
    intro a haU haL
    have hut := (Finset.mem_Icc.mp haU).1
    have hlt := Finset.mem_range.mp haL
    omega
  have hUnion : U ∪ L = Finset.range (d + 1) := by
    ext a
    simp only [U, L, Finset.mem_union, Finset.mem_Icc,
      Finset.mem_range]
    omega
  have hw_nonneg : ∀ a ∈ U ∪ L, 0 ≤ w a := by
    intro a _ha
    dsimp only [w]
    positivity
  have hg_cross : ∀ u ∈ U, ∀ l ∈ L, g u ≤ g l := by
    intro u hu l hl
    have hlu : l ≤ u := by
      have hut := (Finset.mem_Icc.mp hu).1
      have hlt := Finset.mem_range.mp hl
      omega
    have htrials : d - u ≤ d - l := Nat.sub_le_sub_left hlu d
    exact namedBinTailFraction_mono_trials jb t htrials
  have hw_eq (a : ℕ) :
      w a = ((binLoadEqEvent (d := d) i a).card : ℝ) := by
    dsimp only [w]
    rw [hBcard]
    exact (cast_card_binLoadEqEvent i a).symm
  have hwg_eq (a : ℕ) :
      w a * g a =
        ((binLoadEqTailEvent (d := d) i j a t).card : ℝ) := by
    dsimp only [w, g]
    rw [hBcard]
    exact sliceWeight_mul_namedTailFraction i j hij a t
  have hsumUwg :
      (∑ a ∈ U, w a * g a) =
        ((twoBinLoadAtLeastEvent (d := d) i j t).card : ℝ) := by
    calc
      (∑ a ∈ U, w a * g a) =
          ∑ a ∈ U,
            ((binLoadEqTailEvent (d := d) i j a t).card : ℝ) := by
        apply Finset.sum_congr rfl
        intro a _ha
        exact hwg_eq a
      _ = ((twoBinLoadAtLeastEvent (d := d) i j t).card : ℝ) := by
        exact_mod_cast
          (card_twoBinLoadAtLeastEvent_eq_sum_eqTailSlices i j).symm
  have hsumUw :
      (∑ a ∈ U, w a) =
        ((binLoadAtLeastEvent (d := d) i t).card : ℝ) := by
    calc
      (∑ a ∈ U, w a) =
          ∑ a ∈ U, ((binLoadEqEvent (d := d) i a).card : ℝ) := by
        apply Finset.sum_congr rfl
        intro a _ha
        exact hw_eq a
      _ = ((binLoadAtLeastEvent (d := d) i t).card : ℝ) := by
        exact_mod_cast (card_binLoadAtLeastEvent_eq_sum_eqSlices i).symm
  have hsumAllw :
      (∑ a ∈ Finset.range (d + 1), w a) = ((q ^ d : ℕ) : ℝ) := by
    calc
      (∑ a ∈ Finset.range (d + 1), w a) =
          ∑ a ∈ Finset.range (d + 1),
            ((binLoadEqEvent (d := d) i a).card : ℝ) := by
        apply Finset.sum_congr rfl
        intro a _ha
        exact hw_eq a
      _ = ((q ^ d : ℕ) : ℝ) := by
        exact_mod_cast sum_card_binLoadEqEvent i
  have hsumAllwg :
      (∑ a ∈ Finset.range (d + 1), w a * g a) =
        ((binLoadAtLeastEvent (d := d) j t).card : ℝ) := by
    calc
      (∑ a ∈ Finset.range (d + 1), w a * g a) =
          ∑ a ∈ Finset.range (d + 1),
            ((binLoadEqTailEvent (d := d) i j a t).card : ℝ) := by
        apply Finset.sum_congr rfl
        intro a _ha
        exact hwg_eq a
      _ = ((binLoadAtLeastEvent (d := d) j t).card : ℝ) := by
        exact_mod_cast
          (card_binLoadAtLeastEvent_eq_sum_eqTailSlices i j).symm
  have hcov := weighted_upper_average_le_of_cross_antitone
    U L w g hUL hw_nonneg hg_cross
  rw [hUnion, hsumUwg, hsumUw, hsumAllw, hsumAllwg] at hcov
  exact hcov

/-- Probability form of negative correlation. -/
theorem twoBinLoadAtLeastEvent_card_le_mul_div
    {q d t : ℕ} (i j : Fin q) (hij : i ≠ j) (htd : t ≤ d) :
    ((twoBinLoadAtLeastEvent (d := d) i j t).card : ℝ) ≤
      ((binLoadAtLeastEvent (d := d) i t).card : ℝ) *
          ((binLoadAtLeastEvent (d := d) j t).card : ℝ) /
        Fintype.card (Fin d → Fin q) := by
  have hq : 0 < q := lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hN : (0 : ℝ) < Fintype.card (Fin d → Fin q) := by
    have : Nonempty (Fin d → Fin q) := ⟨fun _ ↦ i⟩
    exact_mod_cast Fintype.card_pos
  apply (le_div_iff₀ hN).2
  have hneg := twoBinLoadAtLeastEvent_negative_correlation i j hij htd
  simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] using hneg

/-- Fixed-reference-bin form consumed by the second-moment API. -/
theorem twoBinLoadAtLeastEvent_card_le_fixed_sq_div
    {q d t : ℕ} (i₀ i j : Fin q) (hij : i ≠ j) (htd : t ≤ d) :
    ((twoBinLoadAtLeastEvent (d := d) i j t).card : ℝ) ≤
      ((binLoadAtLeastEvent (d := d) i₀ t).card : ℝ) ^ 2 /
        Fintype.card (Fin d → Fin q) := by
  have h := twoBinLoadAtLeastEvent_card_le_mul_div i j hij htd
  have hi : ((binLoadAtLeastEvent (d := d) i t).card : ℝ) =
      ((binLoadAtLeastEvent (d := d) i₀ t).card : ℝ) := by
    exact_mod_cast card_binLoadAtLeastEvent_eq i i₀
  have hj : ((binLoadAtLeastEvent (d := d) j t).card : ℝ) =
      ((binLoadAtLeastEvent (d := d) i₀ t).card : ℝ) := by
    exact_mod_cast card_binLoadAtLeastEvent_eq j i₀
  rw [hi, hj] at h
  simpa only [pow_two] using h

/-- A load of at least `t` supplies a `t`-set of balls all forced into the
same bin. -/
theorem binLoadAtLeastEvent_subset_biUnion_fixedBinEvent
    {q d : ℕ} (i : Fin q) (t : ℕ) :
    binLoadAtLeastEvent (d := d) i t ⊆
      ((Finset.univ : Finset (Fin d)).powersetCard t).biUnion
        (fun S ↦ fixedBinEvent i S) := by
  classical
  intro f hf
  have hload : t ≤ binLoad f i :=
    (Finset.mem_filter.mp hf).2
  let fibre : Finset (Fin d) :=
    Finset.univ.filter fun x ↦ f x = i
  obtain ⟨S, hSfibre, hScard⟩ :=
    Finset.exists_subset_card_eq (s := fibre) hload
  rw [Finset.mem_biUnion]
  refine ⟨S, ?_, ?_⟩
  · rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ S, hScard⟩
  · rw [fixedBinEvent, Finset.mem_filter]
    refine ⟨Finset.mem_univ f, ?_⟩
    intro x hxS
    have hxFibre := hSfibre hxS
    simpa only [fibre, Finset.mem_filter, Finset.mem_univ, true_and]
      using hxFibre

/-- A simultaneous load of at least `t` in two distinct bins supplies two
disjoint `t`-sets of forced balls. -/
theorem twoBinLoadAtLeastEvent_subset_biUnion_fixedTwoBinEvent
    {q d : ℕ} (i j : Fin q) (hij : i ≠ j) (t : ℕ) :
    twoBinLoadAtLeastEvent (d := d) i j t ⊆
      ((Finset.univ : Finset (Fin d)).powersetCard t).biUnion
        (fun S ↦ ((Finset.univ \ S).powersetCard t).biUnion
          (fun T ↦ fixedTwoBinEvent i j S T)) := by
  classical
  intro f hf
  have hloads := (Finset.mem_filter.mp hf).2
  let fibreI : Finset (Fin d) :=
    Finset.univ.filter fun x ↦ f x = i
  let fibreJ : Finset (Fin d) :=
    Finset.univ.filter fun x ↦ f x = j
  obtain ⟨S, hSI, hScard⟩ :=
    Finset.exists_subset_card_eq (s := fibreI) hloads.1
  obtain ⟨T, hTJ, hTcard⟩ :=
    Finset.exists_subset_card_eq (s := fibreJ) hloads.2
  have hFibres : Disjoint fibreI fibreJ := by
    rw [Finset.disjoint_left]
    intro x hxI hxJ
    have hxi : f x = i := by
      simpa only [fibreI, Finset.mem_filter, Finset.mem_univ, true_and]
        using hxI
    have hxj : f x = j := by
      simpa only [fibreJ, Finset.mem_filter, Finset.mem_univ, true_and]
        using hxJ
    exact hij (hxi.symm.trans hxj)
  have hST : Disjoint S T := hFibres.mono hSI hTJ
  rw [Finset.mem_biUnion]
  refine ⟨S, ?_, ?_⟩
  · rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ S, hScard⟩
  · rw [Finset.mem_biUnion]
    refine ⟨T, ?_, ?_⟩
    · rw [Finset.mem_powersetCard]
      refine ⟨?_, hTcard⟩
      intro x hxT
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x,
        fun hxS ↦ Finset.disjoint_left.mp hST hxS hxT⟩
    · rw [fixedTwoBinEvent, Finset.mem_filter]
      refine ⟨Finset.mem_univ f, ?_, ?_⟩
      · intro x hxS
        have hxI := hSI hxS
        simpa only [fibreI, Finset.mem_filter, Finset.mem_univ, true_and]
          using hxI
      · intro x hxT
        have hxJ := hTJ hxT
        simpa only [fibreJ, Finset.mem_filter, Finset.mem_univ, true_and]
          using hxJ

/-- A simultaneous upper tail in two distinct bins is bounded by choosing
the `t` witnesses for the first bin, then `t` disjoint witnesses for the
second bin, and finally assigning every remaining ball arbitrarily. -/
theorem card_twoBinLoadAtLeastEvent_le {q d : ℕ} (i j : Fin q)
    (hij : i ≠ j) (t : ℕ) :
    (twoBinLoadAtLeastEvent (d := d) i j t).card ≤
      Nat.choose d t * Nat.choose (d - t) t * q ^ (d - (t + t)) := by
  classical
  let P : Finset (Finset (Fin d)) :=
    (Finset.univ : Finset (Fin d)).powersetCard t
  calc
    (twoBinLoadAtLeastEvent (d := d) i j t).card ≤
        (P.biUnion fun S ↦ ((Finset.univ \ S).powersetCard t).biUnion
          fun T ↦ fixedTwoBinEvent i j S T).card :=
      Finset.card_le_card
        (twoBinLoadAtLeastEvent_subset_biUnion_fixedTwoBinEvent i j hij t)
    _ ≤ ∑ S ∈ P, (((Finset.univ \ S).powersetCard t).biUnion
          fun T ↦ fixedTwoBinEvent i j S T).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ S ∈ P, ∑ T ∈ (Finset.univ \ S).powersetCard t,
          (fixedTwoBinEvent i j S T).card := by
      apply Finset.sum_le_sum
      intro S hS
      exact Finset.card_biUnion_le
    _ ≤ ∑ S ∈ P, ∑ _T ∈ (Finset.univ \ S).powersetCard t,
          q ^ (d - (t + t)) := by
      apply Finset.sum_le_sum
      intro S hS
      have hScard : S.card = t :=
        (Finset.mem_powersetCard.mp hS).2
      apply Finset.sum_le_sum
      intro T hT
      have hTdata := Finset.mem_powersetCard.mp hT
      have hTcard : T.card = t := hTdata.2
      have hST : Disjoint S T := by
        rw [Finset.disjoint_left]
        intro x hxS hxT
        exact (Finset.mem_sdiff.mp (hTdata.1 hxT)).2 hxS
      simpa only [hScard, hTcard] using
        card_fixedTwoBinEvent_le i j S T hST
    _ = Nat.choose d t * Nat.choose (d - t) t *
          q ^ (d - (t + t)) := by
      have hPcard : P.card = Nat.choose d t := by
        simp only [P, Finset.card_powersetCard, Finset.card_univ,
          Fintype.card_fin]
      have hbaseCard (S : Finset (Fin d)) (hS : S ∈ P) :
          (Finset.univ \ S).card = d - t := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ S),
          Finset.card_univ, Fintype.card_fin]
        rw [(Finset.mem_powersetCard.mp hS).2]
      rw [Finset.sum_congr rfl (fun S hS ↦ by
        rw [Finset.sum_const, Finset.card_powersetCard, hbaseCard S hS,
          nsmul_eq_mul])]
      rw [Finset.sum_const, hPcard, nsmul_eq_mul]
      ac_rfl

/-- Elementary binomial upper-tail count.  It is the counting core of a
Chernoff bound and avoids introducing a measure-theory model for the finite
allocation space. -/
theorem card_binLoadAtLeastEvent_le {q d : ℕ} (i : Fin q) (t : ℕ) :
    (binLoadAtLeastEvent (d := d) i t).card ≤
      Nat.choose d t * q ^ (d - t) := by
  classical
  calc
    (binLoadAtLeastEvent (d := d) i t).card ≤
        (((Finset.univ : Finset (Fin d)).powersetCard t).biUnion
          (fun S ↦ fixedBinEvent i S)).card :=
      Finset.card_le_card
        (binLoadAtLeastEvent_subset_biUnion_fixedBinEvent i t)
    _ ≤ ∑ S ∈ (Finset.univ : Finset (Fin d)).powersetCard t,
        (fixedBinEvent i S).card := Finset.card_biUnion_le
    _ ≤ ∑ _S ∈ (Finset.univ : Finset (Fin d)).powersetCard t,
        q ^ (d - t) := by
      apply Finset.sum_le_sum
      intro S hS
      have hScard : S.card = t :=
        (Finset.mem_powersetCard.mp hS).2
      simpa only [hScard] using card_fixedBinEvent_le i S
    _ = Nat.choose d t * q ^ (d - t) := by
      rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      norm_cast

/-- A convenient consequence of Stirling's lower bound. -/
theorem pow_div_exp_le_factorial {t : ℕ} (ht : 0 < t) :
    ((t : ℝ) / Real.exp 1) ^ t ≤ (t.factorial : ℝ) := by
  have htReal : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hradicand : (1 : ℝ) ≤ 2 * Real.pi * t := by
    calc
      (1 : ℝ) ≤ 2 * 3 * 1 := by norm_num
      _ ≤ 2 * Real.pi * t := by
        gcongr
        exact Real.pi_gt_three.le
  have hsqrt : (1 : ℝ) ≤ √(2 * Real.pi * t) :=
    Real.one_le_sqrt.mpr hradicand
  calc
    ((t : ℝ) / Real.exp 1) ^ t =
        1 * ((t : ℝ) / Real.exp 1) ^ t := by ring
    _ ≤ √(2 * Real.pi * t) * ((t : ℝ) / Real.exp 1) ^ t :=
      mul_le_mul_of_nonneg_right hsqrt (by positivity)
    _ ≤ (t.factorial : ℝ) := Stirling.le_factorial_stirling t

/-- Standard binomial-coefficient estimate
`choose d t ≤ (e d / t)^t`, derived entirely from mathlib's Stirling
bound. -/
theorem choose_le_exp_mul_div_pow (d : ℕ) {t : ℕ} (ht : 0 < t) :
    (Nat.choose d t : ℝ) ≤
      (Real.exp 1 * d / t) ^ t := by
  calc
    (Nat.choose d t : ℝ) ≤ (d : ℝ) ^ t / (t.factorial : ℝ) :=
      Nat.choose_le_pow_div t d
    _ ≤ (d : ℝ) ^ t / (((t : ℝ) / Real.exp 1) ^ t) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_div_exp_le_factorial ht)
    _ = (Real.exp 1 * d / t) ^ t := by
      have htne : (t : ℝ) ≠ 0 := by positivity
      simp only [div_pow]
      field_simp
      ring

/-- Uniform one-bin upper-tail estimate obtained by dividing the counting
bound by the size `q^d` of the allocation space. -/
theorem uniform_binLoad_tail_le {q d t : ℕ} (i : Fin q)
    (hq : 0 < q) (ht : 0 < t) (htd : t ≤ d) :
    ((binLoadAtLeastEvent (d := d) i t).card : ℝ) /
        Fintype.card (Fin d → Fin q) ≤
      (Real.exp 1 * d / (q * t)) ^ t := by
  have hcount :
      ((binLoadAtLeastEvent (d := d) i t).card : ℝ) ≤
        (Nat.choose d t : ℝ) * (q : ℝ) ^ (d - t) := by
    exact_mod_cast card_binLoadAtLeastEvent_le i t
  have hqReal : (0 : ℝ) < q := by exact_mod_cast hq
  have hden : (0 : ℝ) < (q : ℝ) ^ d := pow_pos hqReal d
  have hchoose := choose_le_exp_mul_div_pow d ht
  have hpow :
      (q : ℝ) ^ d = (q : ℝ) ^ (d - t) * (q : ℝ) ^ t := by
    rw [← pow_add, Nat.sub_add_cancel htd]
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, Nat.cast_pow]
  calc
    ((binLoadAtLeastEvent (d := d) i t).card : ℝ) / (q : ℝ) ^ d ≤
        ((Nat.choose d t : ℝ) * (q : ℝ) ^ (d - t)) /
          (q : ℝ) ^ d :=
      div_le_div_of_nonneg_right hcount hden.le
    _ ≤ (((Real.exp 1 * d / t) ^ t) * (q : ℝ) ^ (d - t)) /
          (q : ℝ) ^ d := by
      apply div_le_div_of_nonneg_right _ hden.le
      exact mul_le_mul_of_nonneg_right hchoose (by positivity)
    _ = (Real.exp 1 * d / (q * t)) ^ t := by
      rw [hpow]
      simp only [div_pow]
      field_simp
      ring

theorem maxBinLoadAtLeastEvent_subset_biUnion {q d t : ℕ} (hq : 0 < q) :
    maxBinLoadAtLeastEvent q d t ⊆
      (Finset.univ : Finset (Fin q)).biUnion
        (fun i ↦ binLoadAtLeastEvent (d := d) i t) := by
  intro f hf
  have hmax : t ≤ maxBinLoad f := (Finset.mem_filter.mp hf).2
  obtain ⟨i, _hi, hiload⟩ := Finset.exists_mem_eq_sup
    (s := (Finset.univ : Finset (Fin q)))
    (Finset.univ_nonempty_iff.mpr ⟨0, hq⟩) (binLoad f)
  rw [Finset.mem_biUnion]
  refine ⟨i, Finset.mem_univ i, ?_⟩
  rw [binLoadAtLeastEvent, Finset.mem_filter]
  refine ⟨Finset.mem_univ f, ?_⟩
  calc
    t ≤ maxBinLoad f := hmax
    _ = binLoad f i := hiload

/-- Union-bound version controlling the maximum load. -/
theorem uniform_maxBinLoad_tail_le {q d t : ℕ}
    (hq : 0 < q) (ht : 0 < t) (htd : t ≤ d) :
    ((maxBinLoadAtLeastEvent q d t).card : ℝ) /
        Fintype.card (Fin d → Fin q) ≤
      q * (Real.exp 1 * d / (q * t)) ^ t := by
  let Bad : Fin q → Finset (Fin d → Fin q) :=
    fun i ↦ binLoadAtLeastEvent (d := d) i t
  have hcardPos : (0 : ℝ) ≤ Fintype.card (Fin d → Fin q) := by
    positivity
  have hsubset := maxBinLoadAtLeastEvent_subset_biUnion (d := d) (t := t) hq
  have hcardSubset :
      ((maxBinLoadAtLeastEvent q d t).card : ℝ) ≤
        (((Finset.univ : Finset (Fin q)).biUnion Bad).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsubset
  calc
    ((maxBinLoadAtLeastEvent q d t).card : ℝ) /
        Fintype.card (Fin d → Fin q) ≤
      (((Finset.univ : Finset (Fin q)).biUnion Bad).card : ℝ) /
        Fintype.card (Fin d → Fin q) :=
      div_le_div_of_nonneg_right hcardSubset hcardPos
    _ ≤ (∑ i : Fin q, ((Bad i).card : ℝ)) /
        Fintype.card (Fin d → Fin q) := by
      apply div_le_div_of_nonneg_right _ hcardPos
      exact_mod_cast (Finset.card_biUnion_le :
        ((Finset.univ : Finset (Fin q)).biUnion Bad).card ≤
          ∑ i, (Bad i).card)
    _ = ∑ i : Fin q,
        ((Bad i).card : ℝ) / Fintype.card (Fin d → Fin q) := by
      rw [Finset.sum_div]
    _ ≤ ∑ _i : Fin q, (Real.exp 1 * d / (q * t)) ^ t := by
      apply Finset.sum_le_sum
      intro i _
      exact uniform_binLoad_tail_le i hq ht htd
    _ = q * (Real.exp 1 * d / (q * t)) ^ t := by simp

/-- Deleting one ball decreases the load of any fixed bin by at most one. -/
theorem binLoad_le_deleteBall_add_one {q d : ℕ}
    (f : Fin (d + 1) → Fin q) (j : Fin (d + 1)) (i : Fin q) :
    binLoad f i ≤ binLoad (deleteBall f j) i + 1 := by
  classical
  let S : Finset (Fin (d + 1)) :=
    Finset.univ.filter fun x ↦ f x = i
  let T : Finset (Fin d) :=
    Finset.univ.filter fun x ↦ deleteBall f j x = i
  let pull : ↑(S.erase j) → ↑T := fun x ↦
    ⟨Classical.choose (Fin.exists_succAbove_eq
        (Finset.ne_of_mem_erase x.2)), by
      have hxS : f x.1 = i := (Finset.mem_filter.mp
        (Finset.mem_of_mem_erase x.2)).2
      have hx := Classical.choose_spec (Fin.exists_succAbove_eq
        (Finset.ne_of_mem_erase x.2))
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and,
        deleteBall, hx, hxS]⟩
  have hpull : Function.Injective pull := by
    intro x y hxy
    apply Subtype.ext
    have hval := congrArg (fun z : ↑T ↦ j.succAbove z.1) hxy
    have hx := Classical.choose_spec (Fin.exists_succAbove_eq
      (Finset.ne_of_mem_erase x.2))
    have hy := Classical.choose_spec (Fin.exists_succAbove_eq
      (Finset.ne_of_mem_erase y.2))
    simpa only [pull, hx, hy] using hval
  have herase : (S.erase j).card ≤ T.card := by
    simpa only [Fintype.card_coe] using
      Fintype.card_le_of_injective pull hpull
  have hS : S.card ≤ (S.erase j).card + 1 := by
    by_cases hj : j ∈ S
    · exact (Finset.card_erase_add_one hj).ge
    · simpa only [Finset.erase_eq_self.mpr hj] using
        Nat.le_add_right S.card 1
  simpa only [binLoad, S, T] using hS.trans (Nat.add_le_add_right herase 1)

/-- Exact form of deleting a ball: the surviving balls of colour `i` are
the old colour fibre with the deleted label erased. -/
theorem binLoad_deleteBall_eq_card_erase {q d : ℕ}
    (f : Fin (d + 1) → Fin q) (j : Fin (d + 1)) (i : Fin q) :
    binLoad (deleteBall f j) i =
      ((Finset.univ.filter fun x ↦ f x = i).erase j).card := by
  classical
  let S : Finset (Fin (d + 1)) :=
    Finset.univ.filter fun x ↦ f x = i
  let T : Finset (Fin d) :=
    Finset.univ.filter fun x ↦ deleteBall f j x = i
  have hmap : T.map j.succAboveEmb = S.erase j := by
    ext x
    constructor
    · intro hx
      rw [Finset.mem_map] at hx
      obtain ⟨y, hyT, hyx⟩ := hx
      have hyx' : j.succAbove y = x := by
        simpa only [Fin.coe_succAboveEmb] using hyx
      have hy : f (j.succAbove y) = i := by
        simpa only [T, Finset.mem_filter, Finset.mem_univ, true_and,
          deleteBall] using hyT
      have hxne : x ≠ j := by
        rw [← hyx']
        exact Fin.succAbove_ne j y
      rw [Finset.mem_erase]
      exact ⟨hxne, by
        simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and, ← hyx']
          using hy⟩
    · intro hx
      obtain ⟨hxne, hxS⟩ := Finset.mem_erase.mp hx
      obtain ⟨y, hyx⟩ := Fin.exists_succAbove_eq hxne
      rw [Finset.mem_map]
      refine ⟨y, ?_, by simpa only [Fin.coe_succAboveEmb] using hyx⟩
      have hfi : f x = i := by
        simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using hxS
      simpa only [T, Finset.mem_filter, Finset.mem_univ, true_and,
        deleteBall, hyx] using hfi
  have hcard := congrArg Finset.card hmap
  simpa only [binLoad, deleteBall, S, T, Finset.card_map] using hcard

/-- Exact one-position deletion recurrence for a bin load. -/
theorem binLoad_deleteBall_add_indicator {q d : ℕ}
    (f : Fin (d + 1) → Fin q) (j : Fin (d + 1)) (i : Fin q) :
    binLoad (deleteBall f j) i + (if f j = i then 1 else 0) =
      binLoad f i := by
  rw [binLoad_deleteBall_eq_card_erase]
  by_cases hj : f j = i
  · have hjS : j ∈ Finset.univ.filter fun x ↦ f x = i := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hj]
    simpa only [hj, if_true, binLoad] using
      Finset.card_erase_add_one hjS
  · have hjS : j ∉ Finset.univ.filter fun x ↦ f x = i := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hj
    rw [if_neg hj, Nat.add_zero, Finset.erase_eq_self.mpr hjS]
    rfl

private theorem sum_exp_indicator {q : ℕ} (i : Fin q) :
    (∑ x : Fin q, if x = i then Real.exp 1 else 1) =
      ((q - 1 : ℕ) : ℝ) + Real.exp 1 := by
  have hsumErase :
      (∑ x ∈ (Finset.univ : Finset (Fin q)).erase i,
        if x = i then Real.exp 1 else 1) = ((q - 1 : ℕ) : ℝ) := by
    calc
      (∑ x ∈ (Finset.univ : Finset (Fin q)).erase i,
          if x = i then Real.exp 1 else 1) =
          ∑ _x ∈ (Finset.univ : Finset (Fin q)).erase i, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [if_neg (Finset.ne_of_mem_erase hx)]
      _ = ((q - 1 : ℕ) : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one,
          Finset.card_erase_of_mem (Finset.mem_univ i),
          Finset.card_univ, Fintype.card_fin]
  calc
    (∑ x : Fin q, if x = i then Real.exp 1 else 1) =
        (∑ x ∈ (Finset.univ : Finset (Fin q)).erase i,
          if x = i then Real.exp 1 else 1) +
            (if i = i then Real.exp 1 else 1) :=
      (Finset.sum_erase_add (Finset.univ : Finset (Fin q))
        (fun x ↦ if x = i then Real.exp 1 else 1)
        (Finset.mem_univ i)).symm
    _ = ((q - 1 : ℕ) : ℝ) + Real.exp 1 := by
      rw [hsumErase, if_pos rfl]

/-- Exact exponential-moment identity for one bin at parameter `λ=1`.
This is the finite-product calculation behind the Chernoff estimate. -/
theorem sum_exp_binLoad {q d : ℕ} (i : Fin q) :
    (∑ f : Fin d → Fin q, Real.exp (binLoad f i)) =
      (((q - 1 : ℕ) : ℝ) + Real.exp 1) ^ d := by
  induction d with
  | zero => simp [binLoad]
  | succ d ih =>
      let j : Fin (d + 1) := Fin.last d
      rw [← Equiv.sum_comp
        (Fin.insertNthEquiv (fun _ : Fin (d + 1) ↦ Fin q) j)
        (fun f ↦ Real.exp (binLoad f i))]
      rw [Fintype.sum_prod_type]
      have hload : ∀ (x : Fin q) (g : Fin d → Fin q),
          binLoad
              ((Fin.insertNthEquiv (fun _ : Fin (d + 1) ↦ Fin q) j) (x, g)) i =
            binLoad g i + (if x = i then 1 else 0) := by
        intro x g
        let f : Fin (d + 1) → Fin q :=
          (Fin.insertNthEquiv (fun _ : Fin (d + 1) ↦ Fin q) j) (x, g)
        have hdel : deleteBall f j = g := by
          funext z
          change (Fin.insertNth (α := fun _ : Fin (d + 1) ↦ Fin q) j x g)
            (j.succAbove z) = g z
          exact Fin.insertNth_apply_succAbove
            (α := fun _ : Fin (d + 1) ↦ Fin q) j x g z
        have hj : f j = x := by
          change (Fin.insertNth (α := fun _ : Fin (d + 1) ↦ Fin q) j x g) j = x
          exact Fin.insertNth_apply_same
            (α := fun _ : Fin (d + 1) ↦ Fin q) j x g
        have h := binLoad_deleteBall_add_indicator f j i
        rw [hdel, hj] at h
        exact h.symm
      have hexp : ∀ (x : Fin q) (g : Fin d → Fin q),
          Real.exp (binLoad
              ((Fin.insertNthEquiv (fun _ : Fin (d + 1) ↦ Fin q) j) (x, g)) i) =
            (if x = i then Real.exp 1 else 1) *
              Real.exp (binLoad g i) := by
        intro x g
        rw [hload x g, Nat.cast_add, Real.exp_add]
        by_cases hx : x = i
        · simp [hx, mul_comm]
        · simp [hx]
      calc
        (∑ x : Fin q, ∑ g : Fin d → Fin q,
            Real.exp (binLoad
              ((Fin.insertNthEquiv (fun _ : Fin (d + 1) ↦ Fin q) j) (x, g)) i)) =
            ∑ x : Fin q, ∑ g : Fin d → Fin q,
              (if x = i then Real.exp 1 else 1) *
                Real.exp (binLoad g i) := by
          apply Finset.sum_congr rfl
          intro x _
          apply Finset.sum_congr rfl
          intro g _
          exact hexp x g
        _ = ∑ x : Fin q,
            (if x = i then Real.exp 1 else 1) *
              (∑ g : Fin d → Fin q, Real.exp (binLoad g i)) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.mul_sum]
        _ = (∑ x : Fin q, if x = i then Real.exp 1 else 1) *
              (∑ g : Fin d → Fin q, Real.exp (binLoad g i)) := by
          rw [Finset.sum_mul]
        _ = (((q - 1 : ℕ) : ℝ) + Real.exp 1) ^ (d + 1) := by
          rw [sum_exp_indicator i, ih, pow_succ]
          ring

/-- Fixed-parameter Chernoff bound for one bin, proved directly from the
finite exponential-moment sum. -/
theorem uniform_binLoad_tail_le_exp {q d t : ℕ} (i : Fin q)
    (hq : 0 < q) :
    ((binLoadAtLeastEvent (d := d) i t).card : ℝ) /
        Fintype.card (Fin d → Fin q) ≤
      Real.exp (-(t : ℝ) +
        d * ((Real.exp 1 - 1) / q)) := by
  let Bad := binLoadAtLeastEvent (d := d) i t
  have hpoint : ∀ f ∈ Bad,
      Real.exp (t : ℝ) ≤ Real.exp (binLoad f i) := by
    intro f hf
    apply Real.exp_monotone
    exact_mod_cast (Finset.mem_filter.mp hf).2
  have htotal :
      (Bad.card : ℝ) * Real.exp (t : ℝ) ≤
        ∑ f : Fin d → Fin q, Real.exp (binLoad f i) := by
    calc
      (Bad.card : ℝ) * Real.exp (t : ℝ) =
          ∑ _f ∈ Bad, Real.exp (t : ℝ) := by simp
      _ ≤ ∑ f ∈ Bad, Real.exp (binLoad f i) :=
        Finset.sum_le_sum hpoint
      _ ≤ ∑ f ∈ (Finset.univ : Finset (Fin d → Fin q)),
          Real.exp (binLoad f i) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ Bad)
          (fun _ _ _ ↦ (Real.exp_pos _).le)
      _ = ∑ f : Fin d → Fin q, Real.exp (binLoad f i) := rfl
  have hqReal : (0 : ℝ) < q := by exact_mod_cast hq
  have hcard :
      (Fintype.card (Fin d → Fin q) : ℝ) = (q : ℝ) ^ d := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  have hden : (0 : ℝ) < (q : ℝ) ^ d := pow_pos hqReal d
  have hexpt : 0 < Real.exp (t : ℝ) := Real.exp_pos _
  have hmoment :
      ((∑ f : Fin d → Fin q, Real.exp (binLoad f i)) /
          ((q : ℝ) ^ d * Real.exp (t : ℝ))) =
        Real.exp (-(t : ℝ)) *
          ((((q - 1 : ℕ) : ℝ) + Real.exp 1) / q) ^ d := by
    rw [sum_exp_binLoad i, Real.exp_neg]
    field_simp
    rw [← mul_pow]
    congr 1
    field_simp
  have hprob :
      (Bad.card : ℝ) / (q : ℝ) ^ d ≤
        Real.exp (-(t : ℝ)) *
          ((((q - 1 : ℕ) : ℝ) + Real.exp 1) / q) ^ d := by
    calc
      (Bad.card : ℝ) / (q : ℝ) ^ d =
          ((Bad.card : ℝ) * Real.exp (t : ℝ)) /
            ((q : ℝ) ^ d * Real.exp (t : ℝ)) := by
        field_simp
      _ ≤ (∑ f : Fin d → Fin q, Real.exp (binLoad f i)) /
            ((q : ℝ) ^ d * Real.exp (t : ℝ)) :=
        div_le_div_of_nonneg_right htotal
          (mul_pos hden hexpt).le
      _ = _ := hmoment
  have hqOne : 1 ≤ q := hq
  have hratio :
      ((((q - 1 : ℕ) : ℝ) + Real.exp 1) / q) =
        1 + (Real.exp 1 - 1) / q := by
    rw [Nat.cast_sub hqOne]
    field_simp
    ring
  let x : ℝ := (Real.exp 1 - 1) / q
  have hx : 0 ≤ x := by
    dsimp only [x]
    exact div_nonneg (sub_nonneg.mpr (Real.one_le_exp (by norm_num))) hqReal.le
  have hbase : 1 + x ≤ Real.exp x := by
    simpa only [add_comm] using Real.add_one_le_exp x
  have hpowBound : (1 + x) ^ d ≤ Real.exp (d * x) := by
    calc
      (1 + x) ^ d ≤ (Real.exp x) ^ d := by
        gcongr
      _ = Real.exp (d * x) := (Real.exp_nat_mul x d).symm
  rw [hcard]
  calc
    (Bad.card : ℝ) / (q : ℝ) ^ d ≤
        Real.exp (-(t : ℝ)) *
          ((((q - 1 : ℕ) : ℝ) + Real.exp 1) / q) ^ d := hprob
    _ = Real.exp (-(t : ℝ)) * (1 + x) ^ d := by rw [hratio]
    _ ≤ Real.exp (-(t : ℝ)) * Real.exp (d * x) :=
      mul_le_mul_of_nonneg_left hpowBound (Real.exp_pos _).le
    _ = Real.exp (-(t : ℝ) + d * ((Real.exp 1 - 1) / q)) := by
      rw [← Real.exp_add]

/-- Union-bound Chernoff estimate for the maximum bin load.  Unlike the
factorial estimate above, this version is valid for every natural threshold
`t`, including thresholds larger than the number of balls. -/
theorem uniform_maxBinLoad_tail_le_exp {q d t : ℕ}
    (hq : 0 < q) :
    ((maxBinLoadAtLeastEvent q d t).card : ℝ) /
        Fintype.card (Fin d → Fin q) ≤
      q * Real.exp (-(t : ℝ) +
        d * ((Real.exp 1 - 1) / q)) := by
  let Bad : Fin q → Finset (Fin d → Fin q) :=
    fun i ↦ binLoadAtLeastEvent (d := d) i t
  have hcardPos : (0 : ℝ) ≤ Fintype.card (Fin d → Fin q) := by
    positivity
  have hsubset := maxBinLoadAtLeastEvent_subset_biUnion
    (d := d) (t := t) hq
  have hcardSubset :
      ((maxBinLoadAtLeastEvent q d t).card : ℝ) ≤
        (((Finset.univ : Finset (Fin q)).biUnion Bad).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsubset
  calc
    ((maxBinLoadAtLeastEvent q d t).card : ℝ) /
        Fintype.card (Fin d → Fin q) ≤
      (((Finset.univ : Finset (Fin q)).biUnion Bad).card : ℝ) /
        Fintype.card (Fin d → Fin q) :=
      div_le_div_of_nonneg_right hcardSubset hcardPos
    _ ≤ (∑ i : Fin q, ((Bad i).card : ℝ)) /
        Fintype.card (Fin d → Fin q) := by
      apply div_le_div_of_nonneg_right _ hcardPos
      exact_mod_cast (Finset.card_biUnion_le :
        ((Finset.univ : Finset (Fin q)).biUnion Bad).card ≤
          ∑ i, (Bad i).card)
    _ = ∑ i : Fin q,
        ((Bad i).card : ℝ) / Fintype.card (Fin d → Fin q) := by
      rw [Finset.sum_div]
    _ ≤ ∑ _i : Fin q, Real.exp (-(t : ℝ) +
        d * ((Real.exp 1 - 1) / q)) := by
      apply Finset.sum_le_sum
      intro i _
      exact uniform_binLoad_tail_le_exp i hq
    _ = q * Real.exp (-(t : ℝ) +
        d * ((Real.exp 1 - 1) / q)) := by simp

/-- The concrete bad-allocation estimate for the floored bin count in
Lemma 4.5.  The event is exactly failure of the integer inequality
`2 * |A_i| + 1 < n`. -/
theorem subgraphFinding_bad_fraction_lt {n a : ℕ} (hn : 0 < n)
    (hq : 2 ≤ (6 * a) / n) :
    ((maxBinLoadAtLeastEvent ((6 * a) / n) a (n / 2)).card : ℝ) /
        Fintype.card (Fin a → Fin ((6 * a) / n)) <
      ((6 * a) / n : ℕ) * Real.exp ((1 : ℝ) / 2 - n / 16) := by
  let q := (6 * a) / n
  have hqpos : 0 < q := lt_of_lt_of_le (by omega) hq
  have hexponent := quotientSix_chernoff_exponent_lt hn hq
  change ((maxBinLoadAtLeastEvent q a (n / 2)).card : ℝ) /
      Fintype.card (Fin a → Fin q) <
    (q : ℝ) * Real.exp ((1 : ℝ) / 2 - n / 16)
  calc
    ((maxBinLoadAtLeastEvent q a (n / 2)).card : ℝ) /
        Fintype.card (Fin a → Fin q) ≤
      (q : ℝ) * Real.exp (-(((n / 2 : ℕ) : ℝ)) +
        a * ((Real.exp 1 - 1) / q)) :=
      uniform_maxBinLoad_tail_le_exp hqpos
    _ < (q : ℝ) * Real.exp ((1 : ℝ) / 2 - n / 16) := by
      apply mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr hexponent)
      exact_mod_cast hqpos

/-- Double-counting all possible deleted labels gives an exact fibre-load
identity. -/
theorem sum_binLoad_deleteBall {q d : ℕ}
    (f : Fin (d + 1) → Fin q) (i : Fin q) :
    ∑ j : Fin (d + 1), binLoad (deleteBall f j) i = d * binLoad f i := by
  have hsum :
      (∑ j : Fin (d + 1),
        (binLoad (deleteBall f j) i + (if f j = i then 1 else 0))) =
        ∑ _j : Fin (d + 1), binLoad f i := by
    exact Finset.sum_congr rfl fun j _ ↦
      binLoad_deleteBall_add_indicator f j i
  have hindicator :
      (∑ j : Fin (d + 1), if f j = i then 1 else 0) = binLoad f i := by
    simp only [binLoad, Finset.sum_boole, Nat.cast_id]
  rw [Finset.sum_add_distrib, hindicator] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hsum
  change (∑ j : Fin (d + 1), binLoad (deleteBall f j) i) +
    binLoad f i = (d + 1) * binLoad f i at hsum
  rw [Nat.add_mul, one_mul] at hsum
  omega

/-- For a fixed deleted label, summing over all `(d+1)`-ball allocations is
the same as summing over the deleted ball's colour and every `d`-ball
allocation.  This is the finite coupling identity used in Appendix A.1. -/
theorem sum_maxBinLoad_deleteBall (q d : ℕ) (j : Fin (d + 1)) :
    (∑ f : Fin (d + 1) → Fin q, maxBinLoad (deleteBall f j)) =
      q * ∑ g : Fin d → Fin q, maxBinLoad g := by
  rw [← Equiv.sum_comp
    (Fin.insertNthEquiv (fun _ : Fin (d + 1) ↦ Fin q) j)
    (fun f ↦ maxBinLoad (deleteBall f j))]
  rw [Fintype.sum_prod_type]
  calc
    (∑ x : Fin q, ∑ y : Fin d → Fin q,
        maxBinLoad (deleteBall
          ((Fin.insertNthEquiv (fun _ : Fin (d + 1) ↦ Fin q) j) (x, y)) j)) =
        ∑ _x : Fin q, ∑ y : Fin d → Fin q, maxBinLoad y := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      apply congrArg maxBinLoad
      funext z
      change (Fin.insertNth (α := fun _ : Fin (d + 1) ↦ Fin q) j x y)
        (j.succAbove z) = y z
      exact Fin.insertNth_apply_succAbove
        (α := fun _ : Fin (d + 1) ↦ Fin q) j x y z
    _ = q * ∑ g : Fin d → Fin q, maxBinLoad g := by simp

/-- Pigeonhole bound in division-free form. -/
theorem balls_le_bins_mul_maxBinLoad {q d : ℕ} (f : Fin d → Fin q) :
    d ≤ q * maxBinLoad f := by
  calc
    d = ∑ i, binLoad f i := (sum_binLoad f).symm
    (∑ i, binLoad f i) ≤ ∑ _i : Fin q, maxBinLoad f :=
      Finset.sum_le_sum fun i _ ↦ binLoad_le_maxBinLoad f i
    _ = q * maxBinLoad f := by simp

/-- No bin can contain more balls than were thrown. -/
theorem maxBinLoad_le {q d : ℕ} (f : Fin d → Fin q) :
    maxBinLoad f ≤ d := by
  apply Finset.sup_le
  intro i _
  simpa only [binLoad, Finset.card_univ, Fintype.card_fin] using
    Finset.card_le_card (Finset.filter_subset
      (fun j ↦ f j = i) (Finset.univ : Finset (Fin d)))

/-- Choose a bin attaining the maximum occupancy. -/
def maximizingBin {q d : ℕ} (hq : 0 < q) (f : Fin d → Fin q) : Fin q :=
  Classical.choose (Finset.exists_mem_eq_sup
    (s := (Finset.univ : Finset (Fin q)))
    (Finset.univ_nonempty_iff.mpr ⟨0, hq⟩) (binLoad f))

theorem binLoad_maximizingBin {q d : ℕ} (hq : 0 < q)
    (f : Fin d → Fin q) :
    binLoad f (maximizingBin hq f) = maxBinLoad f := by
  exact (Classical.choose_spec (Finset.exists_mem_eq_sup
    (s := (Finset.univ : Finset (Fin q)))
    (Finset.univ_nonempty_iff.mpr ⟨0, hq⟩) (binLoad f))).2.symm

/-- Deleting one ball decreases the maximum occupancy by at most one. -/
theorem maxBinLoad_le_deleteBall_add_one {q d : ℕ} (hq : 0 < q)
    (f : Fin (d + 1) → Fin q) (j : Fin (d + 1)) :
    maxBinLoad f ≤ maxBinLoad (deleteBall f j) + 1 := by
  calc
    maxBinLoad f = binLoad f (maximizingBin hq f) :=
      (binLoad_maximizingBin hq f).symm
    _ ≤ binLoad (deleteBall f j) (maximizingBin hq f) + 1 :=
      binLoad_le_deleteBall_add_one f j _
    _ ≤ maxBinLoad (deleteBall f j) + 1 :=
      Nat.add_le_add_right (binLoad_le_maxBinLoad _ _) 1

/-- Averaged over every possible deleted label, maximum occupancy loses at
most the fraction needed for monotonicity of `W` in the number of balls. -/
theorem mul_maxBinLoad_le_sum_deleteBall {q d : ℕ} (hq : 0 < q)
    (f : Fin (d + 1) → Fin q) :
    d * maxBinLoad f ≤
      ∑ j : Fin (d + 1), maxBinLoad (deleteBall f j) := by
  let i := maximizingBin hq f
  calc
    d * maxBinLoad f = d * binLoad f i := by
      rw [binLoad_maximizingBin hq f]
    _ = ∑ j : Fin (d + 1), binLoad (deleteBall f j) i :=
      (sum_binLoad_deleteBall f i).symm
    _ ≤ ∑ j : Fin (d + 1), maxBinLoad (deleteBall f j) :=
      Finset.sum_le_sum fun j _ ↦ binLoad_le_maxBinLoad _ _

/-- Summed coupling inequality over the full allocation space. -/
theorem mul_sum_maxBinLoad_succ_le {q d : ℕ} (hq : 0 < q) :
    d * (∑ f : Fin (d + 1) → Fin q, maxBinLoad f) ≤
      (d + 1) * q * (∑ g : Fin d → Fin q, maxBinLoad g) := by
  calc
    d * (∑ f : Fin (d + 1) → Fin q, maxBinLoad f) =
        ∑ f : Fin (d + 1) → Fin q, d * maxBinLoad f := by
      rw [Finset.mul_sum]
    _ ≤ ∑ f : Fin (d + 1) → Fin q,
        ∑ j : Fin (d + 1), maxBinLoad (deleteBall f j) :=
      Finset.sum_le_sum fun f _ ↦ mul_maxBinLoad_le_sum_deleteBall hq f
    _ = ∑ j : Fin (d + 1),
        ∑ f : Fin (d + 1) → Fin q,
          maxBinLoad (deleteBall f j) := by rw [Finset.sum_comm]
    _ = ∑ _j : Fin (d + 1),
        q * ∑ g : Fin d → Fin q, maxBinLoad g := by
      apply Finset.sum_congr rfl
      intro j _
      exact sum_maxBinLoad_deleteBall q d j
    _ = (d + 1) * q *
        (∑ g : Fin d → Fin q, maxBinLoad g) := by simp; ring

/-- Expected-value form of the deletion coupling. -/
theorem mul_expectedMaxBinLoad_succ_le {q d : ℕ} (hq : 0 < q) :
    (d : ℝ) * expectedMaxBinLoad q (d + 1) ≤
      (d + 1 : ℕ) * expectedMaxBinLoad q d := by
  have hNat := mul_sum_maxBinLoad_succ_le (d := d) hq
  have hReal :
      (d : ℝ) *
          (∑ f : Fin (d + 1) → Fin q, (maxBinLoad f : ℝ)) ≤
        ((d + 1 : ℕ) : ℝ) * q *
          (∑ g : Fin d → Fin q, (maxBinLoad g : ℝ)) := by
    exact_mod_cast hNat
  have hqReal : (0 : ℝ) < q := by exact_mod_cast hq
  have hcardSucc :
      (Fintype.card (Fin (d + 1) → Fin q) : ℝ) =
        (q : ℝ) * (q : ℝ) ^ d := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow,
      Nat.cast_mul, pow_succ]
    ring
  have hcard :
      (Fintype.card (Fin d → Fin q) : ℝ) = (q : ℝ) ^ d := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  rw [expectedMaxBinLoad, expectedMaxBinLoad, hcardSucc, hcard]
  calc
    (d : ℝ) *
        ((∑ f : Fin (d + 1) → Fin q, (maxBinLoad f : ℝ)) /
          ((q : ℝ) * (q : ℝ) ^ d)) =
        ((d : ℝ) *
          ∑ f : Fin (d + 1) → Fin q, (maxBinLoad f : ℝ)) /
            ((q : ℝ) * (q : ℝ) ^ d) := by ring
    _ ≤ (((d + 1 : ℕ) : ℝ) * q *
          ∑ g : Fin d → Fin q, (maxBinLoad g : ℝ)) /
            ((q : ℝ) * (q : ℝ) ^ d) :=
      div_le_div_of_nonneg_right hReal (by positivity)
    _ = ((d + 1 : ℕ) : ℝ) *
        ((∑ g : Fin d → Fin q, (maxBinLoad g : ℝ)) /
          (q : ℝ) ^ d) := by
      field_simp

/-- Appendix Lemma A.1, ball-coordinate successor step:
`W(q,d+1) ≤ W(q,d)`. -/
theorem ballsBinsWeight_succ_le {q d : ℕ} (hq : 0 < q) (hd : 0 < d) :
    ballsBinsWeight q (d + 1) ≤ ballsBinsWeight q d := by
  have h := mul_expectedMaxBinLoad_succ_le (d := d) hq
  rw [ballsBinsWeight, ballsBinsWeight,
    div_le_div_iff₀ (by positivity : (0 : ℝ) < (d + 1 : ℕ))
      (by exact_mod_cast hd : (0 : ℝ) < d)]
  simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using h

/-- Appendix Lemma A.1, monotonicity in the number of balls. -/
theorem ballsBinsWeight_antitone_balls {q d₁ d₂ : ℕ}
    (hq : 0 < q) (hd₁ : 0 < d₁) (hdd : d₁ ≤ d₂) :
    ballsBinsWeight q d₂ ≤ ballsBinsWeight q d₁ := by
  induction d₂, hdd using Nat.le_induction with
  | base => exact le_rfl
  | succ d hd₁d ih =>
      have hd : 0 < d := hd₁.trans_le hd₁d
      exact (ballsBinsWeight_succ_le hq hd).trans ih

theorem expectedMaxBinLoad_nonneg (q d : ℕ) :
    0 ≤ expectedMaxBinLoad q d := by
  unfold expectedMaxBinLoad
  positivity

/-- The maximum occupancy is at most the number of balls, hence so is its
uniform expectation. -/
theorem expectedMaxBinLoad_le_balls (q d : ℕ) :
    expectedMaxBinLoad q d ≤ d := by
  by_cases hq : q = 0
  · subst q
    cases d with
    | zero =>
        have hmax : ∀ f : Fin 0 → Fin 0, maxBinLoad f = 0 := fun f ↦
          Nat.eq_zero_of_le_zero (maxBinLoad_le f)
        simp [expectedMaxBinLoad, hmax]
    | succ d =>
        simp [expectedMaxBinLoad]
        positivity
  · have hqpos : 0 < q := Nat.pos_of_ne_zero hq
    let i₀ : Fin q := ⟨0, hqpos⟩
    let f₀ : Fin d → Fin q := fun _ ↦ i₀
    have hcard : (0 : ℝ) < Fintype.card (Fin d → Fin q) := by
      exact_mod_cast Fintype.card_pos_iff.mpr ⟨f₀⟩
    have hsum :
        (∑ f : Fin d → Fin q, (maxBinLoad f : ℝ)) ≤
          ∑ _f : Fin d → Fin q, (d : ℝ) :=
      Finset.sum_le_sum fun f _ ↦ by exact_mod_cast maxBinLoad_le f
    rw [expectedMaxBinLoad, div_le_iff₀ hcard]
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_comm] using hsum

theorem ballsBinsWeight_nonneg (q d : ℕ) :
    0 ≤ ballsBinsWeight q d := by
  unfold ballsBinsWeight
  exact div_nonneg (expectedMaxBinLoad_nonneg q d) (by positivity)

/-- The normalised expected maximum occupancy lies at most at one. -/
theorem ballsBinsWeight_le_one {q d : ℕ} (hd : 0 < d) :
    ballsBinsWeight q d ≤ 1 := by
  rw [ballsBinsWeight,
    (div_le_one (by exact_mod_cast hd : (0 : ℝ) < d))]
  exact expectedMaxBinLoad_le_balls q d

@[simp]
theorem expectedMaxBinLoad_zero (q : ℕ) :
    expectedMaxBinLoad q 0 = 0 := by
  have hmax : ∀ f : Fin 0 → Fin q, maxBinLoad f = 0 := by
    intro f
    apply Nat.eq_zero_of_le_zero
    apply Finset.sup_le
    intro i _
    simp [binLoad]
  simp [expectedMaxBinLoad, hmax]

@[simp]
theorem expectedMaxBinLoad_zero_bins (d : ℕ) :
    expectedMaxBinLoad 0 d = 0 := by
  cases d with
  | zero => exact expectedMaxBinLoad_zero 0
  | succ d => simp [expectedMaxBinLoad]

@[simp]
theorem ballsBinsWeight_zero_bins (d : ℕ) :
    ballsBinsWeight 0 d = 0 := by
  simp [ballsBinsWeight]

/-- The zero-bin edge case omitted in the paper's informal probabilistic
language is mathematically harmless: with our literal finite average,
`W(0,d)=0`, so the empty graph witnesses Lemma 4.5. -/
theorem BLSSubgraphFindingAt_of_binCount_eq_zero
    [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (r n Δ : ℕ) (V₀ U : Finset V)
    (hn : 2 ≤ n) (hq : subgraphFindingBinCount n V₀.card = 0) :
    BLSSubgraphFindingAt G r n Δ V₀ U := by
  intro _hdisjoint _hcover _hU _hcard _hglobalDegree _hdegree
  refine ⟨⊥, bot_le, ?_, ?_⟩
  · intro hcopy
    obtain ⟨f⟩ := hcopy
    have hp : (pathGraph n).Adj
        (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n) := by
      rw [pathGraph_adj]
      exact Or.inl rfl
    have := f.toHom.map_adj hp
    exact this
  · rw [hq, ballsBinsWeight_zero_bins, mul_zero]
    positivity

/-- Rewriting the expected maximum in terms of the normalised weight. -/
theorem expectedMaxBinLoad_eq_mul_weight (q d : ℕ) :
    expectedMaxBinLoad q d = d * ballsBinsWeight q d := by
  cases d with
  | zero => simp [ballsBinsWeight]
  | succ d =>
      rw [ballsBinsWeight]
      field_simp

/-- Observation 4.4 in its reusable weighted form.  Vertices of degree zero
are handled separately, while every positive degree uses the already proved
monotonicity of `W` in its ball coordinate. -/
theorem expectedMaxBinLoad_degree_sum_lower_bound
    {B : Type*} [Fintype B] {q Δ : ℕ} (hq : 0 < q) (_hΔ : 0 < Δ)
    (degree : B → ℕ) (hle : ∀ b, degree b ≤ Δ) :
    (∑ b, (degree b : ℝ)) * ballsBinsWeight q Δ ≤
      ∑ b, expectedMaxBinLoad q (degree b) := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro b _
  by_cases hb : degree b = 0
  · simp only [hb, Nat.cast_zero, zero_mul, expectedMaxBinLoad_zero]
    exact le_rfl
  · have hbpos : 0 < degree b := Nat.pos_of_ne_zero hb
    have hW := ballsBinsWeight_antitone_balls hq hbpos (hle b)
    calc
      (degree b : ℝ) * ballsBinsWeight q Δ ≤
          (degree b : ℝ) * ballsBinsWeight q (degree b) :=
        mul_le_mul_of_nonneg_left hW (by positivity)
      _ = expectedMaxBinLoad q (degree b) :=
        (expectedMaxBinLoad_eq_mul_weight q (degree b)).symm

/-- Degree of a vertex in a finite bipartite relation, measured on the
left side. -/
def relationDegree {A B : Type*} [Fintype A]
    (R : A → B → Prop) [DecidableRel R] (b : B) : ℕ :=
  #{a ∈ (Finset.univ : Finset A) | R a b}

/-- Number of relation edges retained after every right vertex chooses a
bin maximizing its labelled neighbourhood. -/
def maximizingBinYield {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] (R : A → B → Prop) [DecidableRel R]
    {q : ℕ} (f : A → Fin q) : ℕ :=
  ∑ b, restrictedMaxBinLoad (fun a ↦ R a b) f

theorem maximizingBinYield_le_degreeSum
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]
    (R : A → B → Prop) [DecidableRel R] {q : ℕ} (f : A → Fin q) :
    maximizingBinYield R f ≤ ∑ b, relationDegree R b := by
  unfold maximizingBinYield
  apply Finset.sum_le_sum
  intro b _
  calc
    restrictedMaxBinLoad (fun a ↦ R a b) f ≤
        Fintype.card {a // R a b} :=
      maxBinLoadOn_le_card _
    _ = relationDegree R b := by
      simpa only [relationDegree] using
        Fintype.card_subtype (fun a ↦ R a b)

/-- Exact global-partition form of the balls-and-bins calculation.  Although
neighbourhood restrictions overlap, linearity of the literal finite sums
shows that a single global labelling has the required average yield. -/
theorem uniformAverage_maximizingBinYield
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]
    (R : A → B → Prop) [DecidableRel R] {q : ℕ} (hq : 0 < q) :
    (∑ f : A → Fin q, (maximizingBinYield R f : ℝ)) /
        Fintype.card (A → Fin q) =
      ∑ b, expectedMaxBinLoad q (relationDegree R b) := by
  have hsum :
      (∑ f : A → Fin q, (maximizingBinYield R f : ℝ)) =
        ∑ b, ∑ f : A → Fin q,
          (restrictedMaxBinLoad (fun a ↦ R a b) f : ℝ) := by
    simp only [maximizingBinYield, Nat.cast_sum]
    rw [Finset.sum_comm]
  rw [hsum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro b _
  rw [uniformAverage_restrictedMaxBinLoad (fun a ↦ R a b) hq]
  congr 2
  simpa only [relationDegree] using
    Fintype.card_subtype (fun a ↦ R a b)

/-- Observation 4.4 with the global allocation and all restriction fibres
fully internalised. -/
theorem maximizingBinYield_average_lower_bound
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]
    (R : A → B → Prop) [DecidableRel R] {q Δ : ℕ}
    (hq : 0 < q) (hΔ : 0 < Δ)
    (hdegree : ∀ b, relationDegree R b ≤ Δ) :
    (∑ b, (relationDegree R b : ℝ)) * ballsBinsWeight q Δ ≤
      (∑ f : A → Fin q, (maximizingBinYield R f : ℝ)) /
        Fintype.card (A → Fin q) := by
  rw [uniformAverage_maximizingBinYield R hq]
  exact expectedMaxBinLoad_degree_sum_lower_bound hq hΔ
    (relationDegree R) hdegree

theorem one_le_maxBinLoad {q d : ℕ} (_hq : 0 < q) (hd : 0 < d)
    (f : Fin d → Fin q) : 1 ≤ maxBinLoad f := by
  have h := balls_le_bins_mul_maxBinLoad f
  by_contra hzero
  have : maxBinLoad f = 0 := by omega
  simp only [this, mul_zero] at h
  omega

/-- Averaging preserves a pointwise lower bound on maximum occupancy. -/
private theorem le_expectedMaxBinLoad_of_forall {q d : ℕ} (hq : 0 < q)
    {a : ℝ} (h : ∀ f : Fin d → Fin q, a ≤ maxBinLoad f) :
    a ≤ expectedMaxBinLoad q d := by
  let i₀ : Fin q := ⟨0, hq⟩
  let f₀ : Fin d → Fin q := fun _ ↦ i₀
  have hcard : 0 < Fintype.card (Fin d → Fin q) :=
    Fintype.card_pos_iff.mpr ⟨f₀⟩
  have hsum : (∑ _f : Fin d → Fin q, a) ≤
      ∑ f : Fin d → Fin q, (maxBinLoad f : ℝ) :=
    Finset.sum_le_sum fun f _ ↦ h f
  rw [expectedMaxBinLoad, le_div_iff₀ (by exact_mod_cast hcard)]
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.cast_ofNat, Nat.cast_mul, Nat.cast_ofNat, mul_comm] using hsum

/-- The expected maximum is at least the average load `d/q`. -/
theorem div_le_expectedMaxBinLoad {q d : ℕ} (hq : 0 < q) :
    (d : ℝ) / q ≤ expectedMaxBinLoad q d := by
  apply le_expectedMaxBinLoad_of_forall hq
  intro f
  rw [div_le_iff₀ (by exact_mod_cast hq)]
  exact_mod_cast (by simpa only [Nat.mul_comm] using
    balls_le_bins_mul_maxBinLoad f)

/-- With at least one ball, the expected maximum is at least one. -/
theorem one_le_expectedMaxBinLoad {q d : ℕ} (hq : 0 < q) (hd : 0 < d) :
    (1 : ℝ) ≤ expectedMaxBinLoad q d := by
  apply le_expectedMaxBinLoad_of_forall hq
  intro f
  exact_mod_cast one_le_maxBinLoad hq hd f

/-- First half of Appendix Fact A.4: `W(q,d) >= 1/q`. -/
theorem one_div_le_ballsBinsWeight {q d : ℕ} (hq : 0 < q) (hd : 0 < d) :
    (1 : ℝ) / q ≤ ballsBinsWeight q d := by
  have h := div_le_expectedMaxBinLoad (d := d) hq
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  calc
    (1 : ℝ) / q = ((d : ℝ) / q) / d := by
      field_simp
    _ ≤ expectedMaxBinLoad q d / d :=
      div_le_div_of_nonneg_right h hdR.le
    _ = ballsBinsWeight q d := rfl

/-- Second half of Appendix Fact A.4: `W(q,d) >= 1/d`. -/
theorem one_div_balls_le_ballsBinsWeight {q d : ℕ}
    (hq : 0 < q) (hd : 0 < d) :
    (1 : ℝ) / d ≤ ballsBinsWeight q d := by
  have h := one_le_expectedMaxBinLoad hq hd
  exact div_le_div_of_nonneg_right h (by positivity)

/-- Appendix Fact A.4 in the paper's combined form. -/
theorem ballsBinsWeight_lower_bound {q d : ℕ} (hq : 0 < q) (hd : 0 < d) :
    max ((1 : ℝ) / q) ((1 : ℝ) / d) ≤ ballsBinsWeight q d :=
  max_le (one_div_le_ballsBinsWeight hq hd)
    (one_div_balls_le_ballsBinsWeight hq hd)

/-- Complete exceptional-event estimate used by the truncated expectation
in Lemma 4.5.  This theorem connects the literal floor/ceiling bin count,
the v1 threshold, the path-safe integer event, and Fact A.4. -/
theorem subgraphFinding_bad_fraction_le_weight_div_three
    {r n v Δ : ℕ} (hr : 21 ≤ r)
    (hn : 100 * Real.log (r : ℝ) ≤ (n : ℝ))
    (hv : (v : ℝ) ≤ 2 * (r * Real.log (r : ℝ)) * n)
    (hqTwo : 2 ≤ subgraphFindingBinCount n v) (hΔ : 0 < Δ) :
    let a := (v + 1) / 2
    let q := subgraphFindingBinCount n v
    (((Finset.univ : Finset (Fin a → Fin q)) \
          pathSafeAllocationEvent q a n).card : ℝ) /
        Fintype.card (Fin a → Fin q) ≤
      ballsBinsWeight q Δ / 3 := by
  let a := (v + 1) / 2
  let q := subgraphFindingBinCount n v
  have hrReal : (0 : ℝ) < r := by positivity
  have hlogOne : (1 : ℝ) < Real.log (r : ℝ) := by
    apply (Real.lt_log_iff_exp_lt hrReal).mpr
    exact Real.exp_one_lt_three.trans_le
      (by exact_mod_cast (show 3 ≤ r by omega))
  have hnHundred : (100 : ℝ) < n := by nlinarith
  have hnNat : 2 ≤ n := by exact_mod_cast (show (2 : ℝ) ≤ n by linarith)
  have hnPos : 0 < n := by omega
  have hqPos : 0 < q := by
    dsimp only [q]
    omega
  have hqAsQuotient : q = (6 * a) / n := by
    simp only [q, a, subgraphFindingBinCount]
  have hbadStrict :
      ((maxBinLoadAtLeastEvent q a (n / 2)).card : ℝ) /
          Fintype.card (Fin a → Fin q) <
        (q : ℝ) * Real.exp ((1 : ℝ) / 2 - n / 16) := by
    rw [hqAsQuotient]
    exact subgraphFinding_bad_fraction_lt hnPos (by
      simpa only [← hqAsQuotient] using hqTwo)
  have hqBound : (q : ℝ) ≤ 7 * r * Real.log (r : ℝ) := by
    dsimp only [q]
    exact subgraphFindingBinCount_le_seven_mul hr hn hv
  have htail :
      (q : ℝ) * Real.exp ((1 : ℝ) / 2 - n / 16) ≤
        ((1 : ℝ) / q) / 3 :=
    binCount_mul_exp_le_one_div_three hr hn hqPos hqBound
  have hweight := one_div_le_ballsBinsWeight hqPos hΔ
  dsimp only
  rw [complement_pathSafeAllocationEvent hnNat]
  exact hbadStrict.le.trans (htail.trans
    (div_le_div_of_nonneg_right hweight (by norm_num)))

@[simp]
theorem maxBinLoad_one_bin {d : ℕ} (f : Fin d → Fin 1) :
    maxBinLoad f = d := by
  apply le_antisymm (maxBinLoad_le f)
  have h := balls_le_bins_mul_maxBinLoad f
  simpa using h

@[simp]
theorem maxBinLoadOn_one_bin {D : Type*} [Fintype D] [DecidableEq D]
    (f : D → Fin 1) : maxBinLoadOn f = Fintype.card D := by
  let e : D ≃ Fin (Fintype.card D) := Fintype.equivFin D
  have h := maxBinLoadOn_comp_equiv e.symm f
  simpa only [maxBinLoadOn_fin_eq_maxBinLoad, maxBinLoad_one_bin] using h.symm

@[simp]
theorem restrictedMaxBinLoad_one_bin
    {D : Type*} [Fintype D] [DecidableEq D]
    (p : D → Prop) [DecidablePred p] (f : D → Fin 1) :
    restrictedMaxBinLoad p f = Fintype.card {x // p x} := by
  exact maxBinLoadOn_one_bin _

@[simp]
theorem expectedMaxBinLoad_one_bin (d : ℕ) :
    expectedMaxBinLoad 1 d = d := by
  simp [expectedMaxBinLoad]

/-- In the one-bin boundary case the normalised maximum load is exactly
one, provided at least one ball is present. -/
theorem ballsBinsWeight_one_bin {d : ℕ} (hd : 0 < d) :
    ballsBinsWeight 1 d = 1 := by
  rw [ballsBinsWeight, expectedMaxBinLoad_one_bin]
  field_simp

theorem maximizingBinYield_one_bin
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]
    (R : A → B → Prop) [DecidableRel R] (f : A → Fin 1) :
    maximizingBinYield R f = ∑ b, relationDegree R b := by
  unfold maximizingBinYield
  apply Finset.sum_congr rfl
  intro b _
  rw [restrictedMaxBinLoad_one_bin]
  simpa only [relationDegree] using
    Fintype.card_subtype (fun a ↦ R a b)

/-- In the one-bin branch every allocation is path-safe whenever the whole
left side is already a sufficiently small vertex cover. -/
theorem pathSafeAllocationEvent_one_bin_eq_univ {d n : ℕ}
    (hsmall : 2 * d + 1 < n) :
    pathSafeAllocationEvent 1 d n = Finset.univ := by
  ext f
  simp only [pathSafeAllocationEvent, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro _
    trivial
  · intro _ i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    have hall : ∀ j : Fin d, f j = (0 : Fin 1) := fun j ↦
      Subsingleton.elim _ _
    simpa [binLoad, hall] using hsmall

/-- The `q=1` replacement for the Chernoff extraction: the unique bin keeps
all relation edges and is deterministically safe. -/
theorem exists_pathSafe_maximizingBinYield_one_bin
    {B : Type*} [Fintype B]
    (R : Fin d → B → Prop) [DecidableRel R] {n Δ : ℕ}
    (hsmall : 2 * d + 1 < n) (hΔ : 0 < Δ) :
    ∃ f ∈ pathSafeAllocationEvent 1 d n,
      (2 : ℝ) / 3 * (∑ b, (relationDegree R b : ℝ)) *
          ballsBinsWeight 1 Δ ≤ maximizingBinYield R f := by
  let f : Fin d → Fin 1 := fun _ ↦ 0
  refine ⟨f, ?_, ?_⟩
  · rw [pathSafeAllocationEvent_one_bin_eq_univ hsmall]
    exact Finset.mem_univ f
  · rw [ballsBinsWeight_one_bin hΔ, mul_one,
      maximizingBinYield_one_bin R f]
    simp only [Nat.cast_sum]
    have hsum : (0 : ℝ) ≤ ∑ b, (relationDegree R b : ℝ) := by
      positivity
    nlinarith

/-- The floor arithmetic omitted in the paper's `q=1` edge case: if its
displayed bin count is one, then `ceil(v/2)` itself is path-safe. -/
theorem subgraphFinding_one_bin_small {n v : ℕ} (hn : 0 < n)
    (hq : subgraphFindingBinCount n v = 1) :
    2 * ((v + 1) / 2) + 1 < n := by
  let a := (v + 1) / 2
  have ha : 0 < a := by
    by_contra hzero
    have : a = 0 := Nat.eq_zero_of_not_pos hzero
    have hqZero : subgraphFindingBinCount n v = 0 := by
      unfold subgraphFindingBinCount
      change 6 * a / n = 0
      rw [this, mul_zero]
      exact Nat.zero_div n
    omega
  have hupper := six_half_lt_mul_succ_subgraphFindingBinCount
    (v := v) hn
  rw [hq] at hupper
  change 2 * a + 1 < n
  change 6 * a < n * (1 + 1) at hupper
  omega

/-- Finite probabilistic method: some outcome is at least its uniform
average. -/
theorem exists_uniformAverage_le_value {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (w : Ω → ℝ) :
    ∃ ω, (∑ x, w x) / Fintype.card Ω ≤ w ω := by
  by_contra h
  push Not at h
  have hsum : (∑ x, w x) <
      ∑ _x : Ω, (∑ x, w x) / Fintype.card Ω :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun x _ ↦ h x
  have hcard : (Fintype.card Ω : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have heq : (∑ _x : Ω, (∑ x, w x) / Fintype.card Ω) =
      ∑ x, w x := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  rw [heq] at hsum
  exact (lt_irrefl _ hsum)

/-- Finite probabilistic extraction restricted to a nonempty good event.
The denominator remains the size of the full sample space, exactly as for
the truncated expectation `E[X 1_E]` used in Lemma 4.5. -/
theorem exists_good_of_le_uniformTruncatedAverage
    {Ω : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
    (Good : Finset Ω) (hGood : Good.Nonempty) (w : Ω → ℝ)
    (hw : ∀ ω ∈ Good, 0 ≤ w ω) {a : ℝ}
    (ha : a ≤ (∑ ω ∈ Good, w ω) / Fintype.card Ω) :
    ∃ ω ∈ Good, a ≤ w ω := by
  letI : Nonempty ↑Good := Finset.nonempty_coe_sort.mpr hGood
  have hsum : 0 ≤ ∑ ω ∈ Good, w ω :=
    Finset.sum_nonneg fun ω hω ↦ hw ω hω
  have hGoodCard : (0 : ℝ) < Good.card := by
    exact_mod_cast hGood.card_pos
  have hOmegaCard : (0 : ℝ) < Fintype.card Ω := by
    exact_mod_cast Fintype.card_pos
  have hdenom :
      (∑ ω ∈ Good, w ω) / Fintype.card Ω ≤
        (∑ ω ∈ Good, w ω) / Good.card := by
    rw [div_le_div_iff₀ hOmegaCard hGoodCard]
    exact mul_le_mul_of_nonneg_left
      (by exact_mod_cast Finset.card_le_univ Good) hsum
  obtain ⟨ω, hω⟩ :=
    exists_uniformAverage_le_value (fun x : ↑Good ↦ w x)
  refine ⟨ω, ω.2, ha.trans (hdenom.trans ?_)⟩
  simpa only [Finset.sum_coe_sort, Fintype.card_coe] using hω

/-- Removing a bad event costs at most `M` times its uniform probability.
This is the deterministic finite-sum form of the truncation estimate in the
proof of Lemma 4.5. -/
theorem uniformTruncatedAverage_lower_bound
    {Ω : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
    (Good : Finset Ω) (w : Ω → ℝ) {A M p : ℝ}
    (hM : 0 ≤ M) (hwbad : ∀ ω ∉ Good, w ω ≤ M)
    (havg : A ≤ (∑ ω, w ω) / Fintype.card Ω)
    (hbad : (((Finset.univ \ Good).card : ℕ) : ℝ) /
      Fintype.card Ω ≤ p) :
    A - M * p ≤
      (∑ ω ∈ Good, w ω) / Fintype.card Ω := by
  have hcard : (0 : ℝ) < Fintype.card Ω := by
    exact_mod_cast Fintype.card_pos
  have hsumBad :
      (∑ ω ∈ Finset.univ \ Good, w ω) ≤
        (((Finset.univ \ Good).card : ℕ) : ℝ) * M := by
    calc
      (∑ ω ∈ Finset.univ \ Good, w ω) ≤
          ∑ _ω ∈ Finset.univ \ Good, M := by
        apply Finset.sum_le_sum
        intro ω hω
        exact hwbad ω (by
          simpa only [Finset.mem_sdiff, Finset.mem_univ, true_and] using hω)
      _ = (((Finset.univ \ Good).card : ℕ) : ℝ) * M := by simp
  have hbadAvg :
      (∑ ω ∈ Finset.univ \ Good, w ω) / Fintype.card Ω ≤
        M * p := by
    calc
      (∑ ω ∈ Finset.univ \ Good, w ω) / Fintype.card Ω ≤
          ((((Finset.univ \ Good).card : ℕ) : ℝ) * M) /
            Fintype.card Ω :=
        div_le_div_of_nonneg_right hsumBad hcard.le
      _ = M *
          ((((Finset.univ \ Good).card : ℕ) : ℝ) /
            Fintype.card Ω) := by ring
      _ ≤ M * p := mul_le_mul_of_nonneg_left hbad hM
  have hsplitRaw := Finset.sum_sdiff
    (f := w) (s₁ := Good) (s₂ := (Finset.univ : Finset Ω))
    (Finset.subset_univ Good)
  have hsplit :
      (∑ ω, w ω) / Fintype.card Ω =
        (∑ ω ∈ Finset.univ \ Good, w ω) / Fintype.card Ω +
          (∑ ω ∈ Good, w ω) / Fintype.card Ω := by
    rw [← hsplitRaw]
    ring
  rw [hsplit] at havg
  linarith

/-- The complete finite-probabilistic extraction step used after the
Chernoff estimate in Lemma 4.5. -/
theorem exists_good_value_of_average_and_bad_bound
    {Ω : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
    (Good : Finset Ω) (hGood : Good.Nonempty) (w : Ω → ℝ)
    {A M p : ℝ} (hM : 0 ≤ M) (hwgood : ∀ ω ∈ Good, 0 ≤ w ω)
    (hwbad : ∀ ω ∉ Good, w ω ≤ M)
    (havg : A ≤ (∑ ω, w ω) / Fintype.card Ω)
    (hbad : (((Finset.univ \ Good).card : ℕ) : ℝ) /
      Fintype.card Ω ≤ p) :
    ∃ ω ∈ Good, A - M * p ≤ w ω := by
  apply exists_good_of_le_uniformTruncatedAverage Good hGood w hwgood
  exact uniformTruncatedAverage_lower_bound Good w hM hwbad havg hbad

/-- A strict uniform probability bound below one guarantees that the good
event is inhabited. -/
theorem good_nonempty_of_bad_fraction_lt_one
    {Ω : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
    (Good : Finset Ω)
    (hbad : (((Finset.univ \ Good).card : ℕ) : ℝ) /
      Fintype.card Ω < 1) :
    Good.Nonempty := by
  by_contra hGood
  rw [Finset.not_nonempty_iff_eq_empty] at hGood
  subst Good
  have hcard : (Fintype.card Ω : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp only [Finset.sdiff_empty, Finset.card_univ, div_self hcard,
    lt_self_iff_false] at hbad

/-- Finite Cauchy--Schwarz restricted to the support of a random variable.
This is the algebraic heart of the Paley--Zygmund step in Appendix A.2. -/
theorem sq_sum_le_support_card_mul_sum_sq
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (w : Ω → ℝ) :
    (∑ ω, w ω) ^ 2 ≤
      (((Finset.univ.filter fun ω ↦ w ω ≠ 0).card : ℕ) : ℝ) *
        ∑ ω, (w ω) ^ 2 := by
  let S := Finset.univ.filter fun ω ↦ w ω ≠ 0
  have hsum : (∑ ω, w ω) = ∑ ω ∈ S, w ω := by
    simp only [S, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases hω : w ω = 0 <;> simp [hω]
  have hsumSq : (∑ ω, (w ω) ^ 2) = ∑ ω ∈ S, (w ω) ^ 2 := by
    simp only [S, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases hω : w ω = 0 <;> simp [hω]
  rw [hsum, hsumSq]
  exact sq_sum_le_card_mul_sum_sq

/-- Probability-normalised finite Paley--Zygmund inequality at threshold
zero, stated purely with uniform cardinalities. -/
theorem secondMoment_support_fraction_lower_bound
    {Ω : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
    (w : Ω → ℝ) (hsq : 0 < ∑ ω, (w ω) ^ 2) :
    (∑ ω, w ω) ^ 2 /
        (Fintype.card Ω * ∑ ω, (w ω) ^ 2) ≤
      ((Finset.univ.filter fun ω ↦ w ω ≠ 0).card : ℝ) /
        Fintype.card Ω := by
  have hcard : (0 : ℝ) < Fintype.card Ω := by
    exact_mod_cast Fintype.card_pos
  have hcs := sq_sum_le_support_card_mul_sum_sq w
  rw [div_le_div_iff₀ (mul_pos hcard hsq) hcard]
  calc
    (∑ ω, w ω) ^ 2 * Fintype.card Ω ≤
        (((Finset.univ.filter fun ω ↦ w ω ≠ 0).card : ℕ) : ℝ) *
          (∑ ω, (w ω) ^ 2) * Fintype.card Ω :=
      mul_le_mul_of_nonneg_right hcs hcard.le
    _ = ((Finset.univ.filter fun ω ↦ w ω ≠ 0).card : ℝ) *
        (Fintype.card Ω * ∑ ω, (w ω) ^ 2) := by ring

/-- Paley--Zygmund for the heavy-bin counter `B_t`, with its support
identified exactly as the maximum-load tail event. -/
theorem heavyBinCount_secondMoment_lower_bound {q d t : ℕ}
    (hq : 0 < q)
    (hsq : 0 < ∑ f : Fin d → Fin q, (heavyBinCount f t : ℝ) ^ 2) :
    (∑ f : Fin d → Fin q, (heavyBinCount f t : ℝ)) ^ 2 /
        (Fintype.card (Fin d → Fin q) *
          ∑ f : Fin d → Fin q, (heavyBinCount f t : ℝ) ^ 2) ≤
      ((maxBinLoadAtLeastEvent q d t).card : ℝ) /
        Fintype.card (Fin d → Fin q) := by
  let i₀ : Fin q := ⟨0, hq⟩
  letI : Nonempty (Fin d → Fin q) := ⟨fun _ ↦ i₀⟩
  have h := secondMoment_support_fraction_lower_bound
    (fun f : Fin d → Fin q ↦ (heavyBinCount f t : ℝ)) hsq
  rw [support_heavyBinCount_eq_maxEvent hq] at h
  exact h

/-- A maximum-load tail event contributes its threshold times its uniform
probability to the expectation. -/
theorem threshold_mul_maxEvent_fraction_le_expected {q d t : ℕ}
    : (t : ℝ) * ((maxBinLoadAtLeastEvent q d t).card : ℝ) /
        Fintype.card (Fin d → Fin q) ≤ expectedMaxBinLoad q d := by
  let Bad := maxBinLoadAtLeastEvent q d t
  have hsum : (Bad.card : ℝ) * t ≤
      ∑ f : Fin d → Fin q, (maxBinLoad f : ℝ) := by
    calc
      (Bad.card : ℝ) * t = ∑ _f ∈ Bad, (t : ℝ) := by simp
      _ ≤ ∑ f ∈ Bad, (maxBinLoad f : ℝ) := by
        apply Finset.sum_le_sum
        intro f hf
        exact_mod_cast (Finset.mem_filter.mp hf).2
      _ ≤ ∑ f ∈ (Finset.univ : Finset (Fin d → Fin q)),
          (maxBinLoad f : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ Bad)
          (fun _ _ _ ↦ by positivity)
      _ = ∑ f : Fin d → Fin q, (maxBinLoad f : ℝ) := rfl
  have hcard : (0 : ℝ) ≤ Fintype.card (Fin d → Fin q) := by positivity
  rw [expectedMaxBinLoad]
  calc
    (t : ℝ) * (Bad.card : ℝ) /
        Fintype.card (Fin d → Fin q) =
      (Bad.card : ℝ) * t / Fintype.card (Fin d → Fin q) := by ring
    _ ≤ (∑ f : Fin d → Fin q, (maxBinLoad f : ℝ)) /
        Fintype.card (Fin d → Fin q) :=
      div_le_div_of_nonneg_right hsum hcard

/-- Fully finite second-moment lower bound for the expected maximum. -/
theorem secondMoment_expectedMaxBinLoad_lower_bound {q d t : ℕ}
    (hq : 0 < q)
    (hsq : 0 < ∑ f : Fin d → Fin q, (heavyBinCount f t : ℝ) ^ 2) :
    (t : ℝ) *
        ((∑ f : Fin d → Fin q, (heavyBinCount f t : ℝ)) ^ 2 /
          (Fintype.card (Fin d → Fin q) *
            ∑ f : Fin d → Fin q, (heavyBinCount f t : ℝ) ^ 2)) ≤
      expectedMaxBinLoad q d := by
  have hpaley := heavyBinCount_secondMoment_lower_bound hq hsq
  have hmul := mul_le_mul_of_nonneg_left hpaley (by positivity : (0 : ℝ) ≤ t)
  exact hmul.trans (by
    simpa only [mul_div_assoc] using
      threshold_mul_maxEvent_fraction_le_expected (q := q) (d := d) (t := t))

/-- Appendix A.2 reduced to a single off-diagonal correlation estimate.
The displayed lower bound is the exact finite Paley--Zygmund expression,
before the paper's analytic simplifications. -/
theorem expectedMaxBinLoad_lower_bound_of_pair_bound {q d t : ℕ}
    (i₀ : Fin q) {C : ℝ}
    (hfixed : 0 < ((binLoadAtLeastEvent (d := d) i₀ t).card : ℝ))
    (hpair : ∀ i j : Fin q, i ≠ j →
      ((twoBinLoadAtLeastEvent (d := d) i j t).card : ℝ) ≤
        C * ((binLoadAtLeastEvent (d := d) i₀ t).card : ℝ) ^ 2 /
          Fintype.card (Fin d → Fin q)) :
    let A : ℝ := (binLoadAtLeastEvent (d := d) i₀ t).card
    let N : ℝ := Fintype.card (Fin d → Fin q)
    let S : ℝ := q * A + q * (q - 1) * (C * A ^ 2 / N)
    (t : ℝ) * ((q * A) ^ 2 / (N * S)) ≤ expectedMaxBinLoad q d := by
  let A : ℝ := (binLoadAtLeastEvent (d := d) i₀ t).card
  let N : ℝ := Fintype.card (Fin d → Fin q)
  let S : ℝ := q * A + q * (q - 1) * (C * A ^ 2 / N)
  have hqPos : 0 < q := lt_of_le_of_lt (Nat.zero_le _) i₀.isLt
  have hN : (0 : ℝ) < N := by
    dsimp only [N]
    have : Nonempty (Fin d → Fin q) := ⟨fun _ ↦ i₀⟩
    exact_mod_cast Fintype.card_pos
  have hfirst :
      (∑ f : Fin d → Fin q, (heavyBinCount f t : ℝ)) = q * A := by
    dsimp only [A]
    exact_mod_cast sum_heavyBinCount_eq_mul_fixed (d := d) (t := t) i₀
  have hsecond := sum_sq_heavyBinCount_le_of_pair_bound i₀ hpair
  have hsecond' :
      (∑ f : Fin d → Fin q, (heavyBinCount f t : ℝ) ^ 2) ≤ S := by
    simpa only [S, A, N] using hsecond
  have hcardPos : 0 < (binLoadAtLeastEvent (d := d) i₀ t).card := by
    exact_mod_cast hfixed
  obtain ⟨f, hf⟩ := Finset.card_pos.mp hcardPos
  have hfload : t ≤ binLoad f i₀ := (Finset.mem_filter.mp hf).2
  have hfheavy : 0 < heavyBinCount f t := by
    apply Finset.card_pos.mpr
    exact ⟨i₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfload⟩⟩
  have hsq : 0 <
      ∑ f : Fin d → Fin q, (heavyBinCount f t : ℝ) ^ 2 := by
    apply Finset.sum_pos'
    · intro g _
      positivity
    · refine ⟨f, Finset.mem_univ f, ?_⟩
      positivity
  have hdenActual : 0 < N *
      ∑ f : Fin d → Fin q, (heavyBinCount f t : ℝ) ^ 2 :=
    mul_pos hN hsq
  have hdenLe :
      N * (∑ f : Fin d → Fin q, (heavyBinCount f t : ℝ) ^ 2) ≤
        N * S := mul_le_mul_of_nonneg_left hsecond' hN.le
  have hfraction :
      (q * A) ^ 2 / (N * S) ≤
        (∑ f : Fin d → Fin q, (heavyBinCount f t : ℝ)) ^ 2 /
          (N * ∑ f : Fin d → Fin q, (heavyBinCount f t : ℝ) ^ 2) := by
    rw [hfirst]
    exact div_le_div_of_nonneg_left (sq_nonneg _) hdenActual hdenLe
  have hraw := secondMoment_expectedMaxBinLoad_lower_bound hqPos hsq
  dsimp only
  exact (mul_le_mul_of_nonneg_left hfraction (by positivity)).trans (by
    simpa only [N] using hraw)

/-- Union bound for uniform finite sample spaces. -/
theorem uniform_biUnion_bound
    {I Ω : Type*} [Fintype I] [Fintype Ω] [Nonempty Ω]
    [DecidableEq I] [DecidableEq Ω] (Bad : I → Finset Ω) :
    (((Finset.univ.biUnion Bad).card : ℕ) : ℝ) / Fintype.card Ω ≤
      ∑ i, ((Bad i).card : ℝ) / Fintype.card Ω := by
  have hcard : (0 : ℝ) ≤ Fintype.card Ω := by positivity
  have hunion :
      (((Finset.univ.biUnion Bad).card : ℕ) : ℝ) ≤
        ∑ i, ((Bad i).card : ℝ) := by
    exact_mod_cast (Finset.card_biUnion_le :
      (Finset.univ.biUnion Bad).card ≤ ∑ i, (Bad i).card)
  calc
    (((Finset.univ.biUnion Bad).card : ℕ) : ℝ) / Fintype.card Ω ≤
        (∑ i, ((Bad i).card : ℝ)) / Fintype.card Ω :=
      div_le_div_of_nonneg_right hunion hcard
    _ = ∑ i, ((Bad i).card : ℝ) / Fintype.card Ω := by
      rw [Finset.sum_div]

/-- In the balls-and-bins sample space, some allocation attains at least the
expected maximum occupancy. -/
theorem exists_expectedMaxBinLoad_le {q d : ℕ} (hq : 0 < q) :
    ∃ f : Fin d → Fin q,
      expectedMaxBinLoad q d ≤ maxBinLoad f := by
  let i₀ : Fin q := ⟨0, hq⟩
  letI : Nonempty (Fin d → Fin q) := ⟨fun _ ↦ i₀⟩
  simpa only [expectedMaxBinLoad] using
    exists_uniformAverage_le_value
      (fun f : Fin d → Fin q ↦ (maxBinLoad f : ℝ))

/-- Truncated-expectation conclusion of Lemma 4.5 at the level of a finite
bipartite relation.  A bad-event probability at most `W/3` yields one
path-safe global allocation retaining at least `2/3` of the weighted
average edge count. -/
theorem exists_pathSafe_maximizingBinYield
    {B : Type*} [Fintype B]
    (R : Fin d → B → Prop) [DecidableRel R] {q n Δ : ℕ}
    (hq : 0 < q) (hΔ : 0 < Δ)
    (hdegree : ∀ b, relationDegree R b ≤ Δ)
    (hbad :
      (((Finset.univ : Finset (Fin d → Fin q)) \
          pathSafeAllocationEvent q d n).card : ℝ) /
        Fintype.card (Fin d → Fin q) ≤ ballsBinsWeight q Δ / 3) :
    ∃ f ∈ pathSafeAllocationEvent q d n,
      (2 : ℝ) / 3 * (∑ b, (relationDegree R b : ℝ)) *
          ballsBinsWeight q Δ ≤ maximizingBinYield R f := by
  let i₀ : Fin q := ⟨0, hq⟩
  letI : Nonempty (Fin d → Fin q) := ⟨fun _ ↦ i₀⟩
  let Good := pathSafeAllocationEvent q d n
  let M : ℝ := ∑ b, (relationDegree R b : ℝ)
  let W : ℝ := ballsBinsWeight q Δ
  have hWle : W ≤ 1 := ballsBinsWeight_le_one hΔ
  have hbadLt :
      ((((Finset.univ : Finset (Fin d → Fin q)) \ Good).card : ℕ) : ℝ) /
          Fintype.card (Fin d → Fin q) < 1 := by
    have hp : W / 3 < 1 := by linarith
    exact hbad.trans_lt hp
  have hGood : Good.Nonempty :=
    good_nonempty_of_bad_fraction_lt_one Good hbadLt
  have hM : 0 ≤ M := by
    dsimp only [M]
    positivity
  have havg : M * W ≤
      (∑ f : Fin d → Fin q, (maximizingBinYield R f : ℝ)) /
        Fintype.card (Fin d → Fin q) := by
    dsimp only [M, W]
    exact maximizingBinYield_average_lower_bound R hq hΔ hdegree
  have hyield : ∀ f : Fin d → Fin q,
      (maximizingBinYield R f : ℝ) ≤ M := by
    intro f
    dsimp only [M]
    exact_mod_cast maximizingBinYield_le_degreeSum R f
  obtain ⟨f, hfGood, hf⟩ := exists_good_value_of_average_and_bad_bound
    Good hGood (fun f ↦ (maximizingBinYield R f : ℝ))
    (A := M * W) (M := M) (p := W / 3) hM
    (fun _ _ ↦ by positivity) (fun f _ ↦ hyield f) havg hbad
  refine ⟨f, hfGood, ?_⟩
  change (2 : ℝ) / 3 * M * W ≤ maximizingBinYield R f
  calc
    (2 : ℝ) / 3 * M * W = M * W - M * (W / 3) := by ring
    _ ≤ maximizingBinYield R f := hf

/-- The preceding extraction with all v1 numerical hypotheses discharged
and the literal floor/ceiling bin count substituted. -/
theorem exists_subgraphFinding_safe_allocation
    {r n v Δ : ℕ} {B : Type*} [Fintype B]
    (R : Fin ((v + 1) / 2) → B → Prop) [DecidableRel R]
    (hr : 21 ≤ r)
    (hn : 100 * Real.log (r : ℝ) ≤ (n : ℝ))
    (hv : (v : ℝ) ≤ 2 * (r * Real.log (r : ℝ)) * n)
    (hqTwo : 2 ≤ subgraphFindingBinCount n v) (hΔ : 0 < Δ)
    (hdegree : ∀ b, relationDegree R b ≤ Δ) :
    let a := (v + 1) / 2
    let q := subgraphFindingBinCount n v
    ∃ f ∈ pathSafeAllocationEvent q a n,
      (2 : ℝ) / 3 * (∑ b, (relationDegree R b : ℝ)) *
          ballsBinsWeight q Δ ≤ maximizingBinYield R f := by
  let a := (v + 1) / 2
  let q := subgraphFindingBinCount n v
  have hq : 0 < q := by dsimp only [q]; omega
  have hbad := subgraphFinding_bad_fraction_le_weight_div_three
    hr hn hv hqTwo hΔ
  dsimp only at hbad ⊢
  exact exists_pathSafe_maximizingBinYield R hq hΔ hdegree hbad

/-- Deterministic companion to `exists_subgraphFinding_safe_allocation` for
the only remaining positive small-bin case. -/
theorem exists_subgraphFinding_safe_allocation_one_bin
    {n v Δ : ℕ} {B : Type*} [Fintype B]
    (R : Fin ((v + 1) / 2) → B → Prop) [DecidableRel R]
    (hn : 0 < n) (hqOne : subgraphFindingBinCount n v = 1)
    (hΔ : 0 < Δ) :
    let a := (v + 1) / 2
    let q := subgraphFindingBinCount n v
    ∃ f ∈ pathSafeAllocationEvent q a n,
      (2 : ℝ) / 3 * (∑ b, (relationDegree R b : ℝ)) *
          ballsBinsWeight q Δ ≤ maximizingBinYield R f := by
  have hsmall := subgraphFinding_one_bin_small hn hqOne
  have h := exists_pathSafe_maximizingBinYield_one_bin R hsmall hΔ
  dsimp only
  rw [hqOne]
  exact h

/-! ## Deterministic colouring from a free edge cover -/

/-- Every edge of `G` belongs to at least one graph in the family `H`.  The
graphs in the family may contain additional edges; only their behaviour on
the edge set of `G` matters. -/
def EdgesCoveredBy (G : SimpleGraph V) (H : K → SimpleGraph V) : Prop :=
  ∀ e : Sym2 V, e ∈ G.edgeSet → ∃ i : K, e ∈ (H i).edgeSet

/-- Colour an edge by one member of a covering family that contains it. -/
def coloringOfCover (G : SimpleGraph V) (H : K → SimpleGraph V)
    (hcover : EdgesCoveredBy G H) : G.EdgeLabeling K :=
  fun e ↦ Classical.choose (hcover e.1 e.2)

@[simp]
theorem coloringOfCover_edge_mem (G : SimpleGraph V)
    (H : K → SimpleGraph V) (hcover : EdgesCoveredBy G H)
    (e : G.edgeSet) :
    e.1 ∈ (H (coloringOfCover G H hcover e)).edgeSet := by
  exact Classical.choose_spec (hcover e.1 e.2)

/-- A colour class selected from a cover is a subgraph of its corresponding
covering graph. -/
theorem labelGraph_coloringOfCover_le (G : SimpleGraph V)
    (H : K → SimpleGraph V) (hcover : EdgesCoveredBy G H) (i : K) :
    (coloringOfCover G H hcover).labelGraph i ≤ H i := by
  intro x y hxy
  rw [EdgeLabeling.labelGraph_adj] at hxy
  obtain ⟨hG, hi⟩ := hxy
  have hmem := coloringOfCover_edge_mem G H hcover
    (⟨s(x, y), hG⟩ : G.edgeSet)
  rw [hi] at hmem
  simpa only [mem_edgeSet] using hmem

/-- A cover by `F`-free graphs produces a colouring with no monochromatic
copy of `F`.  This is the deterministic interface used by every subsequent
decomposition and random-existence argument in the paper. -/
theorem coloringOfCover_avoidsMonochromaticCopy
    (F : SimpleGraph W) (G : SimpleGraph V) (H : K → SimpleGraph V)
    (hcover : EdgesCoveredBy G H) (hfree : ∀ i, F.Free (H i)) :
    AvoidsMonochromaticCopy F (coloringOfCover G H hcover) := by
  intro i hcopy
  exact hfree i (hcopy.trans_le (labelGraph_coloringOfCover_le G H hcover i))

/-- Existential form of `coloringOfCover_avoidsMonochromaticCopy`, matching
the witness required by the size--Ramsey lower-bound predicate. -/
theorem exists_avoidingColoring_of_free_cover
    (F : SimpleGraph W) (G : SimpleGraph V) (H : K → SimpleGraph V)
    (hcover : EdgesCoveredBy G H) (hfree : ∀ i, F.Free (H i)) :
    ∃ C : G.EdgeLabeling K, AvoidsMonochromaticCopy F C :=
  ⟨coloringOfCover G H hcover,
    coloringOfCover_avoidsMonochromaticCopy F G H hcover hfree⟩

/-! ## First path-free building block -/

/-- A graph on fewer than `n` vertices cannot contain the `n`-vertex path.
This is the cardinality fact used whenever a colour class is decomposed into
small vertex-supported pieces. -/
theorem pathGraph_free_of_card_lt [Finite V] (G : SimpleGraph V) {n : ℕ}
    (hcard : Nat.card V < n) : (pathGraph n).Free G := by
  intro hcopy
  obtain ⟨f⟩ := hcopy
  have hle : Nat.card (Fin n) ≤ Nat.card V :=
    Nat.card_le_card_of_injective f f.injective
  simp only [Nat.card_fin] at hle
  omega

/-! ## The path bound behind star-type colouring -/

/-- `S` meets every edge of `G`. -/
def IsVertexCover (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ ⦃x y : V⦄, G.Adj x y → x ∈ S ∨ y ∈ S

/-- Along a list in which every consecutive pair meets `P`, the list has at
most twice as many entries satisfying `P`, plus one. -/
private theorem length_le_two_mul_filter_length_add_one
    (P : V → Prop) [DecidablePred P] (l : List V)
    (hchain : l.IsChain fun x y ↦ P x ∨ P y) :
    l.length ≤ 2 * (l.filter P).length + 1 := by
  induction l using List.twoStepInduction with
  | nil => simp
  | singleton x => simp
  | cons_cons x y l ih _ =>
      have hxy : P x ∨ P y := hchain.rel_head
      have htail : l.IsChain fun x y ↦ P x ∨ P y := hchain.tail.tail
      have hrec := ih htail
      by_cases hx : P x <;> by_cases hy : P y <;>
        simp [hx, hy] at * <;>
        omega

/-- Any vertex cover of a graph containing `P_n` has size at least
`(n - 1) / 2`.  The division-free conclusion is exactly what the star-type
colouring needs. -/
theorem card_bound_of_pathGraph_isContained_of_vertexCover [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) {n : ℕ}
    (hcover : IsVertexCover G S) (hpath : pathGraph n ⊑ G) :
    n ≤ 2 * S.card + 1 := by
  obtain ⟨f⟩ := hpath
  let l : List V := List.ofFn f
  have hchain : l.IsChain fun x y ↦ x ∈ S ∨ y ∈ S := by
    dsimp only [l]
    rw [List.isChain_ofFn]
    intro i hi
    apply hcover
    apply f.toHom.map_adj
    rw [pathGraph_adj]
    exact Or.inl rfl
  have hlist := length_le_two_mul_filter_length_add_one
    (fun x ↦ x ∈ S) l hchain
  have hl_nodup : l.Nodup := by
    exact List.nodup_ofFn.mpr f.injective
  have hfilter_nodup : (l.filter fun x ↦ x ∈ S).Nodup :=
    hl_nodup.filter _
  have hfilter_subset :
      (l.filter fun x ↦ x ∈ S).toFinset ⊆ S := by
    intro x hx
    have hx' : x ∈ l.filter fun x ↦ x ∈ S := by simpa using hx
    simpa using (List.mem_filter.mp hx').2
  have hfilter_card : (l.filter fun x ↦ x ∈ S).length ≤ S.card := by
    rw [← List.toFinset_card_of_nodup hfilter_nodup]
    exact Finset.card_le_card hfilter_subset
  simpa only [l, List.length_ofFn] using
    hlist.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hfilter_card) 1)

/-- If a colour class has a vertex cover `S` with `2|S| + 1 < n`, it is
`P_n`-free.  This closes the combinatorial part of Lemma 2.3 independently
of its degree-counting and colour-budget arithmetic. -/
theorem pathGraph_free_of_small_vertexCover [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) {n : ℕ}
    (hcover : IsVertexCover G S) (hsmall : 2 * S.card + 1 < n) :
    (pathGraph n).Free G := by
  intro hpath
  have := card_bound_of_pathGraph_isContained_of_vertexCover G S hcover hpath
  omega

/-- The subgraph consisting of the edges of `G` incident to `S`. -/
def incidentSubgraph (G : SimpleGraph V) (S : Finset V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ (x ∈ S ∨ y ∈ S)
  symm.symm x y hxy := ⟨hxy.1.symm, hxy.2.elim Or.inr Or.inl⟩

@[simp]
theorem incidentSubgraph_adj (G : SimpleGraph V) (S : Finset V) {x y : V} :
    (incidentSubgraph G S).Adj x y ↔ G.Adj x y ∧ (x ∈ S ∨ y ∈ S) :=
  Iff.rfl

instance [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (S : Finset V) : DecidableRel (incidentSubgraph G S).Adj :=
  inferInstanceAs (DecidableRel fun x y ↦ G.Adj x y ∧ (x ∈ S ∨ y ∈ S))

theorem incidentSubgraph_le (G : SimpleGraph V) (S : Finset V) :
    incidentSubgraph G S ≤ G :=
  fun _ _ h ↦ h.1

theorem incidentSubgraph_vertexCover (G : SimpleGraph V) (S : Finset V) :
    IsVertexCover (incidentSubgraph G S) S :=
  by
    intro x y hxy
    exact hxy.2

/-- A graph split into vertex-disjoint groups is `P_n`-free when every edge
stays inside one group and the edges of each group have a sufficiently small
vertex cover.  This is the precise deterministic fact behind the union
`G[A₁,B₁] ∪ ... ∪ G[A_q,B_q]` in Lemma 4.5. -/
theorem pathGraph_free_of_grouped_vertexCovers [DecidableEq V]
    (G : SimpleGraph V) {q n : ℕ} (hq : 0 < q)
    (group : V → Fin q) (S : Fin q → Finset V)
    (hadj : ∀ ⦃x y⦄, G.Adj x y →
      group x = group y ∧
        (x ∈ S (group x) ∨ y ∈ S (group y)))
    (hsmall : ∀ i, 2 * (S i).card + 1 < n) :
    (pathGraph n).Free G := by
  intro hpath
  obtain ⟨f⟩ := hpath
  cases n with
  | zero =>
      have := hsmall (⟨0, hq⟩ : Fin q)
      omega
  | succ m =>
      let i₀ : Fin q := group (f (0 : Fin (m + 1)))
      have hall : ∀ j : Fin (m + 1), group (f j) = i₀ := by
        intro j
        induction j using Fin.induction with
        | zero => rfl
        | succ j ih =>
            have hp : (pathGraph (m + 1)).Adj j.castSucc j.succ := by
              rw [pathGraph_adj]
              exact Or.inl rfl
            have hG : G.Adj (f j.castSucc) (f j.succ) :=
              f.toHom.map_adj hp
            exact (hadj hG).1.symm.trans ih
      let f' : Copy (pathGraph (m + 1))
          (incidentSubgraph G (S i₀)) :=
        { toHom :=
            { toFun := f
              map_rel' := by
                intro x y hxy
                have hG : G.Adj (f x) (f y) := f.toHom.map_adj hxy
                refine ⟨hG, ?_⟩
                obtain ⟨_, hcover⟩ := hadj hG
                rcases hcover with hx | hy
                · exact Or.inl (by simpa only [hall x] using hx)
                · exact Or.inr (by simpa only [hall y] using hy) }
          injective' := f.injective }
      have hbound := card_bound_of_pathGraph_isContained_of_vertexCover
        (incidentSubgraph G (S i₀)) (S i₀)
        (incidentSubgraph_vertexCover G (S i₀)) (show pathGraph (m + 1) ⊑
          incidentSubgraph G (S i₀) from ⟨f'⟩)
      have := hsmall i₀
      omega

/-- If a vertex cover is split among small centre sets, colouring an edge by
one centre set containing an endpoint produces no monochromatic `P_n`.
This is the deterministic heart of the paper's Lemma 2.3. -/
theorem exists_starColoring_of_partition [DecidableEq V]
    (G : SimpleGraph V) {s n : ℕ} (S : Finset V)
    (P : Fin s → Finset V) (hcover : IsVertexCover G S)
    (hpartition : ∀ x ∈ S, ∃ i, x ∈ P i)
    (hsmall : ∀ i, 2 * (P i).card + 1 < n) :
    ∃ C : G.EdgeLabeling (Fin s),
      AvoidsMonochromaticCopy (pathGraph n) C := by
  let H : Fin s → SimpleGraph V := fun i ↦ incidentSubgraph G (P i)
  have hHcover : EdgesCoveredBy G H := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ x y =>
        have hxy : G.Adj x y := by simpa only [mem_edgeSet] using he
        obtain hx | hy := hcover hxy
        · obtain ⟨i, hxi⟩ := hpartition x hx
          refine ⟨i, ?_⟩
          simpa only [mem_edgeSet, H, incidentSubgraph_adj] using
            (show G.Adj x y ∧ (x ∈ P i ∨ y ∈ P i) from ⟨hxy, Or.inl hxi⟩)
        · obtain ⟨i, hyi⟩ := hpartition y hy
          refine ⟨i, ?_⟩
          simpa only [mem_edgeSet, H, incidentSubgraph_adj] using
            (show G.Adj x y ∧ (x ∈ P i ∨ y ∈ P i) from ⟨hxy, Or.inr hyi⟩)
  apply exists_avoidingColoring_of_free_cover (pathGraph n) G H hHcover
  intro i
  exact pathGraph_free_of_small_vertexCover (H i) (P i)
    (incidentSubgraph_vertexCover G (P i)) (hsmall i)

/-- A finite set of size at most `s * b` can be split among `s` labelled
parts of size at most `b`.  We construct the labels by embedding the set into
`Fin (s*b)` and taking quotient by `b`; the remainder proves the fibre bound.
-/
private theorem exists_small_labelled_cover [DecidableEq V]
    (S : Finset V) {s b : ℕ} (_hs : 0 < s) (hb : 0 < b)
    (hcard : S.card ≤ s * b) :
    ∃ P : Fin s → Finset V,
      (∀ x ∈ S, ∃ i, x ∈ P i) ∧ (∀ i, (P i).card ≤ b) := by
  classical
  have hcard' : Fintype.card (↑S : Type u) ≤ Fintype.card (Fin (s * b)) := by
    simpa only [Fintype.card_coe, Fintype.card_fin] using hcard
  let e : (↑S : Type u) ↪ Fin (s * b) :=
    (Function.Embedding.nonempty_of_card_le hcard').some
  let colour : (↑S : Type u) → Fin s := fun x ↦
    ⟨(e x).val / b, (Nat.div_lt_iff_lt_mul hb).mpr (e x).isLt⟩
  let P : Fin s → Finset V := fun i ↦
    S.filter fun x ↦ ∃ hx : x ∈ S, colour ⟨x, hx⟩ = i
  refine ⟨P, ?_, ?_⟩
  · intro x hxS
    refine ⟨colour ⟨x, hxS⟩, ?_⟩
    simp [P, hxS]
  · intro i
    let remainder : (↑(P i) : Type u) → Fin b := fun x ↦
      ⟨(e ⟨x.1, (Finset.mem_filter.mp x.2).1⟩).val % b,
        Nat.mod_lt _ hb⟩
    have hremainder : Function.Injective remainder := by
      intro x y hxy
      have hxS : x.1 ∈ S := (Finset.mem_filter.mp x.2).1
      have hyS : y.1 ∈ S := (Finset.mem_filter.mp y.2).1
      obtain ⟨_, hxc⟩ := (Finset.mem_filter.mp x.2).2
      obtain ⟨_, hyc⟩ := (Finset.mem_filter.mp y.2).2
      have hxc' : colour ⟨x.1, hxS⟩ = i := by simpa using hxc
      have hyc' : colour ⟨y.1, hyS⟩ = i := by simpa using hyc
      have hdiv : (e ⟨x.1, hxS⟩).val / b =
          (e ⟨y.1, hyS⟩).val / b := by
        have := congrArg Fin.val (hxc'.trans hyc'.symm)
        simpa only [colour] using this
      have hmod : (e ⟨x.1, hxS⟩).val % b =
          (e ⟨y.1, hyS⟩).val % b := by
        have hmod' := congrArg Fin.val hxy
        simpa only [remainder] using hmod'
      have heval : (e ⟨x.1, hxS⟩).val =
          (e ⟨y.1, hyS⟩).val := by
        calc
          (e ⟨x.1, hxS⟩).val =
              (e ⟨x.1, hxS⟩).val % b +
                b * ((e ⟨x.1, hxS⟩).val / b) :=
            (Nat.mod_add_div _ _).symm
          _ = (e ⟨y.1, hyS⟩).val % b +
                b * ((e ⟨y.1, hyS⟩).val / b) := by rw [hmod, hdiv]
          _ = (e ⟨y.1, hyS⟩).val := Nat.mod_add_div _ _
      have hsub : (⟨x.1, hxS⟩ : ↑S) = ⟨y.1, hyS⟩ := by
        apply e.injective
        exact Fin.ext heval
      have hval : x.1 = y.1 :=
        congrArg (fun z : (↑S : Type u) ↦ z.1) hsub
      exact Subtype.ext hval
    have hle := Fintype.card_le_of_injective remainder hremainder
    simpa only [Fintype.card_coe, Fintype.card_fin] using hle

/-- Star-type colouring from a small vertex cover.  The paper applies this
with the set of high-degree vertices.  The harmless `n >= 12` assumption is
far weaker than the retained main threshold `n >= 100 log r`. -/
theorem exists_starColoring_of_small_vertexCover [DecidableEq V]
    (G : SimpleGraph V) {s n : ℕ} (hs : 0 < s) (hn : 12 ≤ n)
    (S : Finset V) (hcover : IsVertexCover G S)
    (hcard : 4 * S.card ≤ s * n) :
    ∃ C : G.EdgeLabeling (Fin s),
      AvoidsMonochromaticCopy (pathGraph n) C := by
  have hb : 0 < n / 3 := by omega
  have hn_capacity : n ≤ 4 * (n / 3) := by omega
  have hcapacity : S.card ≤ s * (n / 3) := by
    by_contra h
    have hlt : s * (n / 3) < S.card := by omega
    have hmul : 4 * (s * (n / 3)) < 4 * S.card :=
      (Nat.mul_lt_mul_left (by omega : 0 < 4)).mpr hlt
    have hsn : s * n ≤ 4 * (s * (n / 3)) := by
      calc
        s * n ≤ s * (4 * (n / 3)) := Nat.mul_le_mul_left s hn_capacity
        _ = 4 * (s * (n / 3)) := by ring
    omega
  obtain ⟨P, hpartition, hPcard⟩ :=
    exists_small_labelled_cover S hs hb hcapacity
  apply exists_starColoring_of_partition G S P hcover hpartition
  intro i
  have hi := hPcard i
  have hthird : 2 * (n / 3) + 1 < n := by omega
  omega

/-! ## High-degree removal (the counting half of Lemma 2.3) -/

/-- Vertices whose degree is strictly above the star-colouring cut-off.  A
strict inequality makes the zero-edge case canonical: the set is then empty.
-/
def highDegreeVertices [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (s n : ℕ) : Finset V :=
  Finset.univ.filter fun v ↦
    8 * edgeCount G < n * s * G.degree v

@[simp]
theorem mem_highDegreeVertices [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (s n : ℕ) (v : V) :
    v ∈ highDegreeVertices G s n ↔
      8 * edgeCount G < n * s * G.degree v := by
  simp [highDegreeVertices]

private theorem edgeCount_eq_edgeFinset_card [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    edgeCount G = G.edgeFinset.card := by
  rw [edgeCount, Nat.card_eq_fintype_card, G.card_edgeSet]

/-- Double-counting the incidences at high-degree vertices gives exactly the
cardinality estimate used in Lemma 2.3. -/
theorem four_mul_card_highDegreeVertices_le [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s n : ℕ) :
    4 * (highDegreeVertices G s n).card ≤ s * n := by
  classical
  let S := highDegreeVertices G s n
  let E := G.edgeFinset.card
  by_cases hS : S.Nonempty
  · have hv : ∀ v ∈ S, 8 * E < n * s * G.degree v := by
      intro v hvS
      have := (mem_highDegreeVertices G s n v).mp (by simpa [S] using hvS)
      simpa only [edgeCount_eq_edgeFinset_card G, E] using this
    have hsum : (∑ _v ∈ S, 8 * E) <
        ∑ v ∈ S, n * s * G.degree v :=
      Finset.sum_lt_sum_of_nonempty hS hv
    have hdegree : (∑ v ∈ S, G.degree v) ≤ ∑ v, G.degree v :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ S)
    have htotal : (4 * S.card) * (2 * E) < (n * s) * (2 * E) := by
      calc
        (4 * S.card) * (2 * E) = ∑ _v ∈ S, 8 * E := by
          simp
          ring
        _ < ∑ v ∈ S, n * s * G.degree v := hsum
        _ = (n * s) * ∑ v ∈ S, G.degree v := by
          rw [Finset.mul_sum]
        _ ≤ (n * s) * ∑ v, G.degree v :=
          Nat.mul_le_mul_left (n * s) hdegree
        _ = (n * s) * (2 * E) := by
          rw [G.sum_degrees_eq_twice_card_edges]
    have hcard_strict : 4 * S.card < n * s := by
      by_contra h
      have hreverse : (n * s) * (2 * E) ≤ (4 * S.card) * (2 * E) :=
        Nat.mul_le_mul_right (2 * E) (by omega)
      omega
    simpa only [S, Nat.mul_comm s n] using hcard_strict.le
  · have : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp [S, this]

/-- Lemma 2.3 in decomposition form.  `H` is the part coloured by the
star-type colouring and `R` is the uncoloured remainder.  The maximum-degree
bound is the paper's `8e(G)/(ns)`, using natural-number division. -/
theorem exists_starTypeDecomposition [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {s n : ℕ} (hs : 0 < s) (hn : 12 ≤ n) :
    ∃ H R : SimpleGraph V,
      H ≤ G ∧ R ≤ G ∧ G = H ⊔ R ∧
      (∀ v, Nat.card (R.neighborSet v) ≤
        8 * edgeCount G / (n * s)) ∧
      ∃ C : H.EdgeLabeling (Fin s),
        AvoidsMonochromaticCopy (pathGraph n) C := by
  let S := highDegreeVertices G s n
  let H := incidentSubgraph G S
  let R := G \ H
  letI : DecidableRel R.Adj := Classical.decRel _
  have hHle : H ≤ G := incidentSubgraph_le G S
  have hRle : R ≤ G := by
    exact sdiff_le
  have hdegree : ∀ v, n * s * R.degree v ≤ 8 * edgeCount G := by
    intro v
    by_cases hvS : v ∈ S
    · have hd0 : R.degree v = 0 := by
        rw [R.degree_eq_zero_iff_notMem_support]
        intro hvSupport
        rw [mem_support] at hvSupport
        obtain ⟨w, hvw⟩ := hvSupport
        have hvw' := (sdiff_adj G H v w).mp hvw
        apply hvw'.2
        exact ⟨hvw'.1, Or.inl hvS⟩
      simp only [hd0, mul_zero, Nat.zero_le]
    · have hlowG : n * s * G.degree v ≤ 8 * edgeCount G := by
        have hvNotHigh : ¬8 * edgeCount G < n * s * G.degree v := by
          simpa only [S, mem_highDegreeVertices, not_lt] using hvS
        omega
      exact (Nat.mul_le_mul_left (n * s) (R.degree_le_of_le hRle)).trans hlowG
  have hns : 0 < n * s := Nat.mul_pos (by omega) hs
  have hmax : ∀ v, Nat.card (R.neighborSet v) ≤
      8 * edgeCount G / (n * s) := by
    intro v
    rw [Nat.card_eq_fintype_card, R.card_neighborSet_eq_degree]
    apply (Nat.le_div_iff_mul_le hns).mpr
    simpa only [Nat.mul_comm] using hdegree v
  have hcard : 4 * S.card ≤ s * n := by
    simpa only [S] using four_mul_card_highDegreeVertices_le G s n
  have hScover : IsVertexCover H S := incidentSubgraph_vertexCover G S
  obtain ⟨C, hC⟩ :=
    exists_starColoring_of_small_vertexCover H hs hn S hScover hcard
  refine ⟨H, R, hHle, hRle, ?_, hmax, C, hC⟩
  exact (sup_sdiff_cancel_right hHle).symm

end

end LeanCo.SizeRamsey
