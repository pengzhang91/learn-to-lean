import LeanCo.InversionDescent.GaussianFactorial
import LeanCo.Rascoe.FormalSeries
import LeanCo.Rascoe.QPochhammer
import Mathlib.Data.Fin.Tuple.NatAntidiagonal
import Mathlib.RingTheory.PowerSeries.PiTopology

/-!
# The two finite-coefficient double sums for Rascoe partitions

The paper writes the Rascoe inner index as `0 ≤ m ≤ n`, with the `m=n`
term killed by a Gaussian coefficient with lower index `-1`.  Since natural
number subtraction truncates in Lean, this file uses the equivalent and
literal range `m<n`.  The non-Rascoe sum genuinely uses `m≤n`.

The first part of the file records the decomposition of the *literal*
`Nat.Partition` counts by length and by the number of parts above the length.
The second part defines the locally finite formal-power-series realization of
the two displayed Gaussian/q-Pochhammer double sums.
-/

open scoped BigOperators PowerSeries.WithPiTopology
open Finset PowerSeries PowerSeries.WithPiTopology

namespace LeanCo.RectanglePartition

/-- Ferrers conjugation for a zero-padded rectangle partition. -/
noncomputable def transpose {rows cols : ℕ} (p : RectanglePartition rows cols) :
    RectanglePartition cols rows := by
  classical
  refine ⟨fun j ↦
    ⟨(Finset.univ.filter fun i : Fin rows ↦ j.1 < (p.1 i).1).card, ?_⟩, ?_⟩
  · have hle :
        (Finset.univ.filter fun i : Fin rows ↦ j.1 < (p.1 i).1).card ≤ rows := by
      simpa using Finset.card_filter_le (Finset.univ : Finset (Fin rows))
        (fun i : Fin rows ↦ j.1 < (p.1 i).1)
    omega
  · intro j k hjk
    change (Finset.univ.filter fun i : Fin rows ↦ k.1 < (p.1 i).1).card ≤
      (Finset.univ.filter fun i : Fin rows ↦ j.1 < (p.1 i).1).card
    apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact lt_of_le_of_lt (by simpa using hjk) hi

@[simp] theorem transpose_transpose {rows cols : ℕ}
    (p : RectanglePartition rows cols) :
    transpose (transpose p) = p := by
  classical
  apply Subtype.ext
  funext i
  apply Fin.ext
  change (Finset.univ.filter fun j : Fin cols ↦
      i.1 < (Finset.univ.filter fun k : Fin rows ↦ j.1 < (p.1 k).1).card).card =
    (p.1 i).1
  have hpred :
      (Finset.univ.filter fun j : Fin cols ↦
          i.1 < (Finset.univ.filter fun k : Fin rows ↦ j.1 < (p.1 k).1).card) =
        (Finset.univ.filter fun j : Fin cols ↦ j.1 < (p.1 i).1) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Tuple.lt_card_gt_iff_apply_gt_of_antitone p.2
  rw [hpred, Fin.card_filter_val_lt]
  exact Nat.min_eq_right (Nat.le_of_lt_succ (p.1 i).isLt)

/-- Ferrers conjugation as an equivalence between the two rectangle
orientations. -/
noncomputable def transposeEquiv (rows cols : ℕ) :
    RectanglePartition rows cols ≃ RectanglePartition cols rows where
  toFun := transpose
  invFun := transpose
  left_inv := transpose_transpose
  right_inv := transpose_transpose

@[simp] theorem weight_transpose {rows cols : ℕ}
    (p : RectanglePartition rows cols) :
    (transpose p).weight = p.weight := by
  classical
  simp only [weight, transpose]
  calc
    ∑ j : Fin cols,
        (Finset.univ.filter fun i : Fin rows ↦ j.1 < (p.1 i).1).card =
        ∑ j : Fin cols, ∑ i : Fin rows, if j.1 < (p.1 i).1 then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro j hj
          simp [Finset.sum_boole]
    _ = ∑ i : Fin rows, ∑ j : Fin cols,
        if j.1 < (p.1 i).1 then 1 else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ i : Fin rows,
        (Finset.univ.filter fun j : Fin cols ↦ j.1 < (p.1 i).1).card := by
          apply Finset.sum_congr rfl
          intro i hi
          simp [Finset.sum_boole]
    _ = ∑ i : Fin rows, (p.1 i).1 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Fin.card_filter_val_lt]
          exact Nat.min_eq_right (Nat.le_of_lt_succ (p.1 i).isLt)

end LeanCo.RectanglePartition

namespace LeanCo.Rascoe

/-! ## Literal finite layers of partitions -/

/-- Number of parts of `p` strictly larger than the proposed length `n`. -/
def aboveLengthCount {d : ℕ} (n : ℕ) (p : Nat.Partition d) : ℕ :=
  (p.parts.filter (n < ·)).card

/-- A literal Rascoe layer: total size `d`, length `n`, and exactly `m` parts
strictly larger than `n`. -/
noncomputable def rascoeLayer (d n m : ℕ) : Finset (Nat.Partition d) :=
  by
    classical
    exact Finset.univ.filter fun p ↦
      IsRascoe p ∧ length p = n ∧ aboveLengthCount n p = m

/-- A literal non-Rascoe layer with the same two statistics. -/
noncomputable def nonRascoeLayer (d n m : ℕ) : Finset (Nat.Partition d) :=
  by
    classical
    exact Finset.univ.filter fun p ↦
      IsNonRascoe p ∧ length p = n ∧ aboveLengthCount n p = m

/-- A multiset of positive naturals has at least as much total mass as
cardinality. -/
theorem multiset_card_le_sum_of_pos (s : Multiset ℕ)
    (hs : ∀ x ∈ s, 0 < x) :
    s.card ≤ s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
      have ha : 0 < a := hs a (by simp)
      have hs' : ∀ x ∈ s, 0 < x := by
        intro x hx
        exact hs x (by simp [hx])
      have hih := ih hs'
      simp only [Multiset.card_cons, Multiset.sum_cons]
      omega

theorem length_le_size {d : ℕ} (p : Nat.Partition d) :
    length p ≤ d := by
  simpa [length, p.parts_sum] using
    multiset_card_le_sum_of_pos p.parts (fun x hx ↦ p.parts_pos hx)

theorem aboveLengthCount_le_length {d n : ℕ} (p : Nat.Partition d) :
    aboveLengthCount n p ≤ length p := by
  exact Multiset.card_le_card (Multiset.filter_le _ _)

/-- In a Rascoe layer the number of parts above the length is strictly less
than the length, because one occurrence of the length itself is left over. -/
theorem aboveLengthCount_lt_length_of_rascoe {d : ℕ}
    (p : Nat.Partition d) (hp : IsRascoe p) :
    aboveLengthCount (length p) p < length p := by
  let hi := p.parts.filter (length p < ·)
  let hlo := p.parts.filter (fun x ↦ ¬length p < x)
  have hsplit : hi + hlo = p.parts := by
    simpa [hi, hlo] using
      (Multiset.filter_add_not (fun x ↦ length p < x) p.parts)
  have hmem : length p ∈ hlo := by
    change length p ∈ p.parts at hp
    exact Multiset.mem_filter.mpr ⟨hp, lt_irrefl _⟩
  have hloPos : 0 < hlo.card := Multiset.card_pos.mpr (by
    intro hzero
    rw [hzero] at hmem
    simpa using hmem)
  have hcard := congrArg Multiset.card hsplit
  simp only [Multiset.card_add] at hcard
  change hi.card < p.parts.card
  omega

theorem aboveLengthCount_lt_of_rascoe_length_eq {d n : ℕ}
    (p : Nat.Partition d) (hp : IsRascoe p) (hlen : length p = n) :
    aboveLengthCount n p < n := by
  subst n
  exact aboveLengthCount_lt_length_of_rascoe p hp

/-- Literal Rascoe partitions split disjointly by `(length, aboveLengthCount)`.
Both sums are finite; the bounds follow from positivity of partition parts. -/
theorem rascoeNumber_eq_sum_layers (d : ℕ) :
    rascoeNumber d =
      ∑ n ∈ Finset.range (d + 1),
        ∑ m ∈ Finset.range n, (rascoeLayer d n m).card := by
  classical
  let s : Finset (Nat.Partition d) := Finset.univ.filter IsRascoe
  have hlenMaps : (s : Set (Nat.Partition d)).MapsTo length
      (Finset.range (d + 1)) := by
    intro p hp
    simp only [Finset.mem_coe, Finset.mem_range]
    exact Nat.lt_succ_of_le (length_le_size p)
  calc
    rascoeNumber d = s.card := by
      let e : RascoePartition d ≃ ↥s := {
        toFun p := ⟨p.1, by simp [s, p.2]⟩
        invFun p := ⟨p.1, by
          have hp : p.1 ∈ Finset.univ.filter IsRascoe := by
            simpa only [s] using p.2
          exact (Finset.mem_filter.mp hp).2⟩
        left_inv p := by cases p; rfl
        right_inv p := by cases p; rfl
      }
      simpa [rascoeNumber] using Fintype.card_congr e
    _ = ∑ n ∈ Finset.range (d + 1),
          #{p ∈ s | length p = n} :=
      Finset.card_eq_sum_card_fiberwise hlenMaps
    _ = ∑ n ∈ Finset.range (d + 1),
          ∑ m ∈ Finset.range n, (rascoeLayer d n m).card := by
      apply Finset.sum_congr rfl
      intro n hn
      let sn : Finset (Nat.Partition d) := s.filter fun p ↦ length p = n
      have hmMaps : (sn : Set (Nat.Partition d)).MapsTo
          (aboveLengthCount n) (Finset.range n) := by
        intro p hp
        simp only [Finset.mem_coe, Finset.mem_range]
        have hps : p ∈ s := (Finset.mem_filter.mp hp).1
        have hlen : length p = n := (Finset.mem_filter.mp hp).2
        have hrascoe : IsRascoe p := (Finset.mem_filter.mp hps).2
        exact aboveLengthCount_lt_of_rascoe_length_eq p hrascoe hlen
      rw [show #{p ∈ s | length p = n} = sn.card by rfl]
      rw [Finset.card_eq_sum_card_fiberwise hmMaps]
      apply Finset.sum_congr rfl
      intro m hm
      apply congrArg Finset.card
      ext p
      simp [sn, s, rascoeLayer, and_assoc]

/-- Literal non-Rascoe partitions split by the same statistics.  Here all
parts may be above the length, so the correct inner range is `m≤n`. -/
theorem nonRascoeNumber_eq_sum_layers (d : ℕ) :
    nonRascoeNumber d =
      ∑ n ∈ Finset.range (d + 1),
        ∑ m ∈ Finset.range (n + 1), (nonRascoeLayer d n m).card := by
  classical
  let s : Finset (Nat.Partition d) := Finset.univ.filter IsNonRascoe
  have hlenMaps : (s : Set (Nat.Partition d)).MapsTo length
      (Finset.range (d + 1)) := by
    intro p hp
    simp only [Finset.mem_coe, Finset.mem_range]
    exact Nat.lt_succ_of_le (length_le_size p)
  calc
    nonRascoeNumber d = s.card := by
      let e : NonRascoePartition d ≃ ↥s := {
        toFun p := ⟨p.1, by simp [s, p.2]⟩
        invFun p := ⟨p.1, by
          have hp : p.1 ∈ Finset.univ.filter IsNonRascoe := by
            simpa only [s] using p.2
          exact (Finset.mem_filter.mp hp).2⟩
        left_inv p := by cases p; rfl
        right_inv p := by cases p; rfl
      }
      simpa [nonRascoeNumber] using Fintype.card_congr e
    _ = ∑ n ∈ Finset.range (d + 1),
          #{p ∈ s | length p = n} :=
      Finset.card_eq_sum_card_fiberwise hlenMaps
    _ = ∑ n ∈ Finset.range (d + 1),
          ∑ m ∈ Finset.range (n + 1), (nonRascoeLayer d n m).card := by
      apply Finset.sum_congr rfl
      intro n hn
      let sn : Finset (Nat.Partition d) := s.filter fun p ↦ length p = n
      have hmMaps : (sn : Set (Nat.Partition d)).MapsTo
          (aboveLengthCount n) (Finset.range (n + 1)) := by
        intro p hp
        simp only [Finset.mem_coe, Finset.mem_range]
        have hlen : length p = n := (Finset.mem_filter.mp hp).2
        exact Nat.lt_succ_of_le (by
          rw [← hlen]
          exact aboveLengthCount_le_length p)
      rw [show #{p ∈ s | length p = n} = sn.card by rfl]
      rw [Finset.card_eq_sum_card_fiberwise hmMaps]
      apply Finset.sum_congr rfl
      intro m hm
      apply congrArg Finset.card
      ext p
      simp [sn, s, nonRascoeLayer, and_assoc]

/-- The coefficientwise series obtained directly from the literal Rascoe
layers. -/
noncomputable def literalRascoeDoubleSeries : ℤ⟦X⟧ :=
  PowerSeries.mk fun d ↦
    ∑ n ∈ Finset.range (d + 1),
      ∑ m ∈ Finset.range n, ((rascoeLayer d n m).card : ℤ)

/-- The analogous literal non-Rascoe layer series. -/
noncomputable def literalNonRascoeDoubleSeries : ℤ⟦X⟧ :=
  PowerSeries.mk fun d ↦
    ∑ n ∈ Finset.range (d + 1),
      ∑ m ∈ Finset.range (n + 1), ((nonRascoeLayer d n m).card : ℤ)

theorem literalRascoeDoubleSeries_eq_rascoeSeries :
    literalRascoeDoubleSeries = rascoeSeries ℤ := by
  ext d
  simp only [literalRascoeDoubleSeries, coeff_mk, coeff_rascoeSeries]
  exact_mod_cast (rascoeNumber_eq_sum_layers d).symm

theorem literalNonRascoeDoubleSeries_eq_nonRascoeSeries :
    literalNonRascoeDoubleSeries = nonRascoeSeries ℤ := by
  ext d
  simp only [literalNonRascoeDoubleSeries, coeff_mk, coeff_nonRascoeSeries]
  exact_mod_cast (nonRascoeNumber_eq_sum_layers d).symm

/-! ## Formal inverses and the displayed paper terms -/

/-- The formal reciprocal `1/(X;X)ₘ`. -/
noncomputable def reciprocalFiniteEuler (m : ℕ) : ℤ⟦X⟧ :=
  ↑((powerSeriesQPochhammerUnit ℤ 1 m (by norm_num))⁻¹)

theorem reciprocalFiniteEuler_mul_pochhammer (m : ℕ) :
    reciprocalFiniteEuler m * powerSeriesQPochhammer ℤ 1 m = 1 := by
  rw [← coe_powerSeriesQPochhammerUnit ℤ 1 m (by norm_num)]
  exact Units.inv_mul _

/-! ### Weakly decreasing tuples and the finite Euler reciprocal -/

/-- Difference coordinates for a weakly decreasing `m`-tuple.  Coordinate
`i` records the drop after the first `i+1` entries. -/
abbrev WeakDifferenceCode (m : ℕ) := Fin m → ℕ

/-- The weight attached to difference coordinates. -/
def weakDifferenceWeight {m : ℕ} (c : WeakDifferenceCode m) : ℕ :=
  ∑ i, (i.1 + 1) * c i

/-- Decode difference coordinates into a weakly decreasing tuple by suffix
sums. -/
def weakEntries {m : ℕ} (c : WeakDifferenceCode m) (i : Fin m) : ℕ :=
  ∑ j ∈ Finset.univ.filter (i ≤ ·), c j

theorem weakEntries_antitone {m : ℕ} (c : WeakDifferenceCode m) :
    Antitone (weakEntries c) := by
  intro i j hij
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact le_trans hij hk
  · intro k hk hkn
    exact Nat.zero_le _

/-- Difference-coordinate weight is the sum of the decoded tuple. -/
theorem sum_weakEntries {m : ℕ} (c : WeakDifferenceCode m) :
    ∑ i, weakEntries c i = weakDifferenceWeight c := by
  simp only [weakEntries, weakDifferenceWeight]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    ∑ i, (if i ≤ j then c j else 0) =
        ∑ i ∈ Finset.univ.filter (· ≤ j), c j := by
          rw [Finset.sum_filter]
    _ = (j.1 + 1) * c j := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [show (Finset.univ.filter (· ≤ j) : Finset (Fin m)) =
          Finset.univ.filter (fun i : Fin m ↦ i.1 < j.1 + 1) by
        ext i
        simp]
      rw [Fin.card_filter_val_lt]
      simp

/-- The formal geometric series in powers of `Xᵏ`. -/
noncomputable def formalGeometricFactor (k : ℕ) : ℤ⟦X⟧ :=
  ∑' j : ℕ, X ^ (k * j)

theorem formalGeometricFactor_mul_one_sub {k : ℕ} (hk : 0 < k) :
    formalGeometricFactor k * (1 - (X : ℤ⟦X⟧) ^ k) = 1 := by
  simpa [formalGeometricFactor, pow_mul] using
    (PowerSeries.WithPiTopology.tsum_pow_mul_one_sub_of_constantCoeff_eq_zero
      (f := (X : ℤ⟦X⟧) ^ k) (by simp [hk.ne']))

/-- Product generating series of the difference coordinates of a weakly
decreasing `m`-tuple. -/
noncomputable def weakTupleSeries (m : ℕ) : ℤ⟦X⟧ :=
  ∏ i : Fin m, formalGeometricFactor (i.1 + 1)

theorem weakTupleSeries_mul_pochhammer (m : ℕ) :
    weakTupleSeries m * powerSeriesQPochhammer ℤ 1 m = 1 := by
  rw [powerSeriesQPochhammer_eq_prod]
  rw [weakTupleSeries]
  have hconvert :
      (∏ i : Fin m, formalGeometricFactor (i.1 + 1)) =
        ∏ i ∈ Finset.range m, formalGeometricFactor (i + 1) := by
    rw [Finset.prod_range]
  rw [hconvert]
  simp only [Nat.add_comm 1]
  rw [← Finset.prod_mul_distrib]
  simp [formalGeometricFactor_mul_one_sub (k := _)]

/-- The weak-tuple generating product is exactly `1/(X;X)ₘ`. -/
theorem weakTupleSeries_eq_reciprocalFiniteEuler (m : ℕ) :
    weakTupleSeries m = reciprocalFiniteEuler m := by
  let u := powerSeriesQPochhammerUnit ℤ 1 m (by norm_num)
  have hu : (u : ℤ⟦X⟧) = powerSeriesQPochhammer ℤ 1 m := by
    exact coe_powerSeriesQPochhammerUnit ℤ 1 m (by norm_num)
  calc
    weakTupleSeries m =
        weakTupleSeries m * (u : ℤ⟦X⟧) * (↑(u⁻¹) : ℤ⟦X⟧) := by
      rw [mul_assoc, Units.mul_inv, mul_one]
    _ = 1 * (↑(u⁻¹) : ℤ⟦X⟧) := by
      rw [hu, weakTupleSeries_mul_pochhammer]
    _ = reciprocalFiniteEuler m := by
      simp [reciprocalFiniteEuler, u]

/-- A literal weakly decreasing tuple of `m` nonnegative integers. -/
def WeakDescending (m : ℕ) := {a : Fin m → ℕ // Antitone a}

namespace WeakDescending

instance (m : ℕ) : CoeFun (WeakDescending m) (fun _ ↦ Fin m → ℕ) :=
  ⟨Subtype.val⟩

/-- Sum of the tuple entries. -/
def weight {m : ℕ} (a : WeakDescending m) : ℕ := ∑ i, a i

/-- Remove the last entry as a common baseline. -/
def removeLastBaseline {m : ℕ} (a : WeakDescending (m + 1)) :
    WeakDescending m :=
  ⟨fun i ↦ a i.castSucc - a (Fin.last m), by
    intro i j hij
    exact Nat.sub_le_sub_right (a.2 hij) _⟩

/-- Restore a common last baseline. -/
def addLastBaseline {m : ℕ} (ab : WeakDescending m × ℕ) :
    WeakDescending (m + 1) :=
  ⟨Fin.snoc (fun i ↦ ab.1 i + ab.2) ab.2, by
    intro i j hij
    induction i using Fin.lastCases with
    | last =>
        induction j using Fin.lastCases with
        | last => simp
        | cast j => exact (not_le_of_gt j.castSucc_lt_last hij).elim
    | cast i =>
        induction j using Fin.lastCases with
        | last => simp
        | cast j =>
            simp only [Fin.snoc_castSucc]
            exact Nat.add_le_add_right (ab.1.2 hij) _⟩

@[simp] theorem addLastBaseline_castSucc {m : ℕ}
    (ab : WeakDescending m × ℕ) (i : Fin m) :
    addLastBaseline ab i.castSucc = ab.1 i + ab.2 := by
  simp [addLastBaseline]

@[simp] theorem addLastBaseline_last {m : ℕ}
    (ab : WeakDescending m × ℕ) :
    addLastBaseline ab (Fin.last m) = ab.2 := by
  simp [addLastBaseline]

/-- Canonical last-baseline decomposition of a weakly decreasing tuple. -/
def lastBaselineEquiv (m : ℕ) :
    WeakDescending (m + 1) ≃ WeakDescending m × ℕ where
  toFun a := (removeLastBaseline a, a (Fin.last m))
  invFun := addLastBaseline
  left_inv a := by
    apply Subtype.ext
    funext i
    induction i using Fin.lastCases with
    | last => simp [addLastBaseline]
    | cast i =>
        simp only [addLastBaseline_castSucc, removeLastBaseline]
        exact Nat.sub_add_cancel (a.2 (Fin.le_last i.castSucc))
  right_inv ab := by
    apply Prod.ext
    · apply Subtype.ext
      funext i
      simp [removeLastBaseline]
    · simp

theorem weight_addLastBaseline {m : ℕ} (a : WeakDescending m) (b : ℕ) :
    weight (addLastBaseline (a, b)) = weight a + (m + 1) * b := by
  rw [weight, Fin.sum_univ_castSucc]
  simp only [addLastBaseline_castSucc, addLastBaseline_last, weight,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [Nat.succ_mul, Nat.add_assoc]
  simp

theorem weight_lastBaselineEquiv {m : ℕ} (a : WeakDescending (m + 1)) :
    weight a = weight (lastBaselineEquiv m a).1 +
      (m + 1) * (lastBaselineEquiv m a).2 := by
  have h := weight_addLastBaseline
    (lastBaselineEquiv m a).1 (lastBaselineEquiv m a).2
  have hinv := (lastBaselineEquiv m).left_inv a
  change addLastBaseline
    ((lastBaselineEquiv m a).1, (lastBaselineEquiv m a).2) = a at hinv
  rw [hinv] at h
  exact h

/-- Every fixed-weight fiber of weakly decreasing tuples is finite. -/
theorem finite_weight_fiber (m d : ℕ) :
    Set.Finite {a : WeakDescending m | weight a = d} := by
  rw [← Set.finite_coe_iff]
  let f : {a : WeakDescending m // weight a = d} →
      {x : Fin m → ℕ // x ∈ Finset.Nat.antidiagonalTuple m d} :=
    fun a ↦ ⟨a.1.1, Finset.Nat.mem_antidiagonalTuple.mpr a.2⟩
  apply Finite.of_injective f
  intro a b hab
  have hv : a.1.1 = b.1.1 :=
    congrArg (fun z : {x : Fin m → ℕ //
      x ∈ Finset.Nat.antidiagonalTuple m d} ↦ z.1) hab
  apply Subtype.ext
  apply Subtype.ext
  exact hv

theorem summable_weight_monomials (m : ℕ) :
    Summable (fun a : WeakDescending m ↦ (X : ℤ⟦X⟧) ^ weight a) := by
  rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
  intro d
  apply summable_of_hasFiniteSupport
  apply (finite_weight_fiber m d).subset
  intro a ha
  simp only [Function.mem_support, ne_eq, coeff_X_pow] at ha
  by_contra hne
  have hne' : d ≠ weight a := fun h ↦ hne h.symm
  rw [if_neg hne'] at ha
  exact ha rfl

/-- The finite set of weakly decreasing tuples with prescribed weight. -/
noncomputable def weightFiber (m d : ℕ) : Finset (WeakDescending m) :=
  (finite_weight_fiber m d).toFinset

@[simp] theorem mem_weightFiber {m d : ℕ} {a : WeakDescending m} :
    a ∈ weightFiber m d ↔ weight a = d := by
  simp [weightFiber]

/-- Literal weight generating function of weakly decreasing nonnegative
`m`-tuples. -/
noncomputable def weightSeries (m : ℕ) : ℤ⟦X⟧ :=
  ∑' a : WeakDescending m, X ^ weight a

/-- Coefficient form of the literal weak-tuple generating function. -/
theorem coeff_weightSeries (m d : ℕ) :
    coeff d (weightSeries m) = ((weightFiber m d).card : ℤ) := by
  have hs : HasSum
      (fun a : WeakDescending m ↦ coeff d ((X : ℤ⟦X⟧) ^ weight a))
      (coeff d (weightSeries m)) := by
    apply (PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff ℤ).mp
      ((summable_weight_monomials m).hasSum) d
  rw [← hs.tsum_eq, tsum_eq_sum (s := weightFiber m d)]
  · simp only [coeff_X_pow]
    calc
      ∑ a ∈ weightFiber m d, (if d = weight a then (1 : ℤ) else 0) =
          ∑ _a ∈ weightFiber m d, (1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [if_pos (mem_weightFiber.mp ha).symm]
      _ = ((weightFiber m d).card : ℤ) := by simp
  · intro a ha
    rw [coeff_X_pow, if_neg]
    exact fun h ↦ ha (mem_weightFiber.mpr h.symm)

noncomputable def lastBaselineSeries (k : ℕ) : ℤ⟦X⟧ :=
  ∑' b : ℕ, X ^ (k * b)

theorem summable_lastBaseline_monomials {k : ℕ} (hk : 0 < k) :
    Summable (fun b : ℕ ↦ (X : ℤ⟦X⟧) ^ (k * b)) := by
  have hzero : constantCoeff ((X : ℤ⟦X⟧) ^ k) = 0 := by
    rw [map_pow, constantCoeff_X, zero_pow hk.ne']
  simpa only [pow_mul] using
    (summable_pow_of_constantCoeff_eq_zero hzero)

theorem weightSeries_succ (m : ℕ) :
    weightSeries (m + 1) = weightSeries m * lastBaselineSeries (m + 1) := by
  let F : WeakDescending m × ℕ → ℤ⟦X⟧ := fun ab ↦
    X ^ (weight ab.1 + (m + 1) * ab.2)
  have hF : Summable F := by
    apply ((lastBaselineEquiv m).summable_iff (f := F)).mp
    have hfun : F ∘ (lastBaselineEquiv m) =
        fun a : WeakDescending (m + 1) ↦ (X : ℤ⟦X⟧) ^ weight a := by
      funext a
      simp only [Function.comp_apply, F]
      rw [weight_lastBaselineEquiv]
    rw [hfun]
    exact summable_weight_monomials (m + 1)
  have hprod : Summable (fun ab : WeakDescending m × ℕ ↦
      (X : ℤ⟦X⟧) ^ weight ab.1 * X ^ ((m + 1) * ab.2)) := by
    simpa only [← pow_add] using hF
  calc
    weightSeries (m + 1) = ∑' a : WeakDescending (m + 1),
        F (lastBaselineEquiv m a) := by
      apply tsum_congr
      intro a
      simp only [F, weight_lastBaselineEquiv]
    _ = ∑' ab : WeakDescending m × ℕ, F ab :=
      (lastBaselineEquiv m).tsum_eq F
    _ = weightSeries m * lastBaselineSeries (m + 1) := by
      rw [weightSeries, lastBaselineSeries]
      symm
      simpa only [F, ← pow_add] using
        (summable_weight_monomials m).tsum_mul_tsum
          (summable_lastBaseline_monomials (by omega)) hprod

theorem weightSeries_zero : weightSeries 0 = 1 := by
  let nil : WeakDescending 0 :=
    ⟨Fin.elim0, fun i ↦ Fin.elim0 i⟩
  rw [weightSeries, tsum_eq_single nil]
  · simp [weight, nil]
  · intro b hb
    exfalso
    apply hb
    apply Subtype.ext
    funext i
    exact Fin.elim0 i

theorem lastBaselineSeries_mul_one_sub (k : ℕ) (hk : 0 < k) :
    lastBaselineSeries k * (1 - (X : ℤ⟦X⟧) ^ k) = 1 := by
  rw [lastBaselineSeries]
  have hzero : constantCoeff ((X : ℤ⟦X⟧) ^ k) = 0 := by
    rw [map_pow, constantCoeff_X, zero_pow hk.ne']
  simpa only [pow_mul] using
    (tsum_pow_mul_one_sub_of_constantCoeff_eq_zero hzero)

theorem weightSeries_mul_pochhammer (m : ℕ) :
    weightSeries m * powerSeriesQPochhammer ℤ 1 m = 1 := by
  induction m with
  | zero => simp [weightSeries_zero]
  | succ m ih =>
      rw [weightSeries_succ, powerSeriesQPochhammer_succ]
      calc
        (weightSeries m * lastBaselineSeries (m + 1)) *
            (powerSeriesQPochhammer ℤ 1 m * (1 - X ^ (1 + m))) =
            (weightSeries m * powerSeriesQPochhammer ℤ 1 m) *
              (lastBaselineSeries (m + 1) * (1 - X ^ (m + 1))) := by
                rw [Nat.add_comm 1 m]
                ring
        _ = 1 := by
          rw [ih, lastBaselineSeries_mul_one_sub (m + 1) (by omega), one_mul]

/-- Main high-parts interface: weakly decreasing nonnegative `m`-tuples,
weighted by the sum, have generating function `1/(X;X)ₘ`. -/
theorem weightSeries_eq_reciprocalFiniteEuler (m : ℕ) :
    weightSeries m = reciprocalFiniteEuler m := by
  apply mul_right_cancel₀
    ((powerSeriesQPochhammer_isUnit ℤ (by omega : 0 < 1) m).ne_zero)
  rw [weightSeries_mul_pochhammer, reciprocalFiniteEuler_mul_pochhammer]

/-! ### Multisets of fixed cardinality as weakly decreasing tuples -/

noncomputable def ofMultiset (m : ℕ) :
    {s : Multiset ℕ // s.card = m} → WeakDescending m := fun s => by
  let l := s.1.sort (· ≥ ·)
  have hl : l.length = m := by simp [l]
  refine ⟨fun i => l.get ⟨i.1, by simpa [hl] using i.2⟩, ?_⟩
  intro i j hij
  apply (Multiset.pairwise_sort s.1 (· ≥ ·)).sortedGE.antitone_get
  exact hij

theorem ofMultiset_mem (m : ℕ)
    (s : {s : Multiset ℕ // s.card = m}) (i : Fin m) :
    ofMultiset m s i ∈ s.1 := by
  change (s.1.sort (· ≥ ·)).get _ ∈ s.1
  apply (Multiset.mem_sort (s := s.1) (· ≥ ·)).mp
  exact List.get_mem _ _

def toMultiset (m : ℕ) : WeakDescending m →
    {s : Multiset ℕ // s.card = m} := fun a ↦
  ⟨(List.ofFn a.1 : List ℕ), by simp⟩

/-- Sorting gives a weight-preserving equivalence between multisets of
cardinality `m` and weakly decreasing `m`-tuples. -/
noncomputable def multisetEquiv (m : ℕ) :
    {s : Multiset ℕ // s.card = m} ≃ WeakDescending m where
  toFun := ofMultiset m
  invFun := toMultiset m
  left_inv s := by
    apply Subtype.ext
    change (List.ofFn (ofMultiset m s).1 : Multiset ℕ) = s.1
    rw [← Multiset.sort_eq s.1 (· ≥ ·)]
    apply congrArg (fun l : List ℕ => (l : Multiset ℕ))
    apply List.ext_get
    · simp [ofMultiset]
    · intro i hi₁ hi₂
      simp [ofMultiset]
  right_inv a := by
    apply Subtype.ext
    apply List.ofFn_injective
    apply List.Perm.eq_of_sortedGE
      (ofMultiset m (toMultiset m a)).2.sortedGE_ofFn
      a.2.sortedGE_ofFn
    apply Multiset.coe_eq_coe.mp
    have hsort : ((List.ofFn a.1 : List ℕ) : Multiset ℕ).sort (· ≥ ·) =
        List.ofFn a.1 := by
      apply List.Perm.eq_of_sortedGE
        (Multiset.pairwise_sort
          ((List.ofFn a.1 : List ℕ) : Multiset ℕ) (· ≥ ·)).sortedGE
        a.2.sortedGE_ofFn
      apply Multiset.coe_eq_coe.mp
      exact Multiset.sort_eq _ _
    have hof : List.ofFn (ofMultiset m (toMultiset m a)).1 =
        ((List.ofFn a.1 : List ℕ) : Multiset ℕ).sort (· ≥ ·) := by
      apply List.ext_get
      · simp [ofMultiset, toMultiset]
      · intro i hi₁ hi₂
        simp [ofMultiset, toMultiset]
    rw [hof, hsort]

theorem weight_multisetEquiv (m : ℕ)
    (s : {s : Multiset ℕ // s.card = m}) :
    weight (multisetEquiv m s) = s.1.sum := by
  rw [weight, ← List.sum_ofFn]
  change (List.ofFn (ofMultiset m s).1).sum = s.1.sum
  have hof : List.ofFn (ofMultiset m s).1 = s.1.sort (· ≥ ·) := by
    apply List.ext_get
    · simp [ofMultiset]
    · intro i hi₁ hi₂
      simp [ofMultiset]
  rw [hof, ← Multiset.sum_coe]
  exact congrArg Multiset.sum (Multiset.sort_eq s.1 (· ≥ ·))

theorem sum_multisetEquiv_symm (m : ℕ) (a : WeakDescending m) :
    ((multisetEquiv m).symm a).1.sum = weight a := by
  rw [← weight_multisetEquiv m ((multisetEquiv m).symm a)]
  simp

end WeakDescending

/-! ### Bounded multisets and rectangle partitions -/

/-- A multiset of exactly `rows` naturals, each at most `cols`. -/
def BoundedMultiset (rows cols : ℕ) :=
  {s : Multiset ℕ // s.card = rows ∧ ∀ x ∈ s, x ≤ cols}

/-- A weakly decreasing tuple whose entries are bounded by `cols`. -/
def BoundedWeakDescending (rows cols : ℕ) :=
  {a : WeakDescending rows // ∀ i, a i ≤ cols}

/-- Sorting is an equivalence from bounded multisets to bounded weakly
decreasing tuples. -/
noncomputable def boundedMultisetEquivWeak (rows cols : ℕ) :
    BoundedMultiset rows cols ≃ BoundedWeakDescending rows cols where
  toFun s :=
    ⟨WeakDescending.multisetEquiv rows ⟨s.1, s.2.1⟩,
      fun i ↦ s.2.2 _ (WeakDescending.ofMultiset_mem rows ⟨s.1, s.2.1⟩ i)⟩
  invFun a := by
    refine ⟨((WeakDescending.multisetEquiv rows).symm a.1).1,
      (WeakDescending.multisetEquiv rows).symm a.1 |>.2, ?_⟩
    intro x hx
    change x ∈ (List.ofFn a.1.1 : List ℕ) at hx
    simp only [Multiset.mem_coe, List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    exact a.2 i
  left_inv s := by
    apply Subtype.ext
    change ((WeakDescending.multisetEquiv rows).symm
      (WeakDescending.multisetEquiv rows ⟨s.1, s.2.1⟩)).1 = s.1
    rw [Equiv.symm_apply_apply]
  right_inv a := by
    apply Subtype.ext
    change WeakDescending.multisetEquiv rows
      ((WeakDescending.multisetEquiv rows).symm a.1) = a.1
    rw [Equiv.apply_symm_apply]

/-- Bounded weakly decreasing natural tuples are exactly the project's
zero-padded rectangle partitions. -/
def boundedWeakEquivRectangle (rows cols : ℕ) :
    BoundedWeakDescending rows cols ≃ LeanCo.RectanglePartition rows cols where
  toFun a :=
    ⟨fun i ↦ ⟨a.1 i, Nat.lt_succ_of_le (a.2 i)⟩,
      fun _ _ h ↦ a.1.2 h⟩
  invFun p :=
    ⟨⟨fun i ↦ (p.1 i).val, fun _ _ h ↦ p.2 h⟩,
      fun i ↦ Nat.le_of_lt_succ (p.1 i).isLt⟩
  left_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv p := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    rfl

/-- Fixed-cardinality bounded multisets as rectangle partitions. -/
noncomputable def boundedMultisetEquivRectangle (rows cols : ℕ) :
    BoundedMultiset rows cols ≃ LeanCo.RectanglePartition rows cols :=
  (boundedMultisetEquivWeak rows cols).trans
    (boundedWeakEquivRectangle rows cols)

/-- The bounded-multiset/rectangle equivalence preserves total weight. -/
theorem weight_boundedMultisetEquivRectangle {rows cols : ℕ}
    (s : BoundedMultiset rows cols) :
    (boundedMultisetEquivRectangle rows cols s).weight = s.1.sum := by
  change WeakDescending.weight
      (WeakDescending.multisetEquiv rows ⟨s.1, s.2.1⟩) = s.1.sum
  exact WeakDescending.weight_multisetEquiv rows ⟨s.1, s.2.1⟩

/-- The bounded multiset of row lengths underlying a rectangle partition. -/
noncomputable def rectangleEntries {rows cols : ℕ}
    (p : LeanCo.RectanglePartition rows cols) : BoundedMultiset rows cols :=
  (boundedMultisetEquivRectangle rows cols).symm p

@[simp] theorem rectangleEntries_card {rows cols : ℕ}
    (p : LeanCo.RectanglePartition rows cols) :
    (rectangleEntries p).1.card = rows :=
  (rectangleEntries p).2.1

theorem rectangleEntries_bound {rows cols : ℕ}
    (p : LeanCo.RectanglePartition rows cols) {x : ℕ}
    (hx : x ∈ (rectangleEntries p).1) : x ≤ cols :=
  (rectangleEntries p).2.2 x hx

@[simp] theorem rectangleEntries_sum {rows cols : ℕ}
    (p : LeanCo.RectanglePartition rows cols) :
    (rectangleEntries p).1.sum = p.weight := by
  have h := weight_boundedMultisetEquivRectangle (rectangleEntries p)
  simpa [rectangleEntries] using h.symm

/-- The multiset of entries of a weakly decreasing tuple. -/
noncomputable def weakEntriesMultiset {m : ℕ}
    (a : WeakDescending m) : Multiset ℕ :=
  ((WeakDescending.multisetEquiv m).symm a).1

@[simp] theorem weakEntriesMultiset_card {m : ℕ}
    (a : WeakDescending m) :
    (weakEntriesMultiset a).card = m :=
  ((WeakDescending.multisetEquiv m).symm a).2

@[simp] theorem weakEntriesMultiset_sum {m : ℕ}
    (a : WeakDescending m) :
    (weakEntriesMultiset a).sum = WeakDescending.weight a :=
  WeakDescending.sum_multisetEquiv_symm m a

theorem multiset_sum_map_add_const (s : Multiset ℕ) (c : ℕ) :
    (s.map fun x ↦ x + c).sum = s.sum + s.card * c := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons x s ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
      rw [ih, Nat.succ_mul]
      omega

/-- Rectangle/tuple code for a fixed Rascoe `(length, high-count)` layer. -/
abbrev RascoeLayerCode (n m : ℕ) :=
  Σ _p : LeanCo.RectanglePartition (n - 1) (n - m - 1), WeakDescending m

/-- Rectangle/tuple code for a fixed non-Rascoe layer. -/
abbrev NonRascoeLayerCode (n m : ℕ) :=
  Σ _p : LeanCo.RectanglePartition (n - 2) (n - m), WeakDescending m

/-- Rebuild the parts of a Rascoe partition from its rectangle/tuple code. -/
noncomputable def rascoeCodeParts (n m : ℕ) (z : RascoeLayerCode n m) :
    Multiset ℕ :=
  (weakEntriesMultiset z.2).map (fun x ↦ x + (n + 1)) +
    n ::ₘ (rectangleEntries (LeanCo.RectanglePartition.transpose z.1)).1.map Nat.succ

/-- Rebuild the parts of a non-Rascoe partition from its code. -/
noncomputable def nonRascoeCodeParts (n m : ℕ) (z : NonRascoeLayerCode n m) :
    Multiset ℕ :=
  (weakEntriesMultiset z.2).map (fun x ↦ x + (n + 1)) +
    (rectangleEntries (LeanCo.RectanglePartition.transpose z.1)).1.map Nat.succ

theorem rascoeCodeParts_card {n m : ℕ} (hn : 2 ≤ n) (hm : m < n)
    (z : RascoeLayerCode n m) :
    (rascoeCodeParts n m z).card = n := by
  simp only [rascoeCodeParts, Multiset.card_add, Multiset.card_map,
    Multiset.card_cons, weakEntriesMultiset_card, rectangleEntries_card]
  omega

theorem nonRascoeCodeParts_card {n m : ℕ} (hn : 2 ≤ n) (hm : m ≤ n)
    (z : NonRascoeLayerCode n m) :
    (nonRascoeCodeParts n m z).card = n := by
  simp only [nonRascoeCodeParts, Multiset.card_add, Multiset.card_map,
    weakEntriesMultiset_card, rectangleEntries_card]
  omega

theorem rascoeCodeParts_sum {n m : ℕ} (hn : 2 ≤ n) (hm : m < n)
    (z : RascoeLayerCode n m) :
    (rascoeCodeParts n m z).sum =
      m * n + 2 * n - 1 + z.1.weight + WeakDescending.weight z.2 := by
  have hlow :
      (rectangleEntries (LeanCo.RectanglePartition.transpose z.1)).1.card =
        n - m - 1 := rectangleEntries_card _
  simp only [rascoeCodeParts, Multiset.sum_add, Multiset.sum_cons,
    multiset_sum_map_add_const, weakEntriesMultiset_card,
    weakEntriesMultiset_sum, sum_map_succ, rectangleEntries_sum,
    LeanCo.RectanglePartition.weight_transpose, hlow, Nat.mul_add, Nat.mul_one]
  omega

theorem nonRascoeCodeParts_sum {n m : ℕ} (hn : 2 ≤ n) (hm : m ≤ n)
    (z : NonRascoeLayerCode n m) :
    (nonRascoeCodeParts n m z).sum =
      m * n + n + z.1.weight + WeakDescending.weight z.2 := by
  have hlow :
      (rectangleEntries (LeanCo.RectanglePartition.transpose z.1)).1.card =
        n - m := rectangleEntries_card _
  simp only [nonRascoeCodeParts, Multiset.sum_add,
    multiset_sum_map_add_const, weakEntriesMultiset_card,
    weakEntriesMultiset_sum, sum_map_succ, rectangleEntries_sum,
    LeanCo.RectanglePartition.weight_transpose, hlow, Nat.mul_add, Nat.mul_one]
  omega

theorem rascoeCodeParts_pos {n m : ℕ} (hn : 2 ≤ n)
    (z : RascoeLayerCode n m) {x : ℕ} (hx : x ∈ rascoeCodeParts n m z) :
    0 < x := by
  simp only [rascoeCodeParts, Multiset.mem_add, Multiset.mem_map,
    Multiset.mem_cons] at hx
  rcases hx with ⟨y, hy, rfl⟩ | rfl | ⟨y, hy, rfl⟩ <;> omega

theorem nonRascoeCodeParts_pos {n m : ℕ} (hn : 2 ≤ n)
    (z : NonRascoeLayerCode n m) {x : ℕ} (hx : x ∈ nonRascoeCodeParts n m z) :
    0 < x := by
  simp only [nonRascoeCodeParts, Multiset.mem_add, Multiset.mem_map] at hx
  rcases hx with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩ <;> omega

theorem filter_gt_rascoeCodeParts {n m : ℕ}
    (hn : 2 ≤ n) (z : RascoeLayerCode n m) :
    (rascoeCodeParts n m z).filter (n < ·) =
      (weakEntriesMultiset z.2).map (fun x ↦ x + (n + 1)) := by
  rw [rascoeCodeParts, Multiset.filter_add]
  have hhigh :
      ((weakEntriesMultiset z.2).map (fun x ↦ x + (n + 1))).filter (n < ·) =
        (weakEntriesMultiset z.2).map (fun x ↦ x + (n + 1)) := by
    apply Multiset.filter_eq_self.mpr
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
    omega
  have hlow :
      (n ::ₘ (rectangleEntries
        (LeanCo.RectanglePartition.transpose z.1)).1.map Nat.succ).filter (n < ·) = 0 := by
    apply Multiset.filter_eq_nil.mpr
    intro x hx
    rw [Multiset.mem_cons] at hx
    rcases hx with rfl | hx
    · exact lt_irrefl _
    · obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
      have hb : y ≤ n - 1 := rectangleEntries_bound
        (LeanCo.RectanglePartition.transpose z.1) hy
      omega
  rw [hhigh, hlow, add_zero]

theorem filter_gt_nonRascoeCodeParts {n m : ℕ}
    (hn : 2 ≤ n) (z : NonRascoeLayerCode n m) :
    (nonRascoeCodeParts n m z).filter (n < ·) =
      (weakEntriesMultiset z.2).map (fun x ↦ x + (n + 1)) := by
  rw [nonRascoeCodeParts, Multiset.filter_add]
  have hhigh :
      ((weakEntriesMultiset z.2).map (fun x ↦ x + (n + 1))).filter (n < ·) =
        (weakEntriesMultiset z.2).map (fun x ↦ x + (n + 1)) := by
    apply Multiset.filter_eq_self.mpr
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
    omega
  have hlow :
      ((rectangleEntries
        (LeanCo.RectanglePartition.transpose z.1)).1.map Nat.succ).filter (n < ·) = 0 := by
    apply Multiset.filter_eq_nil.mpr
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
    have hb : y ≤ n - 2 := rectangleEntries_bound
      (LeanCo.RectanglePartition.transpose z.1) hy
    omega
  rw [hhigh, hlow, add_zero]

theorem rascoeCodeParts_highCount {n m : ℕ}
    (hn : 2 ≤ n) (z : RascoeLayerCode n m) :
    ((rascoeCodeParts n m z).filter (n < ·)).card = m := by
  rw [filter_gt_rascoeCodeParts hn]
  simp

theorem nonRascoeCodeParts_highCount {n m : ℕ}
    (hn : 2 ≤ n) (z : NonRascoeLayerCode n m) :
    ((nonRascoeCodeParts n m z).filter (n < ·)).card = m := by
  rw [filter_gt_nonRascoeCodeParts hn]
  simp

theorem length_mem_rascoeCodeParts {n m : ℕ} (hn : 2 ≤ n) (hm : m < n)
    (z : RascoeLayerCode n m) :
    (rascoeCodeParts n m z).card ∈ rascoeCodeParts n m z := by
  rw [rascoeCodeParts_card hn hm]
  simp [rascoeCodeParts]

theorem length_notMem_nonRascoeCodeParts {n m : ℕ}
    (hn : 2 ≤ n) (hm : m ≤ n) (z : NonRascoeLayerCode n m) :
    (nonRascoeCodeParts n m z).card ∉ nonRascoeCodeParts n m z := by
  rw [nonRascoeCodeParts_card hn hm]
  intro h
  simp only [nonRascoeCodeParts, Multiset.mem_add, Multiset.mem_map] at h
  rcases h with ⟨y, hy, heq⟩ | ⟨y, hy, heq⟩
  · omega
  · have hb := rectangleEntries_bound
      (LeanCo.RectanglePartition.transpose z.1) hy
    omega

/-- The finite Rascoe code fiber at total size `d`. -/
abbrev RascoeCodeFiber (d n m : ℕ) :=
  {z : RascoeLayerCode n m //
    m * n + 2 * n - 1 + z.1.weight + WeakDescending.weight z.2 = d}

/-- The finite non-Rascoe code fiber at total size `d`. -/
abbrev NonRascoeCodeFiber (d n m : ℕ) :=
  {z : NonRascoeLayerCode n m //
    m * n + n + z.1.weight + WeakDescending.weight z.2 = d}

/-- Turn a code in the correct weight fiber into an actual partition of
`d`. -/
noncomputable def decodeRascoeCode (d n m : ℕ) (hn : 2 ≤ n) (hm : m < n)
    (z : RascoeCodeFiber d n m) : Nat.Partition d where
  parts := rascoeCodeParts n m z.1
  parts_pos := fun hx ↦ rascoeCodeParts_pos hn z.1 hx
  parts_sum := by
    rw [rascoeCodeParts_sum hn hm]
    exact z.2

/-- Non-Rascoe analogue of `decodeRascoeCode`. -/
noncomputable def decodeNonRascoeCode (d n m : ℕ)
    (hn : 2 ≤ n) (hm : m ≤ n)
    (z : NonRascoeCodeFiber d n m) : Nat.Partition d where
  parts := nonRascoeCodeParts n m z.1
  parts_pos := fun hx ↦ nonRascoeCodeParts_pos hn z.1 hx
  parts_sum := by
    rw [nonRascoeCodeParts_sum hn hm]
    exact z.2

theorem decodeRascoeCode_mem_layer (d n m : ℕ) (hn : 2 ≤ n) (hm : m < n)
    (z : RascoeCodeFiber d n m) :
    decodeRascoeCode d n m hn hm z ∈ rascoeLayer d n m := by
  classical
  simp only [rascoeLayer, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨?_, ?_, ?_⟩
  · exact length_mem_rascoeCodeParts hn hm z.1
  · exact rascoeCodeParts_card hn hm z.1
  · exact rascoeCodeParts_highCount hn z.1

theorem decodeNonRascoeCode_mem_layer (d n m : ℕ)
    (hn : 2 ≤ n) (hm : m ≤ n) (z : NonRascoeCodeFiber d n m) :
    decodeNonRascoeCode d n m hn hm z ∈ nonRascoeLayer d n m := by
  classical
  simp only [nonRascoeLayer, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨?_, ?_, ?_⟩
  · exact length_notMem_nonRascoeCodeParts hn hm z.1
  · exact nonRascoeCodeParts_card hn hm z.1
  · exact nonRascoeCodeParts_highCount hn z.1

/-- Decoding as a map into the literal Rascoe layer. -/
noncomputable def decodeRascoeLayerCode (d n m : ℕ)
    (hn : 2 ≤ n) (hm : m < n) :
    RascoeCodeFiber d n m → ↥(rascoeLayer d n m) :=
  fun z ↦ ⟨decodeRascoeCode d n m hn hm z,
    decodeRascoeCode_mem_layer d n m hn hm z⟩

/-- Decoding as a map into the literal non-Rascoe layer. -/
noncomputable def decodeNonRascoeLayerCode (d n m : ℕ)
    (hn : 2 ≤ n) (hm : m ≤ n) :
    NonRascoeCodeFiber d n m → ↥(nonRascoeLayer d n m) :=
  fun z ↦ ⟨decodeNonRascoeCode d n m hn hm z,
    decodeNonRascoeCode_mem_layer d n m hn hm z⟩

/-! ### Encoding literal layers -/

def partsAbove (n : ℕ) (s : Multiset ℕ) : Multiset ℕ :=
  s.filter (n < ·)

def partsAtMost (n : ℕ) (s : Multiset ℕ) : Multiset ℕ :=
  s.filter (fun x ↦ ¬n < x)

def highResidual (n : ℕ) (s : Multiset ℕ) : Multiset ℕ :=
  (partsAbove n s).map (fun x ↦ x - (n + 1))

def rascoeLowResidual (n : ℕ) (s : Multiset ℕ) : Multiset ℕ :=
  ((partsAtMost n s).erase n).map Nat.pred

def nonRascoeLowResidual (n : ℕ) (s : Multiset ℕ) : Multiset ℕ :=
  (partsAtMost n s).map Nat.pred

theorem partsAbove_add_partsAtMost (n : ℕ) (s : Multiset ℕ) :
    partsAbove n s + partsAtMost n s = s := by
  exact Multiset.filter_add_not (n < ·) s

theorem raise_highResidual (n : ℕ) (s : Multiset ℕ) :
    (highResidual n s).map (fun x ↦ x + (n + 1)) = partsAbove n s := by
  rw [highResidual, Multiset.map_map]
  calc
    (partsAbove n s).map
        ((fun x ↦ x + (n + 1)) ∘ fun x ↦ x - (n + 1)) =
        (partsAbove n s).map id := by
      apply Multiset.map_congr rfl
      intro x hx
      have hx' : n < x := (Multiset.mem_filter.mp hx).2
      simp only [Function.comp_apply, id_eq]
      omega
    _ = partsAbove n s := Multiset.map_id _

theorem raise_rascoeLowResidual (n : ℕ) (s : Multiset ℕ)
    (hs : ∀ x ∈ s, 0 < x) (hn : n ∈ partsAtMost n s) :
    n ::ₘ (rascoeLowResidual n s).map Nat.succ = partsAtMost n s := by
  rw [rascoeLowResidual, Multiset.map_map]
  have hmap :
      ((partsAtMost n s).erase n).map (Nat.succ ∘ Nat.pred) =
        (partsAtMost n s).erase n := by
    calc
      ((partsAtMost n s).erase n).map (Nat.succ ∘ Nat.pred) =
          ((partsAtMost n s).erase n).map id := by
        apply Multiset.map_congr rfl
        intro x hx
        simp only [Function.comp_apply, id_eq]
        have hxparts : x ∈ s :=
          Multiset.mem_of_mem_filter (Multiset.mem_of_mem_erase hx)
        exact Nat.succ_pred_eq_of_pos (hs x hxparts)
      _ = (partsAtMost n s).erase n := Multiset.map_id _
  rw [hmap]
  exact Multiset.cons_erase hn

theorem raise_nonRascoeLowResidual (n : ℕ) (s : Multiset ℕ)
    (hs : ∀ x ∈ s, 0 < x) :
    (nonRascoeLowResidual n s).map Nat.succ = partsAtMost n s := by
  rw [nonRascoeLowResidual, Multiset.map_map]
  calc
    (partsAtMost n s).map (Nat.succ ∘ Nat.pred) =
        (partsAtMost n s).map id := by
      apply Multiset.map_congr rfl
      intro x hx
      simp only [Function.comp_apply, id_eq]
      exact Nat.succ_pred_eq_of_pos (hs x (Multiset.mem_of_mem_filter hx))
    _ = partsAtMost n s := Multiset.map_id _

theorem card_partsAbove_add_card_partsAtMost (n : ℕ) (s : Multiset ℕ) :
    (partsAbove n s).card + (partsAtMost n s).card = s.card := by
  simpa using congrArg Multiset.card (partsAbove_add_partsAtMost n s)

@[simp] theorem highResidual_card (n : ℕ) (s : Multiset ℕ) :
    (highResidual n s).card = (partsAbove n s).card := by
  simp [highResidual]

theorem rascoeLowResidual_card {n m : ℕ} (s : Multiset ℕ)
    (hcard : s.card = n) (hhigh : (partsAbove n s).card = m)
    (hnmem : n ∈ partsAtMost n s) (hm : m < n) :
    (rascoeLowResidual n s).card = n - m - 1 := by
  have hsplit := card_partsAbove_add_card_partsAtMost n s
  have herase := Multiset.card_erase_add_one hnmem
  simp only [rascoeLowResidual, Multiset.card_map]
  omega

theorem nonRascoeLowResidual_card {n m : ℕ} (s : Multiset ℕ)
    (hcard : s.card = n) (hhigh : (partsAbove n s).card = m)
    (hm : m ≤ n) :
    (nonRascoeLowResidual n s).card = n - m := by
  have hsplit := card_partsAbove_add_card_partsAtMost n s
  simp only [nonRascoeLowResidual, Multiset.card_map]
  omega

theorem rascoeLowResidual_bound {n : ℕ} (hn : 2 ≤ n) (s : Multiset ℕ)
    {x : ℕ} (hx : x ∈ rascoeLowResidual n s) : x ≤ n - 1 := by
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
  have hy' : y ∈ partsAtMost n s := Multiset.mem_of_mem_erase hy
  have hle : y ≤ n := Nat.le_of_not_gt (Multiset.mem_filter.mp hy').2
  simpa [Nat.pred_eq_sub_one] using Nat.pred_le_pred hle

theorem nonRascoeLowResidual_bound {n : ℕ} (hn : 2 ≤ n) (s : Multiset ℕ)
    (hnmem : n ∉ s) {x : ℕ} (hx : x ∈ nonRascoeLowResidual n s) :
    x ≤ n - 2 := by
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
  have hyParts : y ∈ s := Multiset.mem_of_mem_filter hy
  have hle : y ≤ n := Nat.le_of_not_gt (Multiset.mem_filter.mp hy).2
  have hne : y ≠ n := fun h ↦ hnmem (h ▸ hyParts)
  cases y with
  | zero => simp
  | succ y =>
      simp only [Nat.pred_succ]
      omega

/-- Extract a rectangle/tuple code from a literal Rascoe layer. -/
noncomputable def encodeRascoeRaw (d n m : ℕ) (hn : 2 ≤ n) (hm : m < n)
    (p : ↥(rascoeLayer d n m)) : RascoeLayerCode n m := by
  classical
  have hp : IsRascoe p.1 ∧ length p.1 = n ∧ aboveLengthCount n p.1 = m := by
    have hpMem := p.2
    change p.1 ∈ Finset.univ.filter (fun q ↦
      IsRascoe q ∧ length q = n ∧ aboveLengthCount n q = m) at hpMem
    exact (Finset.mem_filter.mp hpMem).2
  have hcard : p.1.parts.card = n := hp.2.1
  have hhigh : (partsAbove n p.1.parts).card = m := by
    simpa [partsAbove, aboveLengthCount] using hp.2.2
  have hnparts : n ∈ p.1.parts := by
    have h := hp.1
    change p.1.parts.card ∈ p.1.parts at h
    rw [hcard] at h
    exact h
  have hnlow : n ∈ partsAtMost n p.1.parts := by
    simp [partsAtMost, hnparts]
  let high : {s : Multiset ℕ // s.card = m} :=
    ⟨highResidual n p.1.parts, by simp [hhigh]⟩
  let low : BoundedMultiset (n - m - 1) (n - 1) :=
    ⟨rascoeLowResidual n p.1.parts,
      rascoeLowResidual_card p.1.parts hcard hhigh hnlow hm,
      fun _ hx ↦ rascoeLowResidual_bound hn p.1.parts hx⟩
  exact ⟨LeanCo.RectanglePartition.transpose
      (boundedMultisetEquivRectangle (n - m - 1) (n - 1) low),
    WeakDescending.multisetEquiv m high⟩

/-- Extract a rectangle/tuple code from a literal non-Rascoe layer. -/
noncomputable def encodeNonRascoeRaw (d n m : ℕ)
    (hn : 2 ≤ n) (hm : m ≤ n)
    (p : ↥(nonRascoeLayer d n m)) : NonRascoeLayerCode n m := by
  classical
  have hp : IsNonRascoe p.1 ∧ length p.1 = n ∧ aboveLengthCount n p.1 = m := by
    have hpMem := p.2
    change p.1 ∈ Finset.univ.filter (fun q ↦
      IsNonRascoe q ∧ length q = n ∧ aboveLengthCount n q = m) at hpMem
    exact (Finset.mem_filter.mp hpMem).2
  have hcard : p.1.parts.card = n := hp.2.1
  have hhigh : (partsAbove n p.1.parts).card = m := by
    simpa [partsAbove, aboveLengthCount] using hp.2.2
  have hnparts : n ∉ p.1.parts := by
    have h := hp.1
    change p.1.parts.card ∉ p.1.parts at h
    rw [hcard] at h
    exact h
  let high : {s : Multiset ℕ // s.card = m} :=
    ⟨highResidual n p.1.parts, by simp [hhigh]⟩
  let low : BoundedMultiset (n - m) (n - 2) :=
    ⟨nonRascoeLowResidual n p.1.parts,
      nonRascoeLowResidual_card p.1.parts hcard hhigh hm,
      fun _ hx ↦ nonRascoeLowResidual_bound hn p.1.parts hnparts hx⟩
  exact ⟨LeanCo.RectanglePartition.transpose
      (boundedMultisetEquivRectangle (n - m) (n - 2) low),
    WeakDescending.multisetEquiv m high⟩

theorem weakEntriesMultiset_encodeRascoeRaw
    (d n m : ℕ) (hn : 2 ≤ n) (hm : m < n)
    (p : ↥(rascoeLayer d n m)) :
    weakEntriesMultiset (encodeRascoeRaw d n m hn hm p).2 =
      highResidual n p.1.parts := by
  classical
  simp [encodeRascoeRaw, weakEntriesMultiset]

theorem rectangleEntries_encodeRascoeRaw
    (d n m : ℕ) (hn : 2 ≤ n) (hm : m < n)
    (p : ↥(rascoeLayer d n m)) :
    (rectangleEntries (LeanCo.RectanglePartition.transpose
      (encodeRascoeRaw d n m hn hm p).1)).1 =
      rascoeLowResidual n p.1.parts := by
  classical
  simp [encodeRascoeRaw, rectangleEntries]

theorem weakEntriesMultiset_encodeNonRascoeRaw
    (d n m : ℕ) (hn : 2 ≤ n) (hm : m ≤ n)
    (p : ↥(nonRascoeLayer d n m)) :
    weakEntriesMultiset (encodeNonRascoeRaw d n m hn hm p).2 =
      highResidual n p.1.parts := by
  classical
  simp [encodeNonRascoeRaw, weakEntriesMultiset]

theorem rectangleEntries_encodeNonRascoeRaw
    (d n m : ℕ) (hn : 2 ≤ n) (hm : m ≤ n)
    (p : ↥(nonRascoeLayer d n m)) :
    (rectangleEntries (LeanCo.RectanglePartition.transpose
      (encodeNonRascoeRaw d n m hn hm p).1)).1 =
      nonRascoeLowResidual n p.1.parts := by
  classical
  simp [encodeNonRascoeRaw, rectangleEntries]

theorem rascoeCodeParts_encodeRascoeRaw
    (d n m : ℕ) (hn : 2 ≤ n) (hm : m < n)
    (p : ↥(rascoeLayer d n m)) :
    rascoeCodeParts n m (encodeRascoeRaw d n m hn hm p) = p.1.parts := by
  classical
  have hp : IsRascoe p.1 ∧ length p.1 = n := by
    have hpMem := p.2
    change p.1 ∈ Finset.univ.filter (fun q ↦
      IsRascoe q ∧ length q = n ∧ aboveLengthCount n q = m) at hpMem
    exact ⟨(Finset.mem_filter.mp hpMem).2.1,
      (Finset.mem_filter.mp hpMem).2.2.1⟩
  have hnparts : n ∈ p.1.parts := by
    have h := hp.1
    change p.1.parts.card ∈ p.1.parts at h
    have hcard := hp.2
    change p.1.parts.card = n at hcard
    rw [hcard] at h
    exact h
  have hnlow : n ∈ partsAtMost n p.1.parts := by
    simp [partsAtMost, hnparts]
  rw [rascoeCodeParts, weakEntriesMultiset_encodeRascoeRaw,
    rectangleEntries_encodeRascoeRaw, raise_highResidual,
    raise_rascoeLowResidual n p.1.parts (fun x hx ↦ p.1.parts_pos hx) hnlow,
    partsAbove_add_partsAtMost]

theorem nonRascoeCodeParts_encodeNonRascoeRaw
    (d n m : ℕ) (hn : 2 ≤ n) (hm : m ≤ n)
    (p : ↥(nonRascoeLayer d n m)) :
    nonRascoeCodeParts n m (encodeNonRascoeRaw d n m hn hm p) = p.1.parts := by
  classical
  rw [nonRascoeCodeParts, weakEntriesMultiset_encodeNonRascoeRaw,
    rectangleEntries_encodeNonRascoeRaw, raise_highResidual,
    raise_nonRascoeLowResidual n p.1.parts (fun x hx ↦ p.1.parts_pos hx),
    partsAbove_add_partsAtMost]

/-- The raw encoding automatically has the prescribed total weight. -/
noncomputable def encodeRascoeCode (d n m : ℕ) (hn : 2 ≤ n) (hm : m < n) :
    ↥(rascoeLayer d n m) → RascoeCodeFiber d n m := fun p ↦
  ⟨encodeRascoeRaw d n m hn hm p, by
    calc
      m * n + 2 * n - 1 + (encodeRascoeRaw d n m hn hm p).1.weight +
          WeakDescending.weight (encodeRascoeRaw d n m hn hm p).2 =
          (rascoeCodeParts n m (encodeRascoeRaw d n m hn hm p)).sum :=
        (rascoeCodeParts_sum hn hm _).symm
      _ = p.1.parts.sum := congrArg Multiset.sum
        (rascoeCodeParts_encodeRascoeRaw d n m hn hm p)
      _ = d := p.1.parts_sum⟩

noncomputable def encodeNonRascoeCode (d n m : ℕ)
    (hn : 2 ≤ n) (hm : m ≤ n) :
    ↥(nonRascoeLayer d n m) → NonRascoeCodeFiber d n m := fun p ↦
  ⟨encodeNonRascoeRaw d n m hn hm p, by
    calc
      m * n + n + (encodeNonRascoeRaw d n m hn hm p).1.weight +
          WeakDescending.weight (encodeNonRascoeRaw d n m hn hm p).2 =
          (nonRascoeCodeParts n m (encodeNonRascoeRaw d n m hn hm p)).sum :=
        (nonRascoeCodeParts_sum hn hm _).symm
      _ = p.1.parts.sum := congrArg Multiset.sum
        (nonRascoeCodeParts_encodeNonRascoeRaw d n m hn hm p)
      _ = d := p.1.parts_sum⟩

theorem decodeRascoeLayerCode_encodeRascoeCode
    (d n m : ℕ) (hn : 2 ≤ n) (hm : m < n)
    (p : ↥(rascoeLayer d n m)) :
    decodeRascoeLayerCode d n m hn hm (encodeRascoeCode d n m hn hm p) = p := by
  apply Subtype.ext
  apply Nat.Partition.ext
  exact rascoeCodeParts_encodeRascoeRaw d n m hn hm p

theorem decodeNonRascoeLayerCode_encodeNonRascoeCode
    (d n m : ℕ) (hn : 2 ≤ n) (hm : m ≤ n)
    (p : ↥(nonRascoeLayer d n m)) :
    decodeNonRascoeLayerCode d n m hn hm
      (encodeNonRascoeCode d n m hn hm p) = p := by
  apply Subtype.ext
  apply Nat.Partition.ext
  exact nonRascoeCodeParts_encodeNonRascoeRaw d n m hn hm p

theorem weakEntriesMultiset_injective {m : ℕ} :
    Function.Injective (weakEntriesMultiset : WeakDescending m → Multiset ℕ) := by
  intro a b hab
  apply (WeakDescending.multisetEquiv m).symm.injective
  apply Subtype.ext
  exact hab

theorem rectangleEntries_injective {rows cols : ℕ} :
    Function.Injective
      (rectangleEntries : LeanCo.RectanglePartition rows cols →
        BoundedMultiset rows cols) := by
  exact (boundedMultisetEquivRectangle rows cols).symm.injective

theorem rascoeCodeParts_injective {n m : ℕ} (hn : 2 ≤ n) (hm : m < n) :
    Function.Injective (rascoeCodeParts n m) := by
  intro a b hab
  have hfiltered := congrArg (Multiset.filter (n < ·)) hab
  rw [filter_gt_rascoeCodeParts hn, filter_gt_rascoeCodeParts hn] at hfiltered
  have hweak : weakEntriesMultiset a.2 = weakEntriesMultiset b.2 :=
    Multiset.map_injective (fun x y h ↦ by omega) hfiltered
  have hsecond : a.2 = b.2 := weakEntriesMultiset_injective hweak
  have hab' := hab
  simp only [rascoeCodeParts] at hab'
  have hhighMap :
      (weakEntriesMultiset a.2).map (fun x ↦ x + (n + 1)) =
        (weakEntriesMultiset b.2).map (fun x ↦ x + (n + 1)) :=
    congrArg (Multiset.map (fun x ↦ x + (n + 1))) hweak
  rw [hhighMap] at hab'
  have hcons :
      n ::ₘ (rectangleEntries (LeanCo.RectanglePartition.transpose a.1)).1.map Nat.succ =
        n ::ₘ (rectangleEntries (LeanCo.RectanglePartition.transpose b.1)).1.map Nat.succ :=
    add_left_cancel hab'
  have hlowMap := (Multiset.cons_inj_right n).mp hcons
  have hlow :
      (rectangleEntries (LeanCo.RectanglePartition.transpose a.1)).1 =
        (rectangleEntries (LeanCo.RectanglePartition.transpose b.1)).1 :=
    Multiset.map_injective Nat.succ_injective hlowMap
  have hsmall :
      LeanCo.RectanglePartition.transpose a.1 =
        LeanCo.RectanglePartition.transpose b.1 := by
    apply rectangleEntries_injective
    apply Subtype.ext
    exact hlow
  have hfirst : a.1 = b.1 := by
    have h := congrArg LeanCo.RectanglePartition.transpose hsmall
    simpa using h
  apply Sigma.ext hfirst
  simpa using hsecond

theorem nonRascoeCodeParts_injective {n m : ℕ}
    (hn : 2 ≤ n) (hm : m ≤ n) :
    Function.Injective (nonRascoeCodeParts n m) := by
  intro a b hab
  have hfiltered := congrArg (Multiset.filter (n < ·)) hab
  rw [filter_gt_nonRascoeCodeParts hn,
    filter_gt_nonRascoeCodeParts hn] at hfiltered
  have hweak : weakEntriesMultiset a.2 = weakEntriesMultiset b.2 :=
    Multiset.map_injective (fun x y h ↦ by omega) hfiltered
  have hsecond : a.2 = b.2 := weakEntriesMultiset_injective hweak
  have hab' := hab
  simp only [nonRascoeCodeParts] at hab'
  have hhighMap :
      (weakEntriesMultiset a.2).map (fun x ↦ x + (n + 1)) =
        (weakEntriesMultiset b.2).map (fun x ↦ x + (n + 1)) :=
    congrArg (Multiset.map (fun x ↦ x + (n + 1))) hweak
  rw [hhighMap] at hab'
  have hlowMap :
      (rectangleEntries (LeanCo.RectanglePartition.transpose a.1)).1.map Nat.succ =
        (rectangleEntries (LeanCo.RectanglePartition.transpose b.1)).1.map Nat.succ :=
    add_left_cancel hab'
  have hlow :
      (rectangleEntries (LeanCo.RectanglePartition.transpose a.1)).1 =
        (rectangleEntries (LeanCo.RectanglePartition.transpose b.1)).1 :=
    Multiset.map_injective Nat.succ_injective hlowMap
  have hsmall :
      LeanCo.RectanglePartition.transpose a.1 =
        LeanCo.RectanglePartition.transpose b.1 := by
    apply rectangleEntries_injective
    apply Subtype.ext
    exact hlow
  have hfirst : a.1 = b.1 := by
    have h := congrArg LeanCo.RectanglePartition.transpose hsmall
    simpa using h
  apply Sigma.ext hfirst
  simpa using hsecond

theorem decodeRascoeLayerCode_injective
    (d n m : ℕ) (hn : 2 ≤ n) (hm : m < n) :
    Function.Injective (decodeRascoeLayerCode d n m hn hm) := by
  intro a b hab
  apply Subtype.ext
  apply rascoeCodeParts_injective hn hm
  exact congrArg (fun p ↦ p.1.parts) hab

theorem decodeNonRascoeLayerCode_injective
    (d n m : ℕ) (hn : 2 ≤ n) (hm : m ≤ n) :
    Function.Injective (decodeNonRascoeLayerCode d n m hn hm) := by
  intro a b hab
  apply Subtype.ext
  apply nonRascoeCodeParts_injective hn hm
  exact congrArg (fun p ↦ p.1.parts) hab

/-- Weight-preserving code/literal-layer equivalence for Rascoe partitions. -/
noncomputable def rascoeCodeEquivLayer
    (d n m : ℕ) (hn : 2 ≤ n) (hm : m < n) :
    RascoeCodeFiber d n m ≃ ↥(rascoeLayer d n m) :=
  Equiv.ofBijective (decodeRascoeLayerCode d n m hn hm)
    ⟨decodeRascoeLayerCode_injective d n m hn hm, fun p ↦
      ⟨encodeRascoeCode d n m hn hm p,
        decodeRascoeLayerCode_encodeRascoeCode d n m hn hm p⟩⟩

/-- Weight-preserving code/literal-layer equivalence for non-Rascoe
partitions. -/
noncomputable def nonRascoeCodeEquivLayer
    (d n m : ℕ) (hn : 2 ≤ n) (hm : m ≤ n) :
    NonRascoeCodeFiber d n m ≃ ↥(nonRascoeLayer d n m) :=
  Equiv.ofBijective (decodeNonRascoeLayerCode d n m hn hm)
    ⟨decodeNonRascoeLayerCode_injective d n m hn hm, fun p ↦
      ⟨encodeNonRascoeCode d n m hn hm p,
        decodeNonRascoeLayerCode_encodeNonRascoeCode d n m hn hm p⟩⟩

/-! ### Coefficients of a rectangle times a weak-tuple reciprocal -/

/-- Number of pairs consisting of a rectangle partition and a weakly
decreasing tuple whose weights, together with `base`, add to `d`.  The
definition is manifestly finite: after choosing the rectangle, the tuple is
taken from one fixed finite weight fiber. -/
noncomputable def rectangleTupleCount
    (base rows cols m d : ℕ) : ℕ :=
  ∑ p : LeanCo.RectanglePartition rows cols,
    if base + p.weight ≤ d then
      (WeakDescending.weightFiber m (d - (base + p.weight))).card
    else 0

/-- The corresponding finite set of actual rectangle/tuple codes. -/
noncomputable def rectangleTupleFiber
    (base rows cols m d : ℕ) :
    Finset (Σ _p : LeanCo.RectanglePartition rows cols, WeakDescending m) :=
  Finset.univ.sigma fun p ↦
    if base + p.weight ≤ d then
      WeakDescending.weightFiber m (d - (base + p.weight))
    else ∅

@[simp] theorem mem_rectangleTupleFiber
    {base rows cols m d : ℕ}
    {z : Σ _p : LeanCo.RectanglePartition rows cols, WeakDescending m} :
    z ∈ rectangleTupleFiber base rows cols m d ↔
      base + z.1.weight + WeakDescending.weight z.2 = d := by
  classical
  simp only [rectangleTupleFiber, Finset.mem_sigma, Finset.mem_univ, true_and]
  split_ifs with h
  · simp only [WeakDescending.mem_weightFiber]
    omega
  · simp only [Finset.notMem_empty, false_iff]
    intro heq
    apply h
    omega

theorem card_rectangleTupleFiber (base rows cols m d : ℕ) :
    (rectangleTupleFiber base rows cols m d).card =
      rectangleTupleCount base rows cols m d := by
  classical
  simp only [rectangleTupleFiber, Finset.card_sigma, Finset.mem_univ,
    rectangleTupleCount]
  apply Finset.sum_congr rfl
  intro hp
  split_ifs <;> simp

noncomputable def rascoeCodeFiberEquivRectangleFiber
    (d n m : ℕ) :
    RascoeCodeFiber d n m ≃
      ↥(rectangleTupleFiber (m * n + 2 * n - 1) (n - 1)
        (n - m - 1) m d) where
  toFun z := ⟨z.1, mem_rectangleTupleFiber.mpr z.2⟩
  invFun z := ⟨z.1, mem_rectangleTupleFiber.mp z.2⟩
  left_inv z := by cases z; rfl
  right_inv z := by cases z; rfl

noncomputable def nonRascoeCodeFiberEquivRectangleFiber
    (d n m : ℕ) :
    NonRascoeCodeFiber d n m ≃
      ↥(rectangleTupleFiber (m * n + n) (n - 2) (n - m) m d) where
  toFun z := ⟨z.1, mem_rectangleTupleFiber.mpr z.2⟩
  invFun z := ⟨z.1, mem_rectangleTupleFiber.mp z.2⟩
  left_inv z := by cases z; rfl
  right_inv z := by cases z; rfl

/-- The literal Rascoe layer has exactly the rectangle/tuple fiber count. -/
theorem card_rascoeLayer_eq_rectangleTupleCount
    (d n m : ℕ) (hn : 2 ≤ n) (hm : m < n) :
    (rascoeLayer d n m).card =
      rectangleTupleCount (m * n + 2 * n - 1) (n - 1)
        (n - m - 1) m d := by
  let e : ↥(rectangleTupleFiber (m * n + 2 * n - 1) (n - 1)
      (n - m - 1) m d) ≃ ↥(rascoeLayer d n m) :=
    (rascoeCodeFiberEquivRectangleFiber d n m).symm.trans
      (rascoeCodeEquivLayer d n m hn hm)
  calc
    (rascoeLayer d n m).card = Fintype.card ↥(rascoeLayer d n m) := by simp
    _ = Fintype.card ↥(rectangleTupleFiber (m * n + 2 * n - 1) (n - 1)
        (n - m - 1) m d) := (Fintype.card_congr e).symm
    _ = (rectangleTupleFiber (m * n + 2 * n - 1) (n - 1)
        (n - m - 1) m d).card := by simp
    _ = rectangleTupleCount (m * n + 2 * n - 1) (n - 1)
        (n - m - 1) m d := card_rectangleTupleFiber _ _ _ _ _

/-- The literal non-Rascoe layer has the analogous code count. -/
theorem card_nonRascoeLayer_eq_rectangleTupleCount
    (d n m : ℕ) (hn : 2 ≤ n) (hm : m ≤ n) :
    (nonRascoeLayer d n m).card =
      rectangleTupleCount (m * n + n) (n - 2) (n - m) m d := by
  let e : ↥(rectangleTupleFiber (m * n + n) (n - 2) (n - m) m d) ≃
      ↥(nonRascoeLayer d n m) :=
    (nonRascoeCodeFiberEquivRectangleFiber d n m).symm.trans
      (nonRascoeCodeEquivLayer d n m hn hm)
  calc
    (nonRascoeLayer d n m).card = Fintype.card ↥(nonRascoeLayer d n m) := by simp
    _ = Fintype.card ↥(rectangleTupleFiber (m * n + n) (n - 2)
        (n - m) m d) := (Fintype.card_congr e).symm
    _ = (rectangleTupleFiber (m * n + n) (n - 2) (n - m) m d).card := by simp
    _ = rectangleTupleCount (m * n + n) (n - 2) (n - m) m d :=
      card_rectangleTupleFiber _ _ _ _ _

/-- Coefficient extraction for the product of a rectangle enumerator, a
baseline monomial, and the finite Euler reciprocal. -/
theorem coeff_rectangle_tuple_product (base rows cols m d : ℕ) :
    coeff d ((X : ℤ⟦X⟧) ^ base *
      (∑ p : LeanCo.RectanglePartition rows cols, X ^ p.weight) *
      reciprocalFiniteEuler m) = (rectangleTupleCount base rows cols m d : ℤ) := by
  rw [← WeakDescending.weightSeries_eq_reciprocalFiniteEuler]
  rw [Finset.mul_sum, Finset.sum_mul, map_sum]
  simp_rw [← pow_add, coeff_X_pow_mul']
  simp_rw [WeakDescending.coeff_weightSeries]
  simp only [rectangleTupleCount, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]

/-- One Rascoe summand in Theorem 1.1.  Its intended range is `2≤n` and
`m<n`; this avoids the paper's negative Gaussian lower index. -/
noncomputable def rascoeGaussianTerm (n m : ℕ) : ℤ⟦X⟧ :=
  qBinomialEval (X : ℤ⟦X⟧) (2 * n - m - 2) (n - m - 1) *
    X ^ (m * n + 2 * n - 1) * reciprocalFiniteEuler m

/-- One non-Rascoe summand in Theorem 1.1. -/
noncomputable def nonRascoeGaussianTerm (n m : ℕ) : ℤ⟦X⟧ :=
  qBinomialEval (X : ℤ⟦X⟧) (2 * n - m - 2) (n - m) *
    X ^ (m * n + n) * reciprocalFiniteEuler m

/-- The coefficient of a Rascoe paper summand is the literal finite count of
its rectangle/weak-tuple codes. -/
theorem coeff_rascoeGaussianTerm_eq_rectangleTupleCount
    (d n m : ℕ) (hn : 2 ≤ n) (hm : m < n) :
    coeff d (rascoeGaussianTerm n m) =
      (rectangleTupleCount (m * n + 2 * n - 1) (n - 1)
        (n - m - 1) m d : ℤ) := by
  have hcol : n - m - 1 ≤ 2 * n - m - 2 := by omega
  have hrow : (2 * n - m - 2) - (n - m - 1) = n - 1 := by omega
  rw [rascoeGaussianTerm, qBinomialEval_eq_rectangle X hcol, hrow]
  rw [show
      (∑ p : LeanCo.RectanglePartition (n - 1) (n - m - 1), X ^ p.weight) *
          X ^ (m * n + 2 * n - 1) * reciprocalFiniteEuler m =
        X ^ (m * n + 2 * n - 1) *
          (∑ p : LeanCo.RectanglePartition (n - 1) (n - m - 1), X ^ p.weight) *
          reciprocalFiniteEuler m by ring]
  exact coeff_rectangle_tuple_product _ _ _ _ _

/-- The analogous coefficient formula for a non-Rascoe paper summand. -/
theorem coeff_nonRascoeGaussianTerm_eq_rectangleTupleCount
    (d n m : ℕ) (hn : 2 ≤ n) (hm : m ≤ n) :
    coeff d (nonRascoeGaussianTerm n m) =
      (rectangleTupleCount (m * n + n) (n - 2) (n - m) m d : ℤ) := by
  have hcol : n - m ≤ 2 * n - m - 2 := by omega
  have hrow : (2 * n - m - 2) - (n - m) = n - 2 := by omega
  rw [nonRascoeGaussianTerm, qBinomialEval_eq_rectangle X hcol, hrow]
  rw [show
      (∑ p : LeanCo.RectanglePartition (n - 2) (n - m), X ^ p.weight) *
          X ^ (m * n + n) * reciprocalFiniteEuler m =
        X ^ (m * n + n) *
          (∑ p : LeanCo.RectanglePartition (n - 2) (n - m), X ^ p.weight) *
          reciprocalFiniteEuler m by ring]
  exact coeff_rectangle_tuple_product _ _ _ _ _

/-- Fixed-layer coefficient theorem derived from the literal partition
bijection. -/
theorem coeff_rascoeGaussianTerm_eq_card_layer
    (d n m : ℕ) (hn : 2 ≤ n) (hm : m < n) :
    coeff d (rascoeGaussianTerm n m) = ((rascoeLayer d n m).card : ℤ) := by
  rw [coeff_rascoeGaussianTerm_eq_rectangleTupleCount d n m hn hm,
    card_rascoeLayer_eq_rectangleTupleCount d n m hn hm]

/-- Fixed non-Rascoe layer coefficient theorem. -/
theorem coeff_nonRascoeGaussianTerm_eq_card_layer
    (d n m : ℕ) (hn : 2 ≤ n) (hm : m ≤ n) :
    coeff d (nonRascoeGaussianTerm n m) =
      ((nonRascoeLayer d n m).card : ℤ) := by
  rw [coeff_nonRascoeGaussianTerm_eq_rectangleTupleCount d n m hn hm,
    card_nonRascoeLayer_eq_rectangleTupleCount d n m hn hm]

/-! ### The exceptional length-zero and length-one layers -/

theorem partition_parts_eq_singleton_of_length_one {d : ℕ}
    (p : Nat.Partition d) (h : p.parts.card = 1) : p.parts = {d} := by
  obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp h
  have had : a = d := by simpa [ha] using p.parts_sum
  simpa [had] using ha

theorem card_rascoeLayer_one_zero (d : ℕ) :
    (rascoeLayer d 1 0).card = if d = 1 then 1 else 0 := by
  classical
  by_cases hd : d = 1
  · subst d
    rw [if_pos rfl]
    have hfin : rascoeLayer 1 1 0 = Finset.univ := by
      ext p
      simp [rascoeLayer, IsRascoe, length, aboveLengthCount,
        Nat.Partition.partition_one_parts p]
    rw [hfin]
    simp
  · rw [if_neg hd]
    apply Finset.card_eq_zero.mpr
    ext p
    simp only [Finset.notMem_empty, iff_false]
    intro hp
    have hp' := (Finset.mem_filter.mp hp).2
    have hcard : p.parts.card = 1 := hp'.2.1
    have hparts := partition_parts_eq_singleton_of_length_one p hcard
    have hmem := hp'.1
    change p.parts.card ∈ p.parts at hmem
    rw [hcard, hparts] at hmem
    have heq : 1 = d := by simpa using hmem
    exact hd heq.symm

theorem card_nonRascoeLayer_zero_zero (d : ℕ) :
    (nonRascoeLayer d 0 0).card = if d = 0 then 1 else 0 := by
  classical
  by_cases hd : d = 0
  · subst d
    rw [if_pos rfl]
    have hfin : nonRascoeLayer 0 0 0 = Finset.univ := by
      ext p
      simp [nonRascoeLayer, IsNonRascoe, length, aboveLengthCount,
        Nat.Partition.partition_zero_parts p]
    rw [hfin]
    simp
  · rw [if_neg hd]
    apply Finset.card_eq_zero.mpr
    ext p
    simp only [Finset.notMem_empty, iff_false]
    intro hp
    have hcard : p.parts.card = 0 := (Finset.mem_filter.mp hp).2.2.1
    have hparts : p.parts = 0 := Multiset.card_eq_zero.mp hcard
    apply hd
    simpa [hparts] using p.parts_sum.symm

theorem card_nonRascoeLayer_one_zero (d : ℕ) :
    (nonRascoeLayer d 1 0).card = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  ext p
  simp only [Finset.notMem_empty, iff_false]
  intro hp
  have hp' := (Finset.mem_filter.mp hp).2
  have hcard : p.parts.card = 1 := hp'.2.1
  have hparts := partition_parts_eq_singleton_of_length_one p hcard
  have hdpos : 0 < d := p.parts_pos (by simp [hparts])
  have hdne : d ≠ 1 := by
    intro hd
    apply hp'.1
    change p.parts.card ∈ p.parts
    simp [hcard, hparts, hd]
  have hhigh := hp'.2.2
  have hdle : d ≤ 1 := by
    by_contra hnot
    have hgt : 1 < d := Nat.lt_of_not_ge hnot
    simp [aboveLengthCount, hparts, hgt] at hhigh
    exact (not_le_of_gt hgt) hhigh
  omega

theorem card_nonRascoeLayer_one_one (d : ℕ) :
    (nonRascoeLayer d 1 1).card = if 2 ≤ d then 1 else 0 := by
  classical
  by_cases hd : 2 ≤ d
  · rw [if_pos hd]
    have hfin : nonRascoeLayer d 1 1 = {Nat.Partition.indiscrete d} := by
      ext p
      constructor
      · intro hp
        have hcard : p.parts.card = 1 := (Finset.mem_filter.mp hp).2.2.1
        have hparts := partition_parts_eq_singleton_of_length_one p hcard
        simp only [Finset.mem_singleton]
        apply Nat.Partition.ext
        rw [hparts, Nat.Partition.indiscrete_parts (by omega)]
      · intro hp
        simp only [Finset.mem_singleton] at hp
        subst p
        have hparts : (Nat.Partition.indiscrete d).parts = {d} :=
          Nat.Partition.indiscrete_parts (by omega)
        change Nat.Partition.indiscrete d ∈ nonRascoeLayer d 1 1
        rw [nonRascoeLayer]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [show length (Nat.Partition.indiscrete d) = 1 by
          simp [length, hparts]]
        constructor
        · simp [IsNonRascoe, length, hparts]
          omega
        · constructor
          · rfl
          · simp only [aboveLengthCount]
            rw [hparts, Multiset.filter_singleton]
            rw [if_pos (show 1 < d by omega)]
            simp
    rw [hfin]
    simp
  · rw [if_neg hd]
    apply Finset.card_eq_zero.mpr
    ext p
    simp only [Finset.notMem_empty, iff_false]
    intro hp
    have hp' := (Finset.mem_filter.mp hp).2
    have hcard : p.parts.card = 1 := hp'.2.1
    have hparts := partition_parts_eq_singleton_of_length_one p hcard
    have hdpos : 0 < d := p.parts_pos (by simp [hparts])
    have hdne : d ≠ 1 := by
      intro hdone
      apply hp'.1
      change p.parts.card ∈ p.parts
      simp [hcard, hparts, hdone]
    omega

/-- Coefficientwise locally finite realization of
`X + Σ_{n≥2} Σ_{m<n} rascoeGaussianTerm n m`.

Only `n≤d` can contribute to coefficient `d`, hence the defining sum is
finite without an analytic convergence premise. -/
noncomputable def rascoeGaussianDoubleSeries : ℤ⟦X⟧ :=
  X + PowerSeries.mk fun d ↦
    ∑ n ∈ Finset.Icc 2 d,
      ∑ m ∈ Finset.range n, coeff d (rascoeGaussianTerm n m)

/-- Coefficientwise locally finite realization of the non-Rascoe middle
expression, including its two exceptional initial pieces. -/
noncomputable def nonRascoeGaussianDoubleSeries : ℤ⟦X⟧ :=
  1 + X ^ 2 * reciprocalFiniteEuler 1 +
    PowerSeries.mk fun d ↦
      ∑ n ∈ Finset.Icc 2 d,
        ∑ m ∈ Finset.range (n + 1), coeff d (nonRascoeGaussianTerm n m)

/-! ### The two formal double-sum identities -/

/-- The unique weakly decreasing one-tuple of weight `d`. -/
noncomputable def oneWeakDescending (d : ℕ) : WeakDescending 1 :=
  ⟨fun _ ↦ d, antitone_const⟩

theorem weightFiber_one (d : ℕ) :
    WeakDescending.weightFiber 1 d = {oneWeakDescending d} := by
  classical
  ext a
  simp only [WeakDescending.mem_weightFiber, Finset.mem_singleton]
  constructor
  · intro ha
    apply Subtype.ext
    funext i
    fin_cases i
    simpa [WeakDescending.weight, oneWeakDescending] using ha
  · intro ha
    subst a
    simp [WeakDescending.weight, oneWeakDescending]

/-- Every coefficient of `(X;X)₁⁻¹ = (1-X)⁻¹` is one. -/
theorem coeff_reciprocalFiniteEuler_one (d : ℕ) :
    coeff d (reciprocalFiniteEuler 1) = 1 := by
  rw [← WeakDescending.weightSeries_eq_reciprocalFiniteEuler,
    WeakDescending.coeff_weightSeries, weightFiber_one]
  simp

theorem coeff_shifted_reciprocal_one (d : ℕ) :
    coeff d ((X : ℤ⟦X⟧) ^ 2 * reciprocalFiniteEuler 1) =
      if 2 ≤ d then 1 else 0 := by
  rw [coeff_X_pow_mul']
  split_ifs with hd
  · exact coeff_reciprocalFiniteEuler_one _
  · rfl

/-- The displayed Rascoe Gaussian double sum is the literal partition
generating series. -/
theorem rascoeGaussianDoubleSeries_eq_literalRascoeDoubleSeries :
    rascoeGaussianDoubleSeries = literalRascoeDoubleSeries := by
  ext d
  simp only [rascoeGaussianDoubleSeries, literalRascoeDoubleSeries,
    map_add, coeff_X, coeff_mk]
  by_cases hd0 : d = 0
  · subst d
    simp
  by_cases hd1 : d = 1
  · subst d
    have hrange2 : Finset.range 2 = {0, 1} := by
      ext n
      simp
      omega
    rw [hrange2]
    simp [card_rascoeLayer_one_zero]
  have hd2 : 2 ≤ d := by omega
  have hrange : Finset.range (d + 1) =
      insert 0 (insert 1 (Finset.Icc 2 d)) := by
    ext n
    simp only [mem_range, mem_insert, mem_Icc]
    omega
  rw [hrange]
  simp [card_rascoeLayer_one_zero, hd1, coeff_X]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  rw [coeff_rascoeGaussianTerm_eq_card_layer d n m
    (Finset.mem_Icc.mp hn).1 (Finset.mem_range.mp hm)]

/-- The displayed non-Rascoe double sum, including its exceptional initial
series, is the literal non-Rascoe partition series. -/
theorem nonRascoeGaussianDoubleSeries_eq_literalNonRascoeDoubleSeries :
    nonRascoeGaussianDoubleSeries = literalNonRascoeDoubleSeries := by
  ext d
  simp only [nonRascoeGaussianDoubleSeries, literalNonRascoeDoubleSeries,
    map_add, coeff_mk]
  by_cases hd0 : d = 0
  · subst d
    simp [coeff_shifted_reciprocal_one, card_nonRascoeLayer_zero_zero]
  by_cases hd1 : d = 1
  · subst d
    have hrange2 : Finset.range 2 = {0, 1} := by
      ext n
      simp
      omega
    rw [hrange2]
    simp [coeff_shifted_reciprocal_one, card_nonRascoeLayer_zero_zero]
    rw [hrange2]
    simp [card_nonRascoeLayer_one_zero, card_nonRascoeLayer_one_one]
  have hd2 : 2 ≤ d := by omega
  have hrange : Finset.range (d + 1) =
      insert 0 (insert 1 (Finset.Icc 2 d)) := by
    ext n
    simp only [mem_range, mem_insert, mem_Icc]
    omega
  rw [hrange]
  have hrange2 : Finset.range 2 = {0, 1} := by
    ext n
    simp
    omega
  simp [coeff_shifted_reciprocal_one, hd2,
    card_nonRascoeLayer_zero_zero, hd0]
  rw [hrange2]
  simp [card_nonRascoeLayer_one_zero, card_nonRascoeLayer_one_one, hd2]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  rw [coeff_nonRascoeGaussianTerm_eq_card_layer d n m
    (Finset.mem_Icc.mp hn).1 (Nat.le_of_lt_succ (Finset.mem_range.mp hm))]

/-- First formal-power-series double-sum identity of Theorem 1.1. -/
theorem rascoeGaussianDoubleSeries_eq_rascoeSeries :
    rascoeGaussianDoubleSeries = rascoeSeries ℤ :=
  rascoeGaussianDoubleSeries_eq_literalRascoeDoubleSeries.trans
    literalRascoeDoubleSeries_eq_rascoeSeries

/-- Second formal-power-series double-sum identity of Theorem 1.1. -/
theorem nonRascoeGaussianDoubleSeries_eq_nonRascoeSeries :
    nonRascoeGaussianDoubleSeries = nonRascoeSeries ℤ :=
  nonRascoeGaussianDoubleSeries_eq_literalNonRascoeDoubleSeries.trans
    literalNonRascoeDoubleSeries_eq_nonRascoeSeries

end LeanCo.Rascoe
