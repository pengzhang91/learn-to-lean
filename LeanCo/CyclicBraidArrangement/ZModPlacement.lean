import LeanCo.CyclicBraidArrangement.FiniteFieldPlacementCount
import Mathlib.Data.ZMod.Basic

/-!
# Realizing cyclic gap placements in `ZMod q`

This file supplies the concrete coordinate bridge used implicitly by the
circle model in Section 2 of arXiv:2608.29203.  We normalize simultaneous
translation by placing cyclic position `0` at residue `0`.
-/

namespace CyclicBraidArrangement

open scoped BigOperators

namespace DeformationMatrix

variable {n q : ℕ}

/-- Length of the clockwise edge leaving cyclic position `k`: its empty-box
gap plus the occupied endpoint. -/
def CirclePlacement.edgeLength (P : CirclePlacement n q) (k : Fin n) : ℕ :=
  P.gaps.gap k + 1

/-- The normalized residue attached to a cyclic position.  Position `0` is
fixed at `0`, thereby choosing one representative modulo simultaneous
translation. -/
def CirclePlacement.positionResidue [NeZero n] (P : CirclePlacement n q)
    (k : Fin n) : ZMod q :=
  (P.clockwiseDistance (0 : Fin n) k.val : ZMod q)

/-- The normalized `ZMod q` coordinate of a named label. -/
def CirclePlacement.labelResidue [NeZero n] (P : CirclePlacement n q)
    (a : Fin n) : ZMod q :=
  P.positionResidue (P.order.symm a)

@[simp] theorem positionResidue_zero [NeZero n] (P : CirclePlacement n q) :
    P.positionResidue (0 : Fin n) = 0 := by
  simp [CirclePlacement.positionResidue, CirclePlacement.clockwiseDistance]

@[simp] theorem labelResidue_order [NeZero n] (P : CirclePlacement n q)
    (k : Fin n) :
    P.labelResidue (P.order k) = P.positionResidue k := by
  simp [CirclePlacement.labelResidue]

/-- The edge lengths make one full turn of exactly `q` boxes. -/
theorem sum_edgeLength [NeZero n] (P : CirclePlacement n q) (hq : n ≤ q) :
    ∑ k, P.edgeLength k = q := by
  simp only [CirclePlacement.edgeLength, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_fin, smul_eq_mul, mul_one]
  rw [P.gaps.sum_eq]
  omega

private theorem cyclicIndex_zero_of_lt [NeZero n] (r : ℕ) (hr : r < n) :
    cyclicIndex n (0 : Fin n) r = ⟨r, hr⟩ := by
  apply Fin.ext
  simp [cyclicIndex, Nat.mod_eq_of_lt hr]

private theorem clockwiseDistance_zero_succ [NeZero n]
    (P : CirclePlacement n q) (s : ℕ) (hs : s < n) :
    P.clockwiseDistance (0 : Fin n) (s + 1) =
      P.clockwiseDistance (0 : Fin n) s + P.edgeLength ⟨s, hs⟩ := by
  simp [CirclePlacement.clockwiseDistance, Finset.sum_range_succ,
    CirclePlacement.edgeLength, cyclicIndex_zero_of_lt s hs]

private theorem clockwiseDistance_zero_full [NeZero n]
    (P : CirclePlacement n q) :
    P.clockwiseDistance (0 : Fin n) n = ∑ k, P.edgeLength k := by
  rw [CirclePlacement.clockwiseDistance]
  change (∑ r ∈ Finset.range n, P.edgeLength (cyclicIndex n 0 r)) = _
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro r hr
  rw [dif_pos (Finset.mem_range.mp hr)]
  congr 1
  exact cyclicIndex_zero_of_lt r (Finset.mem_range.mp hr)

private theorem clockwiseDistance_full [NeZero n]
    (P : CirclePlacement n q) (k : Fin n) :
    P.clockwiseDistance k n = ∑ i, P.edgeLength i := by
  rw [CirclePlacement.clockwiseDistance]
  change (∑ r ∈ Finset.range n, P.edgeLength (cyclicIndex n k r)) = _
  calc
    _ = ∑ j : Fin n, P.edgeLength (cyclicIndex n k j.val) := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro r hr
      rw [dif_pos (Finset.mem_range.mp hr)]
    _ = ∑ i : Fin n, P.edgeLength i := by
      simpa [cyclicIndex, add_comm] using
        (Equiv.sum_comp (Equiv.addRight k) P.edgeLength)

/-- Every proper nonempty clockwise path has numerical length strictly below
one full turn. -/
theorem clockwiseDistance_lt_modulus [NeZero n]
    (P : CirclePlacement n q) (hq : n ≤ q) (k : Fin n) (s : ℕ)
    (hs : s < n) : P.clockwiseDistance k s < q := by
  have hsubset : Finset.range s ⊆ Finset.range n :=
    Finset.range_mono (Nat.le_of_lt hs)
  have hs_mem : s ∈ Finset.range n := Finset.mem_range.mpr hs
  have hs_not_mem : s ∉ Finset.range s := by simp
  have hstrict :
      (∑ r ∈ Finset.range s, P.edgeLength (cyclicIndex n k r)) <
        ∑ r ∈ Finset.range n, P.edgeLength (cyclicIndex n k r) := by
    exact Finset.sum_lt_sum_of_subset hsubset hs_mem hs_not_mem
      (by simp [CirclePlacement.edgeLength])
      (by intro j hjn hjs; exact Nat.zero_le _)
  change P.clockwiseDistance k s < P.clockwiseDistance k n at hstrict
  rw [clockwiseDistance_full P k, sum_edgeLength P hq] at hstrict
  exact hstrict

/-- Advancing by one cyclic position adds precisely the corresponding edge
length in `ZMod q`; at the distinguished cut, the full-turn sum is `q` and
therefore vanishes modulo `q`. -/
theorem positionResidue_next [NeZero n] (P : CirclePlacement n q)
    (hq : n ≤ q) (k : Fin n) :
    P.positionResidue (nextPosition n k) - P.positionResidue k =
      (P.edgeLength k : ZMod q) := by
  by_cases hk : k.val + 1 < n
  · have hnext : (nextPosition n k).val = k.val + 1 := by
      simp [nextPosition, Fin.val_add, Nat.mod_eq_of_lt hk]
    rw [CirclePlacement.positionResidue, CirclePlacement.positionResidue, hnext,
      clockwiseDistance_zero_succ P k.val k.isLt]
    simp
  · have hkn : k.val + 1 = n := by omega
    have hnext : nextPosition n k = 0 := by
      apply Fin.ext
      simp [nextPosition, Fin.val_add, hkn]
    have hfull : P.clockwiseDistance (0 : Fin n) (k.val + 1) = q := by
      rw [hkn, clockwiseDistance_zero_full P, sum_edgeLength P hq]
    have hstep := clockwiseDistance_zero_succ P k.val k.isLt
    rw [hfull] at hstep
    rw [hnext, positionResidue_zero]
    change 0 - (P.clockwiseDistance (0 : Fin n) k.val : ZMod q) = _
    have hcast := congrArg (fun z : ℕ ↦ (z : ZMod q)) hstep
    simp only [Nat.cast_add, ZMod.natCast_self] at hcast
    linear_combination hcast

private theorem clockwiseDistance_succ [NeZero n]
    (P : CirclePlacement n q) (k : Fin n) (s : ℕ) :
    P.clockwiseDistance k (s + 1) =
      P.clockwiseDistance k s + P.edgeLength (cyclicIndex n k s) := by
  simp [CirclePlacement.clockwiseDistance, Finset.sum_range_succ,
    CirclePlacement.edgeLength]

/-- Along an arbitrary clockwise path, the difference of the concrete
`ZMod q` coordinates is the cast of its numerical clockwise length. -/
theorem positionResidue_cyclicIndex_sub [NeZero n]
    (P : CirclePlacement n q) (hq : n ≤ q) (k : Fin n) (s : ℕ) :
    P.positionResidue (cyclicIndex n k s) - P.positionResidue k =
      (P.clockwiseDistance k s : ZMod q) := by
  induction s with
  | zero => simp [cyclicIndex, CirclePlacement.clockwiseDistance]
  | succ s ih =>
      rw [cyclicIndex_succ,
        clockwiseDistance_succ P k s, Nat.cast_add]
      have hnext := positionResidue_next P hq (cyclicIndex n k s)
      linear_combination hnext + ih

/-- Coordinate difference between any two distinct named labels.  The
right-hand side is the paper's clockwise distance, now interpreted as a
residue modulo `q`. -/
theorem labelResidue_sub [NeZero n] (P : CirclePlacement n q)
    (hq : n ≤ q) (a c : Fin n) :
    P.labelResidue c - P.labelResidue a =
      (P.labelDistance a c : ZMod q) := by
  rw [CirclePlacement.labelResidue, CirclePlacement.labelResidue,
    CirclePlacement.labelDistance]
  rw [← cyclicIndex_labelSteps P (a := a) (c := c)]
  exact positionResidue_cyclicIndex_sub P hq (P.order.symm a) (P.labelSteps a c)

/-- Named-label clockwise distances are the canonical representatives in
`{1, ..., q - 1}` whenever the labels are distinct. -/
theorem labelDistance_lt_modulus [NeZero n] (P : CirclePlacement n q)
    (hq : n ≤ q) {a c : Fin n} (_hac : a ≠ c) :
    P.labelDistance a c < q := by
  unfold CirclePlacement.labelDistance
  apply clockwiseDistance_lt_modulus P hq
  exact (P.order.symm c - P.order.symm a).isLt

/-- The oriented form of avoiding the interval arrangement modulo `q`.
For every ordered pair `(a,c)`, it excludes the residues
`x_c - x_a = 0,1,...,m_ac`.  Taking both orientations is exactly the paper's
interval `x_i-x_j in [-m_ij,m_ji]` for each `i<j`. -/
def CirclePlacement.AvoidsModularHyperplanes [NeZero n]
    (M : DeformationMatrix n) (P : CirclePlacement n q) : Prop :=
  ∀ a c, a ≠ c → ∀ r : ℕ, r ≤ M.entry a c →
    P.labelResidue c - P.labelResidue a ≠ (r : ZMod q)

/-- The literal unoriented interval convention from the paper: for `i < j`,
exclude `x_i - x_j = s` for every integer
`s ∈ [-m_ij, m_ji]`. -/
def CirclePlacement.AvoidsPaperIntervalHyperplanes [NeZero n]
    (M : DeformationMatrix n) (P : CirclePlacement n q) : Prop :=
  ∀ i j : Fin n, i.val < j.val → ∀ s : ℤ,
    -(M.entry i j : ℤ) ≤ s → s ≤ (M.entry j i : ℤ) →
      P.labelResidue i - P.labelResidue j ≠ (s : ZMod q)

/-- The ordered nonnegative-distance convention is exactly equivalent to the
paper's signed interval convention, over every modulus. -/
theorem avoidsPaperIntervalHyperplanes_iff_avoidsModularHyperplanes [NeZero n]
    (M : DeformationMatrix n) (P : CirclePlacement n q) :
    P.AvoidsPaperIntervalHyperplanes M ↔ P.AvoidsModularHyperplanes M := by
  constructor
  · intro hpaper a c hac r hr hEq
    rcases lt_or_gt_of_ne hac with haclt | hcalt
    · have hrz : (r : ℤ) ≤ (M.entry a c : ℤ) := by exact_mod_cast hr
      have hforbid := hpaper a c haclt (-(r : ℤ))
        (by omega) (by omega)
      apply hforbid
      calc
        P.labelResidue a - P.labelResidue c =
            -(P.labelResidue c - P.labelResidue a) := by abel
        _ = -((r : ℕ) : ZMod q) := congrArg Neg.neg hEq
        _ = ((-(r : ℤ) : ℤ) : ZMod q) := by simp
    · have hforbid := hpaper c a hcalt (r : ℤ)
        (by omega) (by exact_mod_cast hr)
      exact hforbid (by simpa using hEq)
  · intro hord i j hij s hlo hhi hEq
    by_cases hs : 0 ≤ s
    · let r : ℕ := s.toNat
      have hrs : (r : ℤ) = s := Int.toNat_of_nonneg hs
      have hrz : (r : ℤ) ≤ (M.entry j i : ℤ) := hrs.trans_le hhi
      have hr : r ≤ M.entry j i := by exact_mod_cast hrz
      have hcast : ((r : ℕ) : ZMod q) = (s : ZMod q) := by
        simpa using congrArg (fun z : ℤ ↦ (z : ZMod q)) hrs
      exact hord j i (Fin.ne_of_gt hij) r hr (hEq.trans hcast.symm)
    · have hsneg : s < 0 := lt_of_not_ge hs
      let r : ℕ := (-s).toNat
      have hnr : (r : ℤ) = -s := Int.toNat_of_nonneg (by omega)
      have hrz : (r : ℤ) ≤ (M.entry i j : ℤ) := by rw [hnr]; omega
      have hr : r ≤ M.entry i j := by exact_mod_cast hrz
      apply hord i j (Fin.ne_of_lt hij) r hr
      calc
        P.labelResidue j - P.labelResidue i =
            -(P.labelResidue i - P.labelResidue j) := by abel
        _ = -(s : ZMod q) := congrArg Neg.neg hEq
        _ = (r : ZMod q) := by
          rw [← Int.cast_neg, ← hnr]
          simp

/-- Avoiding all modular interval hyperplanes implies the numerical
all-pair clockwise inequalities.  This direction needs no smallness bound. -/
theorem avoidsEveryOrderedPair_of_avoidsModularHyperplanes [NeZero n]
    (M : DeformationMatrix n) (P : CirclePlacement n q) (hq : n ≤ q)
    (hP : P.AvoidsModularHyperplanes M) : P.AvoidsEveryOrderedPair M := by
  intro a c hac
  by_contra hnot
  have hle : P.labelDistance a c ≤ M.entry a c := Nat.le_of_not_gt hnot
  exact hP a c hac (P.labelDistance a c) hle (labelResidue_sub P hq a c)

/-- Numerical all-pair safety implies genuine avoidance of every modular
interval hyperplane.  The proof uses that a proper clockwise distance and
every smaller forbidden residue are both strictly below `q`, so their casts
to `ZMod q` are injective. -/
theorem avoidsModularHyperplanes_of_avoidsEveryOrderedPair [NeZero n]
    (M : DeformationMatrix n) (P : CirclePlacement n q) (hq : n ≤ q)
    (hP : P.AvoidsEveryOrderedPair M) : P.AvoidsModularHyperplanes M := by
  intro a c hac r hr hEq
  have hsafe := hP a c hac
  have hdist : P.labelDistance a c < q :=
    labelDistance_lt_modulus P hq hac
  have hrq : r < q := lt_of_le_of_lt hr (lt_trans hsafe hdist)
  have hcast : (P.labelDistance a c : ZMod q) = (r : ZMod q) := by
    rw [← labelResidue_sub P hq a c]
    exact hEq
  have hval := congrArg ZMod.val hcast
  rw [ZMod.val_cast_of_lt hdist, ZMod.val_cast_of_lt hrq] at hval
  omega

/-- Exact bridge between the gap-level avoidance predicate and actual
`ZMod q` avoidance of the interval hyperplanes.  Its sole size hypothesis is
`n ≤ q`; all required bounds `< q` follow from the gap total and properness of
the clockwise path. -/
theorem avoidsModularHyperplanes_iff_avoidsEveryOrderedPair [NeZero n]
    (M : DeformationMatrix n) (P : CirclePlacement n q) (hq : n ≤ q) :
    P.AvoidsModularHyperplanes M ↔ P.AvoidsEveryOrderedPair M :=
  ⟨avoidsEveryOrderedPair_of_avoidsModularHyperplanes M P hq,
    avoidsModularHyperplanes_of_avoidsEveryOrderedPair M P hq⟩

/-- Literal paper-interval avoidance is equivalent to the gap-level
all-ordered-pairs inequalities. -/
theorem avoidsPaperIntervalHyperplanes_iff_avoidsEveryOrderedPair [NeZero n]
    (M : DeformationMatrix n) (P : CirclePlacement n q) (hq : n ≤ q) :
    P.AvoidsPaperIntervalHyperplanes M ↔ P.AvoidsEveryOrderedPair M :=
  (avoidsPaperIntervalHyperplanes_iff_avoidsModularHyperplanes M P).trans
    (avoidsModularHyperplanes_iff_avoidsEveryOrderedPair M P hq)

/-- Cyclic compatibility turns the adjacent gap bounds into actual avoidance
of every modular interval hyperplane.  No primality assumption on `q` is
used, exactly as in Proposition 2.2. -/
theorem adjacentBounds_imply_avoidsModularHyperplanes [NeZero n]
    (M : DeformationMatrix n) (hM : M.CyclicallyCompatible)
    (P : CirclePlacement n q) (hq : n ≤ q) (hP : P.AdjacentBounds M) :
    P.AvoidsModularHyperplanes M :=
  avoidsModularHyperplanes_of_avoidsEveryOrderedPair M P hq
    (adjacentBounds_imply_avoidsEveryOrderedPair M hM q hq P hP)

/-- Proposition 2.2(ii) in the paper's original signed-interval notation. -/
theorem adjacentBounds_imply_avoidsPaperIntervalHyperplanes [NeZero n]
    (M : DeformationMatrix n) (hM : M.CyclicallyCompatible)
    (P : CirclePlacement n q) (hq : n ≤ q) (hP : P.AdjacentBounds M) :
    P.AvoidsPaperIntervalHyperplanes M :=
  (avoidsPaperIntervalHyperplanes_iff_avoidsModularHyperplanes M P).2
    (adjacentBounds_imply_avoidsModularHyperplanes M hM P hq hP)

end DeformationMatrix

end CyclicBraidArrangement
