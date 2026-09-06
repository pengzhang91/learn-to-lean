import LeanCo.CyclicBraidArrangement.ArrangementOrbitBridge
import LeanCo.CyclicBraidArrangement.ZModPlacement
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Anchored finite-field points and cyclic gap placements

This file identifies actual complement points in `ZMod q`, modulo simultaneous
translation, with normalized cyclic orders carrying all-pair-safe gap vectors.
The forward map sorts the canonical representatives `ZMod.val`; the inverse map
uses the residue realization of a circle placement.
-/

namespace CyclicBraidArrangement

open scoped BigOperators

set_option maxHeartbeats 800000

namespace DeformationMatrix

variable {n q : ℕ} [NeZero n] [NeZero q]

/-- The coordinate function of a genuine complement point is injective,
because the distance-zero equation occurs for every ordered pair of distinct
labels. -/
theorem anchoredCoordinates_injective (M : DeformationMatrix n)
    (x : M.AnchoredFiniteFieldComplement (ZMod q)) :
    Function.Injective x.1.1 := by
  intro a b hab
  by_contra hne
  let e : M.ForbiddenEquation :=
    ⟨a, ⟨b, Ne.symm hne⟩, ⟨0, Nat.succ_pos _⟩⟩
  apply x.1.2 e
  simp [SatisfiesEquation, e, ForbiddenEquation.source,
    ForbiddenEquation.target, ForbiddenEquation.distance, hab]

/-- Canonical representatives of the coordinates, indexed by labels. -/
def anchoredVal (M : DeformationMatrix n)
    (x : M.AnchoredFiniteFieldComplement (ZMod q)) (a : Fin n) : ℕ :=
  (x.1.1 a).val

theorem anchoredVal_injective (M : DeformationMatrix n)
    (x : M.AnchoredFiniteFieldComplement (ZMod q)) :
    Function.Injective (M.anchoredVal x) :=
  (ZMod.val_injective q).comp (M.anchoredCoordinates_injective x)

/-- The cyclic order obtained by sorting the canonical representatives. -/
noncomputable def anchoredOrder (M : DeformationMatrix n)
    (x : M.AnchoredFiniteFieldComplement (ZMod q)) : NormalizedCycle n := by
  let f := M.anchoredVal x
  let w : CyclicOrdering n := Tuple.sort f
  refine ⟨w, ?_⟩
  have hmono : Monotone (f ∘ w) := Tuple.monotone_sort f
  let k : Fin n := w.symm 0
  have hle : f (w 0) ≤ f (w k) := hmono (Fin.zero_le k)
  have hwk : w k = 0 := w.apply_symm_apply 0
  have hfzero : f 0 = 0 := by
    change (x.1.1 0).val = 0
    rw [x.2]
    exact ZMod.val_zero
  have hf : f (w 0) = 0 := by
    rw [hwk, hfzero] at hle
    omega
  apply M.anchoredVal_injective x
  change f (w 0) = f 0
  exact hf.trans hfzero.symm

/-- Sorted coordinate values. -/
noncomputable def sortedVal (M : DeformationMatrix n)
    (x : M.AnchoredFiniteFieldComplement (ZMod q)) (k : Fin n) : ℕ :=
  M.anchoredVal x ((M.anchoredOrder x).1 k)

theorem sortedVal_strictMono (M : DeformationMatrix n)
    (x : M.AnchoredFiniteFieldComplement (ZMod q)) :
    StrictMono (M.sortedVal x) := by
  change StrictMono (M.anchoredVal x ∘ Tuple.sort (M.anchoredVal x))
  exact (Tuple.monotone_sort (M.anchoredVal x)).strictMono_of_injective
    ((M.anchoredVal_injective x).comp (Tuple.sort (M.anchoredVal x)).injective)

@[simp] theorem sortedVal_zero (M : DeformationMatrix n)
    (x : M.AnchoredFiniteFieldComplement (ZMod q)) :
    M.sortedVal x 0 = 0 := by
  change M.anchoredVal x ((M.anchoredOrder x).1 0) = 0
  rw [(M.anchoredOrder x).2]
  change (x.1.1 0).val = 0
  rw [x.2]
  exact ZMod.val_zero

theorem sortedVal_lt_modulus (M : DeformationMatrix n)
    (x : M.AnchoredFiniteFieldComplement (ZMod q)) (k : Fin n) :
    M.sortedVal x k < q := by
  exact ZMod.val_lt _

/-- The positive clockwise step between consecutive sorted coordinates,
including the wrap from the largest representative back to zero. -/
noncomputable def sortedEdge (M : DeformationMatrix n)
    (x : M.AnchoredFiniteFieldComplement (ZMod q)) (k : Fin n) : ℕ :=
  if h : k.val + 1 < n then
    M.sortedVal x ⟨k.val + 1, h⟩ - M.sortedVal x k
  else q - M.sortedVal x k

theorem sortedEdge_pos (M : DeformationMatrix n)
    (x : M.AnchoredFiniteFieldComplement (ZMod q)) (k : Fin n) :
    0 < M.sortedEdge x k := by
  unfold sortedEdge
  split_ifs with h
  · exact Nat.sub_pos_of_lt (M.sortedVal_strictMono x (by
      change k.val < k.val + 1
      omega))
  · exact Nat.sub_pos_of_lt (M.sortedVal_lt_modulus x k)

private def clampIndex (m i : ℕ) : Fin (m + 1) :=
  ⟨min i m, Nat.lt_succ_of_le (Nat.min_le_right i m)⟩

private theorem clampIndex_mono (m : ℕ) : Monotone (clampIndex m) := by
  intro i j hij
  apply Fin.mk_le_mk.mpr
  exact min_le_min_right m hij

private theorem clampIndex_eq_of_le (m i : ℕ) (hi : i ≤ m) :
    clampIndex m i = ⟨i, Nat.lt_succ_of_le hi⟩ := by
  apply Fin.ext
  simp [clampIndex, Nat.min_eq_left hi]

private theorem sum_fin_adjacent_tsub {m : ℕ} (y : Fin (m + 1) → ℕ)
    (hy : Monotone y) :
    (∑ i : Fin m, (y (Fin.succ i) - y (Fin.castSucc i))) =
      y (Fin.last m) - y 0 := by
  let f : ℕ → ℕ := fun i ↦ y (clampIndex m i)
  have hf : Monotone f := hy.comp (clampIndex_mono m)
  have htel := Finset.sum_range_tsub hf m
  rw [Finset.sum_fin_eq_sum_range]
  calc
    (∑ i ∈ Finset.range m,
        if h : i < m then
          y (Fin.succ (⟨i, h⟩ : Fin m)) -
            y (Fin.castSucc (⟨i, h⟩ : Fin m)) else 0) =
        ∑ i ∈ Finset.range m, (f (i + 1) - f i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have him : i < m := Finset.mem_range.mp hi
      rw [dif_pos him]
      simp [f, clampIndex, Nat.min_eq_left (Nat.le_of_lt him),
        Nat.min_eq_left (Nat.succ_le_of_lt him)]
    _ = f m - f 0 := htel
    _ = y (Fin.last m) - y 0 := by
      simp [f, clampIndex, Fin.last]

/-- The clockwise edge lengths of sorted representatives telescope to one
full turn around the `q` residues. -/
theorem sum_sortedEdge (M : DeformationMatrix n)
    (x : M.AnchoredFiniteFieldComplement (ZMod q)) :
    ∑ k, M.sortedEdge x k = q := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ m =>
      let y : Fin (m + 1) → ℕ := M.sortedVal x
      have htel' :
          (∑ i : Fin m, (y (Fin.succ i) - y (Fin.castSucc i))) =
            y (Fin.last m) - y 0 :=
        sum_fin_adjacent_tsub y (M.sortedVal_strictMono x).monotone
      rw [Fin.sum_univ_castSucc]
      change (∑ i : Fin m,
          (if h : i.castSucc.val + 1 < m + 1 then
            y ⟨i.castSucc.val + 1, h⟩ - y i.castSucc
          else q - y i.castSucc)) +
        (if h : (Fin.last m).val + 1 < m + 1 then
          y ⟨(Fin.last m).val + 1, h⟩ - y (Fin.last m)
        else q - y (Fin.last m)) = q
      simp only [Fin.val_castSucc, Fin.val_last]
      have hi (i : Fin m) : i.val + 1 < m + 1 := Nat.succ_lt_succ i.isLt
      simp_rw [dif_pos (hi _)]
      rw [dif_neg (lt_irrefl (m + 1))]
      have hsucc (i : Fin m) :
          (⟨i.val + 1, hi i⟩ : Fin (m + 1)) = i.succ := by
        apply Fin.ext
        rfl
      simp_rw [hsucc]
      rw [htel']
      have hy0 : y 0 = 0 := M.sortedVal_zero x
      have hylast : y (Fin.last m) < q := M.sortedVal_lt_modulus x _
      omega

/-- Empty-box gaps extracted from the sorted representatives. -/
noncomputable def sortedGap (M : DeformationMatrix n)
    (x : M.AnchoredFiniteFieldComplement (ZMod q)) (k : Fin n) : ℕ :=
  M.sortedEdge x k - 1

theorem sum_sortedGap (M : DeformationMatrix n)
    (x : M.AnchoredFiniteFieldComplement (ZMod q)) (hq : n ≤ q) :
    ∑ k, M.sortedGap x k = q - n := by
  have hedge (k : Fin n) : M.sortedGap x k + 1 = M.sortedEdge x k := by
    exact Nat.sub_add_cancel (M.sortedEdge_pos x k)
  have hsumadd : (∑ k, M.sortedGap x k) + n =
      ∑ k, M.sortedEdge x k := by
    calc
      (∑ k, M.sortedGap x k) + n =
          ∑ k : Fin n, (M.sortedGap x k + 1) := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, Finset.card_fin, smul_eq_mul, mul_one]
      _ = ∑ k, M.sortedEdge x k := by
        apply Finset.sum_congr rfl
        intro k hk
        exact hedge k
  rw [M.sum_sortedEdge x] at hsumadd
  omega

/-- The gap vector decoded from an anchored complement point. -/
noncomputable def anchoredGapVector (M : DeformationMatrix n)
    (x : M.AnchoredFiniteFieldComplement (ZMod q)) (hq : n ≤ q) :
    GapVector n q :=
  ⟨M.sortedGap x, M.sum_sortedGap x hq⟩

/-- The complete circle placement decoded by sorting an anchored complement
point and taking successive empty-box gaps. -/
noncomputable def anchoredCirclePlacement (M : DeformationMatrix n)
    (x : M.AnchoredFiniteFieldComplement (ZMod q)) (hq : n ≤ q) :
    CirclePlacement n q :=
  ⟨(M.anchoredOrder x).1, M.anchoredGapVector x hq⟩

@[simp] theorem anchoredCirclePlacement_order (M : DeformationMatrix n)
    (x : M.AnchoredFiniteFieldComplement (ZMod q)) (hq : n ≤ q) :
    (M.anchoredCirclePlacement x hq).order = (M.anchoredOrder x).1 := rfl

@[simp] theorem anchoredCirclePlacement_gap (M : DeformationMatrix n)
    (x : M.AnchoredFiniteFieldComplement (ZMod q)) (hq : n ≤ q)
    (k : Fin n) :
    (M.anchoredCirclePlacement x hq).gaps.gap k = M.sortedGap x k := rfl

/-- Successive sorted coordinates differ by the decoded positive edge length
in `ZMod q`, including at the wrap. -/
theorem anchoredCoordinate_next_sub (M : DeformationMatrix n)
    (x : M.AnchoredFiniteFieldComplement (ZMod q)) (k : Fin n) :
    x.1.1 ((M.anchoredOrder x).1 (nextPosition n k)) -
        x.1.1 ((M.anchoredOrder x).1 k) =
      (M.sortedEdge x k : ZMod q) := by
  by_cases hk : k.val + 1 < n
  · have hnext : nextPosition n k = ⟨k.val + 1, hk⟩ := by
      apply Fin.ext
      simp [nextPosition, Fin.val_add, Nat.mod_eq_of_lt hk]
    have hle : M.sortedVal x k ≤ M.sortedVal x ⟨k.val + 1, hk⟩ :=
      (M.sortedVal_strictMono x (by
        change k.val < k.val + 1
        omega)).le
    rw [hnext]
    unfold sortedEdge
    rw [dif_pos hk, Nat.cast_sub hle]
    simp only [sortedVal, anchoredVal]
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  · have hkn : k.val + 1 = n := by omega
    have hnext : nextPosition n k = 0 := by
      apply Fin.ext
      simp [nextPosition, Fin.val_add, hkn]
    have hle : M.sortedVal x k ≤ q :=
      Nat.le_of_lt (M.sortedVal_lt_modulus x k)
    rw [hnext, (M.anchoredOrder x).2, x.2]
    unfold sortedEdge
    rw [dif_neg hk, Nat.cast_sub hle]
    have hcast : (M.sortedVal x k : ZMod q) =
        x.1.1 ((M.anchoredOrder x).1 k) := by
      simp [sortedVal, anchoredVal]
    rw [hcast]
    simp

@[simp] theorem anchoredCirclePlacement_edgeLength (M : DeformationMatrix n)
    (x : M.AnchoredFiniteFieldComplement (ZMod q)) (hq : n ≤ q)
    (k : Fin n) :
    (M.anchoredCirclePlacement x hq).edgeLength k = M.sortedEdge x k := by
  rw [CirclePlacement.edgeLength, anchoredCirclePlacement_gap, sortedGap]
  exact Nat.sub_add_cancel (M.sortedEdge_pos x k)

/-- Decoding and then realizing the sorted placement recovers every original
coordinate at its sorted position. -/
theorem anchoredCirclePlacement_positionResidue (M : DeformationMatrix n)
    (x : M.AnchoredFiniteFieldComplement (ZMod q)) (hq : n ≤ q)
    (k : Fin n) :
    (M.anchoredCirclePlacement x hq).positionResidue k =
      x.1.1 ((M.anchoredOrder x).1 k) := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ m =>
      induction k using Fin.induction with
      | zero =>
          rw [positionResidue_zero, (M.anchoredOrder x).2, x.2]
      | succ i ih =>
          have hnext : nextPosition (m + 1) i.castSucc = i.succ := by
            apply Fin.ext
            simp [nextPosition]
          have hp := positionResidue_next
            (M.anchoredCirclePlacement x hq) hq i.castSucc
          rw [hnext, M.anchoredCirclePlacement_edgeLength x hq] at hp
          have hx := M.anchoredCoordinate_next_sub x i.castSucc
          rw [hnext] at hx
          linear_combination hp - hx + ih

/-- In named-label coordinates, decoding followed by residue realization is
literally the identity. -/
theorem anchoredCirclePlacement_labelResidue (M : DeformationMatrix n)
    (x : M.AnchoredFiniteFieldComplement (ZMod q)) (hq : n ≤ q)
    (a : Fin n) :
    (M.anchoredCirclePlacement x hq).labelResidue a = x.1.1 a := by
  rw [CirclePlacement.labelResidue,
    M.anchoredCirclePlacement_positionResidue x hq]
  simp [anchoredCirclePlacement]

theorem anchoredCirclePlacement_safe (M : DeformationMatrix n)
    (x : M.AnchoredFiniteFieldComplement (ZMod q)) (hq : n ≤ q) :
    (M.anchoredCirclePlacement x hq).AvoidsEveryOrderedPair M := by
  rw [← avoidsModularHyperplanes_iff_avoidsEveryOrderedPair M
    (M.anchoredCirclePlacement x hq) hq]
  intro a c hac r hr heq
  let e : M.ForbiddenEquation :=
    ⟨a, ⟨c, hac.symm⟩, ⟨r, Nat.lt_succ_of_le hr⟩⟩
  apply x.1.2 e
  unfold SatisfiesEquation
  change x.1.1 c - x.1.1 a = (r : ZMod q)
  rw [← M.anchoredCirclePlacement_labelResidue x hq,
    ← M.anchoredCirclePlacement_labelResidue x hq]
  exact heq

/-- Sort an anchored complement point and retain its safe gap vector. -/
noncomputable def anchoredToSafeGaps (M : DeformationMatrix n) (hq : n ≤ q) :
    M.AnchoredFiniteFieldComplement (ZMod q) →
      Σ w : NormalizedCycle n, FixedOrderSafeGaps M q w.1 :=
  fun x ↦ ⟨M.anchoredOrder x,
    ⟨M.anchoredGapVector x hq, M.anchoredCirclePlacement_safe x hq⟩⟩

/-- Realize safe cyclic gaps as an actual anchored complement point. -/
noncomputable def safeGapsToAnchored (M : DeformationMatrix n) (hq : n ≤ q) :
    (Σ w : NormalizedCycle n, FixedOrderSafeGaps M q w.1) →
      M.AnchoredFiniteFieldComplement (ZMod q) := fun z ↦ by
  let P : CirclePlacement n q := ⟨z.1.1, z.2.1⟩
  have hmod : P.AvoidsModularHyperplanes M :=
    (avoidsModularHyperplanes_iff_avoidsEveryOrderedPair M P hq).2 z.2.2
  have hw0 : z.1.1.symm 0 = 0 := by
    apply z.1.1.injective
    simp [z.1.2]
  refine ⟨⟨P.labelResidue, ?_⟩, ?_⟩
  · intro e he
    apply hmod (e.source M) (e.target M) (e.source_ne_target M)
      (e.distance M) (e.distance_le M)
    exact he
  · simp [CirclePlacement.labelResidue, P, hw0]

/-- The residue realization is a left inverse to sorting and gap decoding. -/
theorem safeGapsToAnchored_anchoredToSafeGaps (M : DeformationMatrix n)
    (hq : n ≤ q) (x : M.AnchoredFiniteFieldComplement (ZMod q)) :
    M.safeGapsToAnchored hq (M.anchoredToSafeGaps hq x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  funext a
  exact M.anchoredCirclePlacement_labelResidue x hq a

/-- Clockwise prefix lengths are strictly increasing before the cut, since
each occupied step contributes at least one. -/
theorem clockwiseDistance_zero_strictMono (P : CirclePlacement n q) :
    StrictMono (fun k : Fin n ↦ P.clockwiseDistance 0 k.val) := by
  intro i j hij
  unfold CirclePlacement.clockwiseDistance
  have hsubset : Finset.range i.val ⊆ Finset.range j.val :=
    Finset.range_mono hij.le
  have himem : i.val ∈ Finset.range j.val := Finset.mem_range.mpr hij
  have hinot : i.val ∉ Finset.range i.val := by simp
  exact Finset.sum_lt_sum_of_subset hsubset himem hinot
    (by simp)
    (by intro k hkj hki; exact Nat.zero_le _)

theorem positionResidue_val (P : CirclePlacement n q) (hq : n ≤ q)
    (k : Fin n) :
    (P.positionResidue k).val = P.clockwiseDistance 0 k.val := by
  unfold CirclePlacement.positionResidue
  rw [ZMod.val_cast_of_lt]
  exact clockwiseDistance_lt_modulus P hq 0 k.val k.isLt

/-- Along its own cyclic order, every circle placement is strictly sorted by
the canonical representatives of its realized residues. -/
theorem labelResidue_order_val_strictMono (P : CirclePlacement n q)
    (hq : n ≤ q) :
    StrictMono (fun k : Fin n ↦ (P.labelResidue (P.order k)).val) := by
  have h := clockwiseDistance_zero_strictMono P
  simpa only [labelResidue_order, positionResidue_val P hq] using h

/-- Sorting the residue realization of normalized safe gaps recovers its
original normalized cyclic order. -/
theorem anchoredOrder_safeGapsToAnchored (M : DeformationMatrix n)
    (hq : n ≤ q)
    (z : Σ w : NormalizedCycle n, FixedOrderSafeGaps M q w.1) :
    M.anchoredOrder (M.safeGapsToAnchored hq z) = z.1 := by
  let P : CirclePlacement n q := ⟨z.1.1, z.2.1⟩
  let x := M.safeGapsToAnchored hq z
  let f : Fin n → ℕ := M.anchoredVal x
  have hstrict : StrictMono (f ∘ z.1.1) := by
    dsimp [f, x, anchoredVal, safeGapsToAnchored]
    change StrictMono (fun k : Fin n ↦
      (P.labelResidue (P.order k)).val)
    exact labelResidue_order_val_strictMono P hq
  have hcomp : f ∘ z.1.1 = f ∘ Tuple.sort f :=
    (Tuple.comp_sort_eq_comp_iff_monotone).2 hstrict.monotone
  apply Subtype.ext
  change Tuple.sort f = z.1.1
  apply Equiv.ext
  intro k
  apply M.anchoredVal_injective x
  exact (congrFun hcomp k).symm

theorem sortedVal_safeGapsToAnchored (M : DeformationMatrix n)
    (hq : n ≤ q)
    (z : Σ w : NormalizedCycle n, FixedOrderSafeGaps M q w.1)
    (k : Fin n) :
    M.sortedVal (M.safeGapsToAnchored hq z) k =
      (⟨z.1.1, z.2.1⟩ : CirclePlacement n q).clockwiseDistance 0 k.val := by
  let P : CirclePlacement n q := ⟨z.1.1, z.2.1⟩
  let x := M.safeGapsToAnchored hq z
  change (x.1.1 ((M.anchoredOrder x).1 k)).val =
    P.clockwiseDistance 0 k.val
  rw [M.anchoredOrder_safeGapsToAnchored hq z]
  change (P.labelResidue (P.order k)).val = P.clockwiseDistance 0 k.val
  rw [labelResidue_order, positionResidue_val P hq]

private theorem cyclicIndex_zero_eq (k : Fin n) :
    cyclicIndex n (0 : Fin n) k.val = k := by
  apply Fin.ext
  simp [cyclicIndex]

private theorem clockwiseDistance_zero_succ_edge (P : CirclePlacement n q)
    (k : Fin n) :
    P.clockwiseDistance 0 (k.val + 1) =
      P.clockwiseDistance 0 k.val + P.edgeLength k := by
  simp [CirclePlacement.clockwiseDistance, Finset.sum_range_succ,
    CirclePlacement.edgeLength, cyclicIndex_zero_eq k]

private theorem clockwiseDistance_zero_full_eq (P : CirclePlacement n q)
    (hq : n ≤ q) : P.clockwiseDistance 0 n = q := by
  unfold CirclePlacement.clockwiseDistance
  change (∑ r ∈ Finset.range n,
    P.edgeLength (cyclicIndex n 0 r)) = q
  rw [← Fin.sum_univ_eq_sum_range]
  simp_rw [cyclicIndex_zero_eq]
  exact sum_edgeLength P hq

theorem sortedEdge_safeGapsToAnchored (M : DeformationMatrix n)
    (hq : n ≤ q)
    (z : Σ w : NormalizedCycle n, FixedOrderSafeGaps M q w.1)
    (k : Fin n) :
    M.sortedEdge (M.safeGapsToAnchored hq z) k =
      (⟨z.1.1, z.2.1⟩ : CirclePlacement n q).edgeLength k := by
  let P : CirclePlacement n q := ⟨z.1.1, z.2.1⟩
  change M.sortedEdge (M.safeGapsToAnchored hq z) k = P.edgeLength k
  unfold sortedEdge
  split_ifs with hk
  · rw [M.sortedVal_safeGapsToAnchored hq z,
      M.sortedVal_safeGapsToAnchored hq z]
    change P.clockwiseDistance 0 (k.val + 1) -
      P.clockwiseDistance 0 k.val = P.edgeLength k
    have hsucc := clockwiseDistance_zero_succ_edge P k
    omega
  · rw [M.sortedVal_safeGapsToAnchored hq z]
    change q - P.clockwiseDistance 0 k.val = P.edgeLength k
    have hkn : k.val + 1 = n := by omega
    have hsucc := clockwiseDistance_zero_succ_edge P k
    have hfull := clockwiseDistance_zero_full_eq P hq
    rw [hkn] at hsucc
    omega

theorem anchoredGapVector_safeGapsToAnchored (M : DeformationMatrix n)
    (hq : n ≤ q)
    (z : Σ w : NormalizedCycle n, FixedOrderSafeGaps M q w.1) :
    M.anchoredGapVector (M.safeGapsToAnchored hq z) hq = z.2.1 := by
  rcases hz : z.2.1 with ⟨gap, hsum⟩
  change (⟨M.sortedGap (M.safeGapsToAnchored hq z), _⟩ : GapVector n q) =
    ⟨gap, hsum⟩
  rw [GapVector.mk.injEq]
  funext k
  rw [sortedGap, M.sortedEdge_safeGapsToAnchored hq z]
  simp [CirclePlacement.edgeLength, hz]

/-- Sorting after residue realization recovers the complete dependent pair
of normalized order and safe gaps. -/
theorem anchoredToSafeGaps_safeGapsToAnchored (M : DeformationMatrix n)
    (hq : n ≤ q)
    (z : Σ w : NormalizedCycle n, FixedOrderSafeGaps M q w.1) :
    M.anchoredToSafeGaps hq (M.safeGapsToAnchored hq z) = z := by
  let x := M.safeGapsToAnchored hq z
  have hw : M.anchoredOrder x = z.1 :=
    M.anchoredOrder_safeGapsToAnchored hq z
  apply Sigma.ext hw
  rw [Subtype.heq_iff_coe_eq (by
    intro G
    change (CirclePlacement.mk (M.anchoredOrder x).1 G).AvoidsEveryOrderedPair M ↔
      (CirclePlacement.mk z.1.1 G).AvoidsEveryOrderedPair M
    rw [hw])]
  exact M.anchoredGapVector_safeGapsToAnchored hq z

/-- Explicit equivalence between the actual anchored finite-field complement
and normalized cyclic orders with genuinely all-pair-safe gaps. -/
noncomputable def anchoredComplementEquivSafeGaps
    (M : DeformationMatrix n) (hq : n ≤ q) :
    M.AnchoredFiniteFieldComplement (ZMod q) ≃
      Σ w : NormalizedCycle n, FixedOrderSafeGaps M q w.1 where
  toFun := M.anchoredToSafeGaps hq
  invFun := M.safeGapsToAnchored hq
  left_inv := M.safeGapsToAnchored_anchoredToSafeGaps hq
  right_inv := M.anchoredToSafeGaps_safeGapsToAnchored hq

/-- Cardinal form of the anchored-point / safe-gap equivalence.  This is the
exact last combinatorial bridge needed by the finite-field method. -/
theorem card_anchoredFiniteFieldComplement_eq_finiteFieldComplementOrbitCount
    (M : DeformationMatrix n) (hq : n ≤ q) :
    Fintype.card (M.AnchoredFiniteFieldComplement (ZMod q)) =
      M.finiteFieldComplementOrbitCount q := by
  rw [Fintype.card_congr (M.anchoredComplementEquivSafeGaps hq),
    Fintype.card_sigma]
  rfl

end DeformationMatrix

end CyclicBraidArrangement
