import LeanCo.CyclicBraidArrangement.AdjacentPlacement
import LeanCo.CyclicBraidArrangement.FiniteFieldCount
import Mathlib.Data.Fintype.EquivFin

/-!
# Counting genuinely all-pair-safe circle placements

This file separates the finite-field complement model from the adjacent-gap
enumeration.  A safe placement is defined by all ordered-pair clockwise
distance inequalities.  Cyclic compatibility is then used to identify safe
placements with the adjacent lower-bound gap vectors, which are counted by
stars and bars in `FiniteFieldGaps`.
-/

namespace CyclicBraidArrangement

open scoped BigOperators

namespace DeformationMatrix

variable {n q : ℕ}

private def GapVector.toBounded (G : GapVector n q) : Fin n → Fin (q + 1) :=
  fun k ↦ ⟨G.gap k, by
    have hk : G.gap k ≤ ∑ i, G.gap i :=
      Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ k)
    rw [G.sum_eq] at hk
    omega⟩

private theorem GapVector.toBounded_injective :
    Function.Injective (@GapVector.toBounded n q) := by
  intro G H h
  cases G with
  | mk g hg =>
    cases H with
    | mk h hh =>
      congr
      funext k
      exact congrArg Fin.val (congrFun h k)

noncomputable instance gapVectorFintype (n q : ℕ) : Fintype (GapVector n q) := by
  letI : Finite (GapVector n q) :=
    Finite.of_injective GapVector.toBounded GapVector.toBounded_injective
  exact Fintype.ofFinite _

private theorem gapVector_ext {n q : ℕ} {G H : GapVector n q}
    (h : G.gap = H.gap) : G = H := by
  cases G
  cases H
  simp_all

/-- Gap vectors for one fixed cyclic ordering satisfying only the adjacent
lower bounds. -/
abbrev FixedOrderAdjacentGaps [NeZero n] (M : DeformationMatrix n) (q : ℕ)
    (w : CyclicOrdering n) :=
  {G : GapVector n q // ∀ k,
    M.entry (w k) (w (nextPosition n k)) ≤ G.gap k}

/-- Gap vectors for one fixed cyclic ordering satisfying every ordered-pair
avoidance inequality. -/
abbrev FixedOrderSafeGaps [NeZero n] (M : DeformationMatrix n) (q : ℕ)
    (w : CyclicOrdering n) :=
  {G : GapVector n q //
    (CirclePlacement.mk w G).AvoidsEveryOrderedPair M}

noncomputable instance fixedOrderAdjacentGapsFintype [NeZero n]
    (M : DeformationMatrix n) (q : ℕ) (w : CyclicOrdering n) :
    Fintype (FixedOrderAdjacentGaps M q w) := Fintype.ofFinite _

noncomputable instance fixedOrderSafeGapsFintype [NeZero n]
    (M : DeformationMatrix n) (q : ℕ) (w : CyclicOrdering n) :
    Fintype (FixedOrderSafeGaps M q w) := Fintype.ofFinite _

/-- All-pair safety in particular implies each adjacent lower bound. -/
theorem adjacentBounds_of_avoidsEveryOrderedPair [NeZero n]
    (M : DeformationMatrix n) (q : ℕ) (P : CirclePlacement n q)
    (hP : P.AvoidsEveryOrderedPair M) : P.AdjacentBounds M := by
  have hall : P.AvoidsAllPairs M :=
    avoidsAllPairs_of_avoidsEveryOrderedPair M P hP
  intro k
  by_cases hn : 2 ≤ n
  · have h := hall k 1 (by omega) hn
    simpa [CirclePlacement.clockwiseDistance, cyclicIndex_succ] using h
  · have hn1 : n = 1 := by
      have hnpos := NeZero.pos n
      omega
    have hnext : nextPosition n k = k := by
      subst n
      exact Subsingleton.elim _ _
    rw [hnext, M.diagonal_zero]
    exact Nat.zero_le _

/-- For a compatible matrix, fixed-order all-pair-safe gap vectors are
equivalent to fixed-order adjacent-bound gap vectors. -/
noncomputable def fixedOrderSafeEquivAdjacent [NeZero n]
    (M : DeformationMatrix n) (hM : M.CyclicallyCompatible)
    (q : ℕ) (hq : n ≤ q) (w : CyclicOrdering n) :
    FixedOrderSafeGaps M q w ≃ FixedOrderAdjacentGaps M q w :=
  Equiv.subtypeEquiv (Equiv.refl _) (by
    intro G
    constructor
    · exact fun h ↦ adjacentBounds_of_avoidsEveryOrderedPair M q
        (CirclePlacement.mk w G) h
    · exact fun h ↦ adjacentBounds_imply_avoidsEveryOrderedPair M hM q hq
        (CirclePlacement.mk w G) h)

/-- The multiset with the prescribed nonnegative remainder count at each gap
position. -/
private noncomputable def gapRemainderMultiset [NeZero n]
    (M : DeformationMatrix n) (q : ℕ) (w : CyclicOrdering n)
    (G : FixedOrderAdjacentGaps M q w) : Multiset (Fin n) :=
  ∑ k ∈ (Finset.univ : Finset (Fin n)),
    Multiset.replicate
      (G.1.gap k - M.entry (w k) (w (nextPosition n k))) k

private theorem card_gapRemainderMultiset [NeZero n]
    (M : DeformationMatrix n) (q : ℕ) (w : CyclicOrdering n)
    (hfit : n + M.cycleWeight w ≤ q)
    (G : FixedOrderAdjacentGaps M q w) :
    (gapRemainderMultiset M q w G).card = q - n - M.cycleWeight w := by
  classical
  have hsum :
      M.cycleWeight w +
          ∑ k, (G.1.gap k - M.entry (w k) (w (nextPosition n k))) =
        ∑ k, G.1.gap k := by
    change (∑ k, M.entry (w k) (w (nextPosition n k))) +
        (∑ k, (G.1.gap k - M.entry (w k) (w (nextPosition n k)))) =
      ∑ k, G.1.gap k
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    exact Nat.add_sub_of_le (G.2 k)
  rw [G.1.sum_eq] at hsum
  have hrem :
      (∑ k : Fin n,
        (G.1.gap k - M.entry (w k) (w (nextPosition n k)))) =
        q - n - M.cycleWeight w := by
    omega
  simp only [gapRemainderMultiset, Multiset.card_sum,
    Multiset.card_replicate]
  exact hrem

private theorem count_gapRemainderMultiset [NeZero n]
    (M : DeformationMatrix n) (q : ℕ) (w : CyclicOrdering n)
    (G : FixedOrderAdjacentGaps M q w) (k : Fin n) :
    (gapRemainderMultiset M q w G).count k =
      G.1.gap k - M.entry (w k) (w (nextPosition n k)) := by
  classical
  let countHom : Multiset (Fin n) →+ ℕ :=
    { toFun := fun s ↦ s.count k
      map_zero' := by simp
      map_add' := by intro s t; exact Multiset.count_add k s t }
  change countHom (gapRemainderMultiset M q w G) = _
  simp [gapRemainderMultiset, countHom, Multiset.count_replicate]

/-- Remainder multisets are exactly the adjacent-bound gap vectors of the
same total size. -/
noncomputable def fixedCycleGapsEquivAdjacent [NeZero n]
    (M : DeformationMatrix n) (q : ℕ) (w : CyclicOrdering n)
    (hfit : n + M.cycleWeight w ≤ q) :
    M.FixedCycleGaps q w ≃ FixedOrderAdjacentGaps M q w := by
  let f : M.FixedCycleGaps q w → FixedOrderAdjacentGaps M q w := fun s ↦
    ⟨⟨M.realizedGap q w s, M.sum_realizedGap q w hfit s⟩,
      fun k ↦ M.adjacent_bound_realizedGap q w s k⟩
  apply Equiv.ofBijective f
  constructor
  · intro s t hst
    apply M.realizedGap_injective q w
    exact congrArg (fun G ↦ G.1.gap) hst
  · intro G
    let s : M.FixedCycleGaps q w := Sym.mk
      (gapRemainderMultiset M q w G)
      (card_gapRemainderMultiset M q w hfit G)
    refine ⟨s, Subtype.ext (gapVector_ext ?_)⟩
    funext k
    change M.realizedGap q w s k = G.1.gap k
    rw [realizedGap]
    change M.entry (w k) (w (nextPosition n k)) +
        (gapRemainderMultiset M q w G).count k = G.1.gap k
    rw [count_gapRemainderMultiset]
    exact Nat.add_sub_of_le (G.2 k)

/-- Exact fixed-order safe-placement count. -/
theorem card_fixedOrderSafeGaps [NeZero n]
    (M : DeformationMatrix n) (hM : M.CyclicallyCompatible)
    (q : ℕ) (hq : n ≤ q) (w : CyclicOrdering n)
    (hfit : n + M.cycleWeight w ≤ q) :
    Fintype.card (FixedOrderSafeGaps M q w) =
      (q - M.cycleWeight w - 1).choose (n - 1) := by
  calc
    Fintype.card (FixedOrderSafeGaps M q w) =
        Fintype.card (FixedOrderAdjacentGaps M q w) :=
      Fintype.card_congr (fixedOrderSafeEquivAdjacent M hM q hq w)
    _ = Fintype.card (M.FixedCycleGaps q w) :=
      (Fintype.card_congr (fixedCycleGapsEquivAdjacent M q w hfit)).symm
    _ = (q - M.cycleWeight w - 1).choose (n - 1) :=
      card_fixedCycleGaps M q w hfit

/-- The actual complement-placement count modulo simultaneous rotation,
defined through normalized cyclic order and all ordered-pair avoidance. -/
noncomputable def finiteFieldComplementOrbitCount [NeZero n]
    (M : DeformationMatrix n) (q : ℕ) : ℕ :=
  ∑ w : NormalizedCycle n, Fintype.card (FixedOrderSafeGaps M q w.1)

/-- Under compatibility, actual all-pair-safe placements are counted by the
adjacent-gap sum used in the main theorem. -/
theorem finiteFieldComplementOrbitCount_eq_gapCount [NeZero n]
    (M : DeformationMatrix n) (hM : M.CyclicallyCompatible)
    (q : ℕ)
    (hfit : ∀ w : NormalizedCycle n, n + M.cycleWeight w.1 ≤ q) :
    finiteFieldComplementOrbitCount M q = adjacentGapOrbitCount M q := by
  classical
  unfold finiteFieldComplementOrbitCount adjacentGapOrbitCount
  apply Finset.sum_congr rfl
  intro w hw
  rw [card_fixedOrderSafeGaps M hM q
      (show n ≤ q by exact (Nat.le_add_right n _).trans (hfit w)) w.1 (hfit w),
    card_fixedCycleGaps M q w.1 (hfit w)]

/-- Evaluation of the cyclic formula by the actual complement-placement count
for all sufficiently large `q`. -/
theorem finiteFieldComplementOrbitCount_eq_cycleFormula [NeZero n]
    (M : DeformationMatrix n) (hM : M.CyclicallyCompatible)
    (q : ℕ)
    (hfit : ∀ w : NormalizedCycle n, n + M.cycleWeight w.1 ≤ q) :
    (finiteFieldComplementOrbitCount M q : ℚ) = cycleFormula M q := by
  rw [finiteFieldComplementOrbitCount_eq_gapCount M hM q hfit]
  exact adjacentGapOrbitCount_eq_cycleFormula M q hfit

end DeformationMatrix

end CyclicBraidArrangement
