import LeanCo.CyclicBraidArrangement.CyclicCompatibility
import Mathlib.Data.Sym.Card

/-! The path inequality and stars-and-bars step in the cyclic-gap proof. -/

namespace CyclicBraidArrangement

open scoped BigOperators

namespace DeformationMatrix

variable {n : ℕ}

/-- Sum of matrix entries along consecutive vertices of a list. -/
def pathWeight (M : DeformationMatrix n) : List (Fin n) → ℕ
  | a :: b :: rest => M.entry a b + pathWeight M (b :: rest)
  | _ => 0

@[simp] theorem pathWeight_pair (M : DeformationMatrix n) (a b : Fin n) :
    M.pathWeight [a, b] = M.entry a b := by simp [pathWeight]

@[simp] theorem pathWeight_cons_cons (M : DeformationMatrix n)
    (a b : Fin n) (rest : List (Fin n)) :
    M.pathWeight (a :: b :: rest) = M.entry a b + M.pathWeight (b :: rest) :=
  rfl

/-- Iterating cyclic compatibility along a simple directed path.  For a path
with `s+1` edges this is exactly the paper's bound by the adjacent weights
plus `s`. -/
theorem compatible_path_bound (M : DeformationMatrix n)
    (hM : M.CyclicallyCompatible) (a b : Fin n) (rest : List (Fin n))
    (hn : (a :: b :: rest).Nodup) :
    M.entry a ((b :: rest).getLast (by simp)) ≤
      M.pathWeight (a :: b :: rest) + rest.length := by
  induction rest generalizing a b with
  | nil => simp [pathWeight]
  | cons c rest ih =>
      let d := (c :: rest).getLast (by simp)
      have ha_not : a ∉ b :: c :: rest := (List.nodup_cons.mp hn).1
      have htail : (b :: c :: rest).Nodup := (List.nodup_cons.mp hn).2
      have hb_not : b ∉ c :: rest := (List.nodup_cons.mp htail).1
      have hab : a ≠ b := by
        intro h
        exact ha_not (by simp [h])
      have hac : a ≠ d := by
        intro h
        have hmem : d ∈ c :: rest := by
          dsimp [d]
          exact List.getLast_mem (by simp)
        exact ha_not (by rw [h]; exact List.mem_cons_of_mem b hmem)
      have hbc : b ≠ d := by
        intro h
        have hmem : d ∈ c :: rest := by
          dsimp [d]
          exact List.getLast_mem (by simp)
        exact hb_not (by rw [h]; exact hmem)
      have hstep := hM a b d hab hac hbc
      have htail : M.entry b d ≤
          M.pathWeight (b :: c :: rest) + rest.length :=
        ih b c htail
      change M.entry a d ≤
        M.entry a b + M.pathWeight (b :: c :: rest) + (rest.length + 1)
      omega

end DeformationMatrix

/-- Remainders after subtracting the `n` adjacent lower bounds.  A symmetric
power records a multiset of gap positions, equivalently a weak composition. -/
abbrev GapRemainder (n r : ℕ) := Sym (Fin n) r

/-- Stars and bars in the form used in the paper. -/
theorem card_gapRemainder (n r : ℕ) [NeZero n] :
    Fintype.card (GapRemainder n r) = (n + r - 1).choose (n - 1) := by
  rw [Sym.card_sym_eq_choose]
  simp only [Fintype.card_fin]
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hle : n - 1 ≤ n + r - 1 := by omega
  calc
    (n + r - 1).choose r =
        (n + r - 1).choose ((n + r - 1) - (n - 1)) := by
          (congr 1; omega)
    _ = (n + r - 1).choose (n - 1) := Nat.choose_symm hle

/-- Substituting `r = q-n-L` yields the binomial appearing in the cyclic-gap
formula, whenever the lower bounds fit. -/
theorem card_gapRemainder_shifted (n q L : ℕ) [NeZero n]
    (h : n + L ≤ q) :
    Fintype.card (GapRemainder n (q - n - L)) =
      (q - L - 1).choose (n - 1) := by
  rw [card_gapRemainder]
  (congr 2; omega)

end CyclicBraidArrangement
