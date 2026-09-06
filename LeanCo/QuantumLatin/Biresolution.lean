import LeanCo.QuantumLatin.Orthogonality
import LeanCo.QuantumLatin.ClassicalCertificates
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Classical squares with two orthogonal resolutions

The singular direct product uses one classical Latin square together with two
transversal partitions whose every pair meets once.  Three mutually
orthogonal Latin squares give exactly this data.  This file records that
interface and supplies both the finite certificates used later and an
elementary cyclic family when `2` and `3` are units modulo the order.
-/

namespace LeanCo.QuantumLatin

universe u

/-- The ordered pair of symbols of `A` and `B` determines its cell. -/
def TableOrthogonal {ι : Type u} (A B : ι → ι → ι) : Prop :=
  ∀ ⦃i j i' j'⦄,
    A i j = A i' j' → B i j = B i' j' → i = i' ∧ j = j'

/-- A classical Latin square with two transversal label squares.  Pairwise
table orthogonality says that each label fiber is a transversal and that a
fiber from the first partition meets a fiber from the second exactly once. -/
structure ClassicalBiresolution (ι : Type u) [Fintype ι] where
  base : ClassicalQuantumLatinSquare ι
  first : ClassicalQuantumLatinSquare ι
  second : ClassicalQuantumLatinSquare ι
  base_first : TableOrthogonal base.symbol first.symbol
  base_second : TableOrthogonal base.symbol second.symbol
  first_second : TableOrthogonal first.symbol second.symbol

/-- One classical transversal partition, equivalently two orthogonal Latin
squares. -/
structure ClassicalResolvedSquare (ι : Type u) [Fintype ι] where
  base : ClassicalQuantumLatinSquare ι
  label : ClassicalQuantumLatinSquare ι
  base_label : TableOrthogonal base.symbol label.symbol

namespace ClassicalResolvedSquare

variable {ι : Type u} [Fintype ι]

/-- Compatibility names emphasizing that a resolved square is the one-label
special case of a biresolved square. -/
abbrev first (A : ClassicalResolvedSquare ι) := A.label
abbrev second (A : ClassicalResolvedSquare ι) := A.label
theorem base_first (A : ClassicalResolvedSquare ι) :
    TableOrthogonal A.base.symbol A.first.symbol := A.base_label
theorem base_second (A : ClassicalResolvedSquare ι) :
    TableOrthogonal A.base.symbol A.second.symbol := A.base_label

end ClassicalResolvedSquare

namespace ClassicalBiresolution

variable {ι : Type u} [Fintype ι]

def firstResolved (A : ClassicalBiresolution ι) : ClassicalResolvedSquare ι where
  base := A.base
  label := A.first
  base_label := A.base_first

theorem first_fiber_symbol_injective (A : ClassicalBiresolution ι)
    (p : ι) : Function.Injective (fun x : {q : ι × ι // A.first.symbol q.1 q.2 = p} ↦
      A.base.symbol x.1.1 x.1.2) := by
  intro x y h
  have hp : A.first.symbol x.1.1 x.1.2 =
      A.first.symbol y.1.1 y.1.2 := x.property.trans y.property.symm
  apply Subtype.ext
  apply Prod.ext
  · exact (A.base_first h hp).1
  · exact (A.base_first h hp).2

/-- Every first-label fiber and second-label fiber have a unique common
cell.  This is the exact incidence fact used by Construction 4.6. -/
theorem existsUnique_intersection (A : ClassicalBiresolution ι) (p q : ι) :
    ∃! x : ι × ι,
      A.first.symbol x.1 x.2 = p ∧ A.second.symbol x.1 x.2 = q := by
  let F : ι × ι → ι × ι := fun x ↦
    (A.first.symbol x.1 x.2, A.second.symbol x.1 x.2)
  have hF : Function.Bijective F := by
    have hinj : Function.Injective F := by
      intro x y h
      exact Prod.ext (A.first_second (congrArg Prod.fst h)
        (congrArg Prod.snd h)).1 (A.first_second (congrArg Prod.fst h)
        (congrArg Prod.snd h)).2
    exact (Fintype.bijective_iff_injective_and_card F).2 ⟨hinj, by simp⟩
  obtain ⟨x, hx⟩ := hF.2 (p, q)
  refine ⟨x, ⟨congrArg Prod.fst hx, congrArg Prod.snd hx⟩, ?_⟩
  intro y hy
  apply hF.1
  apply Prod.ext
  · exact hy.1.trans (congrArg Prod.fst hx).symm
  · exact hy.2.trans (congrArg Prod.snd hx).symm

end ClassicalBiresolution

section FiniteCertificates

/-- Turn the computational `IsLatin` predicate into the bundled classical
square used by the QLS development. -/
def bundledClassicalSquare {n : ℕ} (L : ClassicalSquare n)
    (hL : IsLatin L) : ClassicalQuantumLatinSquare (Fin n) where
  symbol := L
  row_bijective i := (Fintype.bijective_iff_injective_and_card _).2
    ⟨hL.1 i, by simp⟩
  col_bijective j := (Fintype.bijective_iff_injective_and_card _).2
    ⟨hL.2 j, by simp⟩

theorem biresolution_of_threeMOLS {n : ℕ} (h : HasThreeMOLS n) :
    Nonempty (ClassicalBiresolution (Fin n)) := by
  rcases h with ⟨A, B, C, hA, hB, hC, hAB, hAC, hBC⟩
  refine ⟨{
    base := bundledClassicalSquare A hA
    first := bundledClassicalSquare B hB
    second := bundledClassicalSquare C hC
    base_first := ?_
    base_second := ?_
    first_second := ?_ }⟩
  · intro i j i' j' h₁ h₂
    exact hAB i j i' j' (Prod.ext h₁ h₂)
  · intro i j i' j' h₁ h₂
    exact hAC i j i' j' (Prod.ext h₁ h₂)
  · intro i j i' j' h₁ h₂
    exact hBC i j i' j' (Prod.ext h₁ h₂)

theorem resolvedSquare_of_twoMOLS {n : ℕ} (h : HasTwoMOLS n) :
    Nonempty (ClassicalResolvedSquare (Fin n)) := by
  rcases h with ⟨A, B, hA, hB, hAB⟩
  refine ⟨{
    base := bundledClassicalSquare A hA
    label := bundledClassicalSquare B hB
    base_label := ?_ }⟩
  intro i j i' j' h₁ h₂
  exact hAB i j i' j' (Prod.ext h₁ h₂)

theorem resolvedSquare_ten :
    Nonempty (ClassicalResolvedSquare (Fin 10)) :=
  resolvedSquare_of_twoMOLS hasTwoMOLS_10

theorem biresolution_nine :
    Nonempty (ClassicalBiresolution (Fin 9)) :=
  biresolution_of_threeMOLS hasThreeMOLS_9

theorem biresolution_fourteen :
    Nonempty (ClassicalBiresolution (Fin 14)) :=
  biresolution_of_threeMOLS hasThreeMOLS_14

theorem biresolution_fifteen :
    Nonempty (ClassicalBiresolution (Fin 15)) :=
  biresolution_of_threeMOLS hasThreeMOLS_15

theorem biresolution_eighteen :
    Nonempty (ClassicalBiresolution (Fin 18)) :=
  biresolution_of_threeMOLS hasThreeMOLS_18

theorem biresolution_twentyOne :
    Nonempty (ClassicalBiresolution (Fin 21)) :=
  biresolution_of_threeMOLS hasThreeMOLS_21

end FiniteCertificates

section Cyclic

variable (n : ℕ) [NeZero n]

def linearClassicalSquare (a : ZMod n) : ZMod n → ZMod n → ZMod n :=
  fun i j ↦ i + a * j

def linearClassicalLatin (a : ZMod n) (ha : IsUnit a) :
    ClassicalQuantumLatinSquare (ZMod n) where
  symbol := linearClassicalSquare n a
  row_bijective i := by
    exact (Equiv.addLeft i).bijective.comp
      (IsUnit.isUnit_iff_mulLeft_bijective.mp ha)
  col_bijective j := by
    change Function.Bijective (fun i : ZMod n ↦ i + a * j)
    exact (Equiv.addRight (a * j)).bijective

theorem linear_tables_orthogonal (a b : ZMod n) (hab : IsUnit (b - a)) :
    TableOrthogonal (linearClassicalSquare n a)
      (linearClassicalSquare n b) := by
  intro i j i' j' hA hB
  have hjmul : (b - a) * j = (b - a) * j' := by
    dsimp [linearClassicalSquare] at hA hB ⊢
    linear_combination hB - hA
  have hj : j = j' := hab.mul_right_injective hjmul
  subst j'
  have hi : i = i' := by
    simpa [linearClassicalSquare] using hA
  exact ⟨hi, rfl⟩

/-- Slopes `1,2,3` give three MOLS whenever `2` and `3` are units. -/
noncomputable def cyclicClassicalBiresolution
    (h2 : IsUnit (2 : ZMod n)) (h3 : IsUnit (3 : ZMod n)) :
    ClassicalBiresolution (ZMod n) where
  base := linearClassicalLatin n 1 isUnit_one
  first := linearClassicalLatin n 2 h2
  second := linearClassicalLatin n 3 h3
  base_first := by
    change TableOrthogonal (linearClassicalSquare n 1)
      (linearClassicalSquare n 2)
    apply linear_tables_orthogonal
    convert isUnit_one using 1 <;> ring
  base_second := by
    change TableOrthogonal (linearClassicalSquare n 1)
      (linearClassicalSquare n 3)
    apply linear_tables_orthogonal
    convert h2 using 1 <;> ring
  first_second := by
    change TableOrthogonal (linearClassicalSquare n 2)
      (linearClassicalSquare n 3)
    apply linear_tables_orthogonal
    convert isUnit_one using 1 <;> ring

theorem cyclic_biresolution_of_coprime
    (h2 : Nat.Coprime 2 n) (h3 : Nat.Coprime 3 n) :
    Nonempty (ClassicalBiresolution (ZMod n)) := by
  exact ⟨cyclicClassicalBiresolution n
    ((ZMod.isUnit_iff_coprime 2 n).2 h2)
    ((ZMod.isUnit_iff_coprime 3 n).2 h3)⟩

end Cyclic

end LeanCo.QuantumLatin
