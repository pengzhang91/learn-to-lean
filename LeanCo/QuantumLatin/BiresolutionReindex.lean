import LeanCo.QuantumLatin.Biresolution

/-! Transport classical (bi)resolutions along finite equivalences. -/

namespace LeanCo.QuantumLatin

universe u v

namespace ClassicalQuantumLatinSquare

variable {α : Type u} {κ : Type v}
  [Fintype α] [Fintype κ] [DecidableEq α] [DecidableEq κ]

def reindex (e : α ≃ κ) (A : ClassicalQuantumLatinSquare α) :
    ClassicalQuantumLatinSquare κ where
  symbol i j := e (A.symbol (e.symm i) (e.symm j))
  row_bijective i := e.bijective.comp
    ((A.row_bijective (e.symm i)).comp e.symm.bijective)
  col_bijective j := e.bijective.comp
    ((A.col_bijective (e.symm j)).comp e.symm.bijective)

end ClassicalQuantumLatinSquare

namespace ClassicalBiresolution

variable {α : Type u} {κ : Type v}
  [Fintype α] [Fintype κ] [DecidableEq α] [DecidableEq κ]

def reindex (e : α ≃ κ) (A : ClassicalBiresolution α) :
    ClassicalBiresolution κ where
  base := A.base.reindex e
  first := A.first.reindex e
  second := A.second.reindex e
  base_first := by
    intro i j i' j' hbase hfirst
    have hb := e.injective hbase
    have hf := e.injective hfirst
    rcases A.base_first hb hf with ⟨hi, hj⟩
    exact ⟨e.symm.injective hi, e.symm.injective hj⟩
  base_second := by
    intro i j i' j' hbase hsecond
    have hb := e.injective hbase
    have hs := e.injective hsecond
    rcases A.base_second hb hs with ⟨hi, hj⟩
    exact ⟨e.symm.injective hi, e.symm.injective hj⟩
  first_second := by
    intro i j i' j' hfirst hsecond
    have hf := e.injective hfirst
    have hs := e.injective hsecond
    rcases A.first_second hf hs with ⟨hi, hj⟩
    exact ⟨e.symm.injective hi, e.symm.injective hj⟩

end ClassicalBiresolution

end LeanCo.QuantumLatin
