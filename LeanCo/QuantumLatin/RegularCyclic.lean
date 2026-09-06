import LeanCo.QuantumLatin.OddOrders

/-!
# Regular cyclic squares on `Fin N`

Every Fourier entry has full coordinate support.  This small wrapper transports
the cyclic construction from `ZMod N` to the numerical `Fin N` type used by
the pointed order-eight and order-twelve certificates.
-/

namespace LeanCo.QuantumLatin

/-- A cyclic certificate gives a maximal RQLS on `Fin N` all of whose
coordinates are nonzero. -/
theorem exists_fullSupport_cyclic_fin (N : ℕ) [NeZero N]
    (hcert : Nonempty {μ : ZMod N → ZMod N // CyclicCertificate N μ}) :
    ∃ R : MaximalRQLS (Fin N),
      ∀ i j d, R.square.entry i j d ≠ 0 := by
  classical
  obtain ⟨⟨μ, hμ⟩⟩ := hcert
  let e : ZMod N ≃ Fin N := Fintype.equivOfCardEq (by simp [ZMod.card])
  let R := (cyclicMaximalRQLS N μ hμ).reindex e
  refine ⟨R, ?_⟩
  intro i j d
  change fourierKet N μ (e.symm i) (e.symm j) (e.symm d) ≠ 0
  exact fourierKet_apply_ne_zero N μ _ _ _

theorem exists_fullSupport_odd_fin (N : ℕ) [NeZero N]
    (hN : 7 ≤ N) (hodd : Odd N) :
    ∃ R : MaximalRQLS (Fin N),
      ∀ i j d, R.square.entry i j d ≠ 0 :=
  exists_fullSupport_cyclic_fin N
    (exists_odd_cyclicCertificate N hN hodd)

theorem exists_regular_seven :
    ∃ R : MaximalRQLS (Fin 7),
      ∀ i j, R.square.entry i j 0 ≠ 0 ∧
        R.square.entry i j 1 ≠ 0 := by
  letI : NeZero 7 := ⟨by decide⟩
  obtain ⟨R, hR⟩ := exists_fullSupport_odd_fin 7 (by omega)
    ⟨3, by omega⟩
  exact ⟨R, fun i j ↦ ⟨hR i j 0, hR i j 1⟩⟩

theorem exists_regular_eleven :
    ∃ R : MaximalRQLS (Fin 11),
      ∀ i j, R.square.entry i j 0 ≠ 0 ∧
        R.square.entry i j 1 ≠ 0 := by
  letI : NeZero 11 := ⟨by decide⟩
  obtain ⟨R, hR⟩ := exists_fullSupport_odd_fin 11 (by omega)
    ⟨5, by omega⟩
  exact ⟨R, fun i j ↦ ⟨hR i j 0, hR i j 1⟩⟩

end LeanCo.QuantumLatin
