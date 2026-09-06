import LeanCo.LaplacianLFunctions.BakerNorine.RiemannRoch
import LeanCo.LaplacianLFunctions.Connectivity
import LeanCo.LaplacianLFunctions.EffectiveRank
import LeanCo.LaplacianLFunctions.GraphInvariants

/-!
# Baker--Norine Riemann--Roch for `LooplessMultigraph`

This file transports the complete, mathlib-only Baker--Norine proof in
`BakerNorine/` to the multigraph, divisor, Picard, and `h` definitions used by
arXiv:2608.29981 in this project.
-/

namespace LeanCo.LaplacianLFunctions

open scoped BigOperators

namespace LooplessMultigraph

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- An edge multiset realizing the symmetric multiplicity matrix of `G`.
For every unordered pair we choose one of its two ordered representatives and
repeat it with the prescribed multiplicity. -/
noncomputable def bakerNorineEdges (G : LooplessMultigraph V) :
    Multiset (V × V) :=
  (Finset.univ : Finset (Sym2 V)).val.bind fun e ↦
    Multiset.replicate (G.edgeMultiplicity e) (Quot.out e)

private theorem quotOut_matches_pair_iff (e : Sym2 V) (v w : V) :
    (Quot.out e = (v, w) ∨ Quot.out e = (w, v)) ↔ e = s(v, w) := by
  constructor
  · rintro (h | h)
    · calc
        e = Quot.mk (Sym2.Rel V) (Quot.out e) := (Quot.out_eq e).symm
        _ = s(v, w) := congrArg (Quot.mk (Sym2.Rel V)) h
    · calc
        e = Quot.mk (Sym2.Rel V) (Quot.out e) := (Quot.out_eq e).symm
        _ = s(w, v) := congrArg (Quot.mk (Sym2.Rel V)) h
        _ = s(v, w) := Sym2.sound (Sym2.Rel.swap w v)
  · intro he
    have hr : Sym2.Rel V (Quot.out e) (v, w) :=
      Sym2.exact ((Quot.out_eq e).trans he)
    rcases Sym2.rel_iff.mp hr with h | h
    · exact Or.inl (Prod.ext h.1 h.2)
    · exact Or.inr (Prod.ext h.1 h.2)

private theorem not_mem_bakerNorineEdges_diag
    (G : LooplessMultigraph V) (v : V) :
    (v, v) ∉ G.bakerNorineEdges := by
  intro hv
  rw [bakerNorineEdges, Multiset.mem_bind] at hv
  obtain ⟨e, _, he⟩ := hv
  rw [Multiset.mem_replicate] at he
  have heq : e = s(v, v) :=
    (quotOut_matches_pair_iff e v v).mp (Or.inl he.2.symm)
  have hz : G.edgeMultiplicity e = 0 := by simp [heq]
  exact he.1 hz

/-- The edge-list graph used to invoke the vendored Baker--Norine theorem. -/
noncomputable def toBakerNorineGraph (G : LooplessMultigraph V) : CFGraph where
  V := V
  instDecidableEq := inferInstance
  instFintype := inferInstance
  instNonempty := inferInstance
  edges := G.bakerNorineEdges
  loopless := G.not_mem_bakerNorineEdges_diag

private theorem card_filter_replicate
    {α : Type*} (p : α → Prop) [DecidablePred p] (n : ℕ) (a : α) :
    Multiset.card ((Multiset.replicate n a).filter p) =
      if p a then n else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Multiset.replicate_succ, Multiset.filter_cons]
      by_cases h : p a
      · simp [h, ih]
      · simp [h, ih]

theorem num_edges_toBakerNorineGraph
    (G : LooplessMultigraph V) (v w : V) :
    num_edges G.toBakerNorineGraph v w = G.multiplicity v w := by
  classical
  rw [num_edges]
  change Multiset.card
      (G.bakerNorineEdges.filter
        (fun e ↦ e = (v, w) ∨ e = (w, v))) = G.multiplicity v w
  rw [bakerNorineEdges]
  rw [Multiset.filter_bind, Multiset.card_bind]
  simp only [Function.comp_apply, card_filter_replicate, Finset.sum_map_val]
  simp_rw [quotOut_matches_pair_iff]
  simpa only [G.edgeMultiplicity_mk] using
    (Fintype.sum_ite_eq' s(v, w) G.edgeMultiplicity)

@[simp]
theorem card_bakerNorineEdges (G : LooplessMultigraph V) :
    Multiset.card G.bakerNorineEdges = G.edgeCount := by
  classical
  rw [bakerNorineEdges, Multiset.card_bind]
  simp only [Function.comp_apply, Multiset.card_replicate,
    Finset.sum_map_val]
  rfl

@[simp]
theorem genus_toBakerNorineGraph (G : LooplessMultigraph V) :
    _root_.genus G.toBakerNorineGraph = G.genus := by
  change (Multiset.card G.bakerNorineEdges : ℤ) -
      (Fintype.card V : ℤ) + 1 =
    (G.edgeCount : ℤ) - (Fintype.card V : ℤ) + 1
  rw [G.card_bakerNorineEdges]

@[simp]
theorem vertex_degree_toBakerNorineGraph
    (G : LooplessMultigraph V) (v : V) :
    vertex_degree G.toBakerNorineGraph v = (G.valency v : ℤ) := by
  unfold vertex_degree valency
  simp_rw [G.num_edges_toBakerNorineGraph]
  rw [Nat.cast_sum]
  rfl

@[simp]
theorem canonical_divisor_toBakerNorineGraph
    (G : LooplessMultigraph V) :
    canonical_divisor G.toBakerNorineGraph = G.canonicalDivisor := by
  funext v
  simp [canonical_divisor, LooplessMultigraph.canonicalDivisor]

@[simp]
theorem deg_toBakerNorineGraph
    (G : LooplessMultigraph V) (D : Divisor V) :
    deg (G := G.toBakerNorineGraph) D = Divisor.degree D := by
  rfl

/-- The vendored convention for principal divisors is the negative of this
project's Laplacian convention; their images are consequently identical. -/
theorem prin_toBakerNorineGraph
    (G : LooplessMultigraph V) (σ : Divisor V) :
    prin G.toBakerNorineGraph σ = -G.laplacian σ := by
  funext v
  rw [prin_apply, Pi.neg_apply, G.laplacian_apply]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro w _
  rw [G.num_edges_toBakerNorineGraph]
  ring

/-- Vendored linear equivalence is exactly equality in this project's
Picard group. -/
theorem linear_equiv_toBakerNorineGraph_iff
    (G : LooplessMultigraph V) (D E : Divisor V) :
    linear_equiv G.toBakerNorineGraph D E ↔
      G.divisorClass D = G.divisorClass E := by
  rw [G.divisorClass_eq_iff_sub_mem]
  constructor
  · intro h
    rw [linear_equiv, principal_iff_eq_prin] at h
    obtain ⟨σ, hσ⟩ := h
    rw [G.mem_laplacianLattice_iff]
    refine ⟨σ, ?_⟩
    rw [G.prin_toBakerNorineGraph] at hσ
    calc
      G.laplacian σ = -(-G.laplacian σ) := by simp
      _ = -(E - D) := congrArg Neg.neg hσ.symm
      _ = D - E := by abel
  · intro h
    rw [G.mem_laplacianLattice_iff] at h
    obtain ⟨σ, hσ⟩ := h
    rw [linear_equiv, principal_iff_eq_prin]
    refine ⟨σ, ?_⟩
    rw [G.prin_toBakerNorineGraph]
    calc
      E - D = -(D - E) := by abel
      _ = -G.laplacian σ := (congrArg Neg.neg hσ).symm

@[simp]
theorem effective_toBakerNorineGraph_iff
    (G : LooplessMultigraph V) (D : Divisor V) :
    effective (G := G.toBakerNorineGraph) D ↔ Divisor.IsEffective D := by
  rfl

/-- Winnability in the vendored chip-firing development is exactly existence
of an effective representative of the corresponding Picard class. -/
theorem winnable_toBakerNorineGraph_iff
    (G : LooplessMultigraph V) (D : Divisor V) :
    winnable G.toBakerNorineGraph D ↔
      G.HasEffectiveRepresentative (G.divisorClass D) := by
  rw [winnable_iff_exists_effective]
  constructor
  · rintro ⟨E, hE, hDE⟩
    exact ⟨E, (G.effective_toBakerNorineGraph_iff E).mp hE,
      (G.linear_equiv_toBakerNorineGraph_iff D E).mp hDE |>.symm⟩
  · rintro ⟨E, hE, hclass⟩
    exact ⟨E, (G.effective_toBakerNorineGraph_iff E).mpr hE,
      (G.linear_equiv_toBakerNorineGraph_iff D E).mpr hclass.symm⟩

/-- Connectivity of the support graph implies the cut formulation of
connectivity used by the vendored Baker--Norine development. -/
theorem graph_connected_toBakerNorineGraph
    (G : LooplessMultigraph V) (hconn : G.Connected) :
    graph_connected G.toBakerNorineGraph := by
  intro S hproper
  obtain ⟨v, w, hv, hw⟩ := hproper
  by_contra hcross
  push Not at hcross
  have hclosed : ∀ {a b : V}, a ∈ S → G.support.Adj a b → b ∈ S := by
    intro a b ha hab
    by_contra hb
    have hpositive : num_edges G.toBakerNorineGraph a b > 0 := by
      rw [G.num_edges_toBakerNorineGraph]
      exact (G.support_adj a b).mp hab
    have hnonpositive := hcross a ha b hb
    omega
  obtain ⟨p⟩ := hconn.preconnected v w
  have hwalk : ∀ {a b : V}, G.support.Walk a b → a ∈ S → b ∈ S := by
    intro a b q
    induction q with
    | nil => exact fun ha ↦ ha
    | cons hab q ih =>
        intro ha
        exact ih (hclosed ha hab)
  exact hw (hwalk p hv)

/-- The vendored rank is exactly `h - 1`.  This is proved from the two
independent minimum characterizations, rather than assumed as a convention. -/
theorem rank_add_one_eq_divisorH
    (G : LooplessMultigraph V) (D : Divisor V) :
    rank G.toBakerNorineGraph D + 1 = (G.divisorH D : ℤ) := by
  change rank G.toBakerNorineGraph D + 1 =
    (G.h (G.divisorClass D) : ℤ)
  have hrank_lower : -1 ≤ rank G.toBakerNorineGraph D :=
    rank_geq_neg_one G.toBakerNorineGraph D
  let n : ℕ := (rank G.toBakerNorineGraph D + 1).toNat
  have hn_nonneg : 0 ≤ rank G.toBakerNorineGraph D + 1 := by omega
  have hn_cast : (n : ℤ) = rank G.toBakerNorineGraph D + 1 := by
    exact Int.toNat_of_nonneg hn_nonneg
  obtain ⟨E, hE, hEdeg, hres⟩ :=
    rank_get_effective G.toBakerNorineGraph D
  change Divisor V at E
  have hn_admissible : G.HAdmissible (G.divisorClass D) n := by
    refine ⟨E, (G.effective_toBakerNorineGraph_iff E).mp hE, ?_, ?_⟩
    · calc
        Divisor.degree E = deg (G := G.toBakerNorineGraph) E :=
          (G.deg_toBakerNorineGraph E).symm
        _ = rank G.toBakerNorineGraph D + 1 := hEdeg
        _ = (n : ℤ) := hn_cast.symm
    · intro hhas
      apply hres
      apply (G.winnable_toBakerNorineGraph_iff (D - E)).mpr
      simpa using hhas
  have hh_le : G.h (G.divisorClass D) ≤ n :=
    G.h_min (G.divisorClass D) hn_admissible
  obtain ⟨E', hE', hE'deg, hres'⟩ :=
    G.h_spec (G.divisorClass D)
  have hnotwin : ¬ winnable G.toBakerNorineGraph (D - E') := by
    intro hwin
    apply hres'
    have hhas := (G.winnable_toBakerNorineGraph_iff (D - E')).mp hwin
    simpa using hhas
  have hnot_rank_geq :
      ¬ rank_geq G.toBakerNorineGraph D
        (G.h (G.divisorClass D) : ℤ) := by
    intro hgeq
    apply hnotwin
    apply hgeq E'
    constructor
    · exact (G.effective_toBakerNorineGraph_iff E').mpr hE'
    · calc
        deg (G := G.toBakerNorineGraph) E' = Divisor.degree E' :=
          G.deg_toBakerNorineGraph E'
        _ = (G.h (G.divisorClass D) : ℤ) := hE'deg
  have hrank_lt :
      rank G.toBakerNorineGraph D <
        (G.h (G.divisorClass D) : ℤ) := by
    by_contra hnot
    apply hnot_rank_geq
    apply (rank_geq_iff G.toBakerNorineGraph D
      (G.h (G.divisorClass D) : ℤ)).mpr
    omega
  have hh_cast_le :
      (G.h (G.divisorClass D) : ℤ) ≤ (n : ℤ) := by
    exact_mod_cast hh_le
  rw [hn_cast] at hh_cast_le
  omega

/-- Baker--Norine Riemann--Roch, in the divisor-level `h` notation of
arXiv:2608.29981 (Theorem 2.6). -/
theorem riemann_roch_divisorH
    (G : LooplessMultigraph V) (hconn : G.Connected) (D : Divisor V) :
    (G.divisorH D : ℤ) -
        (G.divisorH (G.canonicalDivisor - D) : ℤ) =
      Divisor.degree D - G.genus + 1 := by
  have hRR := riemann_roch_for_graphs
    (G.graph_connected_toBakerNorineGraph hconn) D
  let K : Divisor V := fun v ↦ canonical_divisor G.toBakerNorineGraph v
  change rank G.toBakerNorineGraph D - rank G.toBakerNorineGraph (K - D) =
    deg (G := G.toBakerNorineGraph) D -
      _root_.genus G.toBakerNorineGraph + 1 at hRR
  have hrankD :
      rank G.toBakerNorineGraph D = (G.divisorH D : ℤ) - 1 := by
    linarith [G.rank_add_one_eq_divisorH D]
  have hcanonical : K = G.canonicalDivisor := by
    funext v
    dsimp only [K]
    exact congrFun G.canonical_divisor_toBakerNorineGraph v
  have hrankKD :
      rank G.toBakerNorineGraph (K - D) =
        (G.divisorH (G.canonicalDivisor - D) : ℤ) - 1 := by
    rw [hcanonical]
    linarith [G.rank_add_one_eq_divisorH (G.canonicalDivisor - D)]
  rw [hrankD, hrankKD, G.deg_toBakerNorineGraph,
    G.genus_toBakerNorineGraph] at hRR
  linarith

/-- The same theorem written directly on Picard classes, matching the
paper's notation `h(D) = h([D])`. -/
theorem riemann_roch_h
    (G : LooplessMultigraph V) (hconn : G.Connected) (D : Divisor V) :
    (G.h (G.divisorClass D) : ℤ) -
        (G.h (G.divisorClass (G.canonicalDivisor - D)) : ℤ) =
      Divisor.degree D - G.genus + 1 := by
  simpa [divisorH] using G.riemann_roch_divisorH hconn D

end LooplessMultigraph

end LeanCo.LaplacianLFunctions
