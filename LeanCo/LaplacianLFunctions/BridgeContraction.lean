import LeanCo.LaplacianLFunctions.ZetaTransport
import Mathlib.Tactic

/-!
# Contracting a bridge

This file formalizes the contraction step in Proposition 3.5 of
arXiv:2608.29981.  Contracting `q` into a distinct vertex `p` is represented
on the genuinely smaller vertex type `{v // v ≠ q}`.  Thus every map between
the original and contracted divisor/Picard groups is explicitly typed; no
identification of differently indexed free abelian groups is implicit.
-/

open scoped BigOperators

namespace LeanCo.LaplacianLFunctions

noncomputable section

/-- Vertex type obtained by deleting `q`; the surviving vertex `p` represents
the contracted pair `{p,q}`. -/
abbrev ContractedVertex {V : Type*} (q : V) := {v : V // v ≠ q}

/-- The quotient map on vertices for contraction of `q` into `p`. -/
def contractVertexMap {V : Type*} [DecidableEq V] (p q : V) (hpq : p ≠ q) :
    V → ContractedVertex q := fun v ↦
  if hv : v = q then ⟨p, hpq⟩ else ⟨v, hv⟩

@[simp]
theorem contractVertexMap_apply_q {V : Type*} [DecidableEq V]
    (p q : V) (hpq : p ≠ q) :
    contractVertexMap p q hpq q = ⟨p, hpq⟩ := by
  simp [contractVertexMap]

@[simp]
theorem contractVertexMap_apply_ne {V : Type*} [DecidableEq V]
    (p q : V) (hpq : p ≠ q) {v : V} (hv : v ≠ q) :
    contractVertexMap p q hpq v = ⟨v, hv⟩ := by
  simp [contractVertexMap, hv]

/-- Multiplicity matrix after contracting `q` into `p`.  Edges incident with
`q` are transferred to `p`, while edges between `p` and `q` become loops and
are discarded. -/
def contractedMultiplicity {V : Type*} [DecidableEq V]
    (G : LooplessMultigraph V) (p q : V) (a b : ContractedVertex q) : ℕ :=
  if a = b then 0
  else
    G.multiplicity a.1 b.1 +
      (if a.1 = p then G.multiplicity q b.1 else 0) +
      (if b.1 = p then G.multiplicity a.1 q else 0)

/-- The loopless multigraph obtained by contracting `q` into `p`. -/
def LooplessMultigraph.contractEdge {V : Type*} [DecidableEq V]
    (G : LooplessMultigraph V) (p q : V) (hpq : p ≠ q) :
    LooplessMultigraph (ContractedVertex q) where
  multiplicity := contractedMultiplicity G p q
  multiplicity_symm a b := by
    classical
    by_cases hab : a = b
    · subst b
      simp [contractedMultiplicity]
    · have hba : b ≠ a := Ne.symm hab
      simp only [contractedMultiplicity, if_neg hab, if_neg hba]
      rw [G.multiplicity_swap a.1 b.1,
        G.multiplicity_swap q b.1,
        G.multiplicity_swap a.1 q]
      ac_rfl
  multiplicity_self a := by
    simp [contractedMultiplicity]

namespace Divisor

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Push a divisor through the contraction: coefficients at `p` and `q` are
added at the contracted vertex. -/
def contractPush (p q : V) (hpq : p ≠ q) :
    Divisor V →ₗ[ℤ] Divisor (ContractedVertex q) where
  toFun D a := D a.1 + if a.1 = p then D q else 0
  map_add' D E := by
    funext a
    by_cases ha : a.1 = p <;> simp [ha] <;> ring
  map_smul' n D := by
    funext a
    by_cases ha : a.1 = p <;> simp [ha] <;> ring

@[simp]
theorem contractPush_apply (p q : V) (hpq : p ≠ q)
    (D : Divisor V) (a : ContractedVertex q) :
    contractPush p q hpq D a = D a.1 + if a.1 = p then D q else 0 :=
  rfl

/-- A section of `contractPush`, putting the merged coefficient at `p` and
zero chips at the deleted vertex `q`. -/
def contractInclude (q : V) :
    Divisor (ContractedVertex q) →ₗ[ℤ] Divisor V where
  toFun D v := if hv : v = q then 0 else D ⟨v, hv⟩
  map_add' D E := by
    funext v
    by_cases hv : v = q <;> simp [hv]
  map_smul' n D := by
    funext v
    by_cases hv : v = q <;> simp [hv]

@[simp]
theorem contractInclude_apply_q (q : V)
    (D : Divisor (ContractedVertex q)) :
    contractInclude q D q = 0 := by
  simp [contractInclude]

@[simp]
theorem contractInclude_apply_ne (q : V)
    (D : Divisor (ContractedVertex q)) {v : V} (hv : v ≠ q) :
    contractInclude q D v = D ⟨v, hv⟩ := by
  simp [contractInclude, hv]

/-- Pull a potential back along the vertex quotient; in particular its values
at `p` and `q` agree. -/
def contractPull (p q : V) (hpq : p ≠ q) :
    Divisor (ContractedVertex q) →ₗ[ℤ] Divisor V where
  toFun D v := D (contractVertexMap p q hpq v)
  map_add' D E := by rfl
  map_smul' n D := by rfl

@[simp]
theorem contractPull_apply (p q : V) (hpq : p ≠ q)
    (D : Divisor (ContractedVertex q)) (v : V) :
    contractPull p q hpq D v = D (contractVertexMap p q hpq v) :=
  rfl

@[simp]
theorem contractPush_contractInclude (p q : V) (hpq : p ≠ q)
    (D : Divisor (ContractedVertex q)) :
    contractPush p q hpq (contractInclude q D) = D := by
  funext a
  have haq : a.1 ≠ q := a.2
  by_cases hap : a.1 = p
  · have ha : a = (⟨p, hpq⟩ : ContractedVertex q) := Subtype.ext hap
    subst a
    simp [contractPush, contractInclude, hpq]
  · simp [contractPush, contractInclude, haq, hap]

/-- Divisor pushforward through a contraction preserves degree. -/
theorem degree_contractPush (p q : V) (hpq : p ≠ q)
    (D : Divisor V) :
    degree (contractPush p q hpq D) = degree D := by
  rw [degree_apply, degree_apply]
  simp only [contractPush_apply, Finset.sum_add_distrib]
  rw [Fintype.sum_eq_add_sum_subtype_ne D q]
  have hsum :
      (∑ a : ContractedVertex q, if a.1 = p then D q else 0) = D q := by
    classical
    rw [Finset.sum_eq_single (⟨p, hpq⟩ : ContractedVertex q)]
    · simp
    · intro a ha hane
      have hap : a.1 ≠ p := by
        intro hap
        exact hane (Subtype.ext hap)
      simp [hap]
    · simp
  rw [hsum]
  abel

/-- Effectivity is preserved by divisor pushforward. -/
theorem IsEffective.contractPush {p q : V} (hpq : p ≠ q)
    {D : Divisor V} (hD : IsEffective D) :
    IsEffective (contractPush p q hpq D) := by
  intro a
  rw [contractPush_apply]
  split_ifs
  · exact add_nonneg (hD a.1) (hD q)
  · simpa using hD a.1

/-- Effectivity is preserved by the chosen divisor section. -/
theorem IsEffective.contractInclude {q : V}
    {D : Divisor (ContractedVertex q)} (hD : IsEffective D) :
    IsEffective (contractInclude q D) := by
  intro v
  by_cases hv : v = q
  · simp [contractInclude, hv]
  · simpa [contractInclude, hv] using hD ⟨v, hv⟩

/-- The bridge endpoint difference lies in the kernel of divisor
pushforward. -/
@[simp]
theorem contractPush_vertexDifference (p q : V) (hpq : p ≠ q) :
    contractPush p q hpq
      (vertexDivisor p - vertexDivisor q) = 0 := by
  funext a
  by_cases hap : a.1 = p
  · have ha : a = (⟨p, hpq⟩ : ContractedVertex q) := Subtype.ext hap
    subst a
    simp [contractPush, vertexDivisor_apply, hpq, Ne.symm hpq]
  · have haq : a.1 ≠ q := a.2
    simp [contractPush, vertexDivisor_apply, hap, haq]

/-- The chosen section followed by pushforward differs from the original
divisor by a multiple of the bridge endpoint difference. -/
theorem contractInclude_contractPush_sub
    (p q : V) (hpq : p ≠ q) (D : Divisor V) :
    contractInclude q (contractPush p q hpq D) - D =
      D q • (vertexDivisor p - vertexDivisor q) := by
  funext v
  by_cases hvq : v = q
  · subst v
    simp [vertexDivisor_apply, Ne.symm hpq]
  · by_cases hvp : v = p
    · subst v
      simp [contractPush, vertexDivisor_apply, hpq]
    · simp [contractPush, vertexDivisor_apply, hvq, hvp]

/-- The chosen divisor section preserves degree. -/
theorem degree_contractInclude (p q : V) (hpq : p ≠ q)
    (D : Divisor (ContractedVertex q)) :
    degree (contractInclude q D) = degree D := by
  calc
    degree (contractInclude q D) =
        degree (contractPush p q hpq (contractInclude q D)) :=
      (degree_contractPush p q hpq (contractInclude q D)).symm
    _ = degree D := by rw [contractPush_contractInclude]

end Divisor

namespace LooplessMultigraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A cut certificate for the specified edge `p--q` to be a bridge.  Across
the cut there is exactly that one edge, with multiplicity one. -/
structure IsBridgeCut (G : LooplessMultigraph V)
    (S : Finset V) (p q : V) : Prop where
  mem_left : p ∈ S
  notMem_right : q ∉ S
  crossing : ∀ x, x ∈ S → ∀ y, y ∉ S →
    G.multiplicity x y = if x = p ∧ y = q then 1 else 0

theorem IsBridgeCut.ne {G : LooplessMultigraph V} {S : Finset V} {p q : V}
    (h : IsBridgeCut G S p q) : p ≠ q := by
  intro hpq
  subst q
  exact h.notMem_right h.mem_left

/-- Pulling a potential through the vertex quotient and then pushing its
Laplacian is exactly the Laplacian on the contracted multigraph. -/
theorem contractPush_laplacian_contractPull
    (G : LooplessMultigraph V) (p q : V) (hpq : p ≠ q)
    (D : Divisor (ContractedVertex q)) :
    Divisor.contractPush p q hpq
        (G.laplacian (Divisor.contractPull p q hpq D)) =
      (G.contractEdge p q hpq).laplacian D := by
  funext a
  by_cases hap : a.1 = p
  · have ha : a = (⟨p, hpq⟩ : ContractedVertex q) := Subtype.ext hap
    subst a
    simp only [Divisor.contractPush_apply, if_pos,
      laplacian_apply, Divisor.contractPull_apply]
    rw [Fintype.sum_eq_add_sum_subtype_ne
      (fun y : V ↦ (G.multiplicity p y : ℤ) *
        (D (contractVertexMap p q hpq p) -
          D (contractVertexMap p q hpq y))) q]
    rw [Fintype.sum_eq_add_sum_subtype_ne
      (fun y : V ↦ (G.multiplicity q y : ℤ) *
        (D (contractVertexMap p q hpq q) -
          D (contractVertexMap p q hpq y))) q]
    simp [contractVertexMap, hpq]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hxp : x.1 = p
    · have hxeq : x = (⟨p, hpq⟩ : ContractedVertex q) :=
        Subtype.ext hxp
      subst x
      simp [contractEdge, hpq]
    · have hxne : (⟨p, hpq⟩ : ContractedVertex q) ≠ x := by
        intro heq
        exact hxp (congrArg Subtype.val heq).symm
      simp [contractEdge, contractedMultiplicity, hxp, x.2, hxne]
      ring
  · simp only [Divisor.contractPush_apply, if_neg hap, add_zero,
      laplacian_apply, Divisor.contractPull_apply]
    rw [Fintype.sum_eq_add_sum_subtype_ne
      (fun y : V ↦ (G.multiplicity a.1 y : ℤ) *
        (D (contractVertexMap p q hpq a.1) -
          D (contractVertexMap p q hpq y))) q]
    have hamap : contractVertexMap p q hpq a.1 = a := by
      exact Subtype.ext (by simp [contractVertexMap, a.2])
    rw [hamap, contractVertexMap_apply_q]
    have hsurvivor :
        (∑ x : ContractedVertex q,
          (G.multiplicity a.1 x.1 : ℤ) *
            (D a - D (contractVertexMap p q hpq x.1))) =
          ∑ x : ContractedVertex q,
            (G.multiplicity a.1 x.1 : ℤ) * (D a - D x) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [contractVertexMap_apply_ne p q hpq x.2]
    rw [hsurvivor]
    rw [Fintype.sum_eq_add_sum_subtype_ne
      (fun b : ContractedVertex q ↦
        (G.multiplicity a.1 b.1 : ℤ) * (D a - D b))
      (⟨p, hpq⟩ : ContractedVertex q)]
    rw [Fintype.sum_eq_add_sum_subtype_ne
      (fun b : ContractedVertex q ↦
        ((G.contractEdge p q hpq).multiplicity a b : ℤ) * (D a - D b))
      (⟨p, hpq⟩ : ContractedVertex q)]
    have hane : a ≠ (⟨p, hpq⟩ : ContractedVertex q) := by
      intro heq
      exact hap (congrArg Subtype.val heq)
    have hmult_p :
        (G.contractEdge p q hpq).multiplicity a ⟨p, hpq⟩ =
          G.multiplicity a.1 p + G.multiplicity a.1 q := by
      simp [contractEdge, contractedMultiplicity, hane, hap]
    have hsum_eq :
        (∑ i : {b : ContractedVertex q // b ≠ ⟨p, hpq⟩},
          (G.multiplicity a.1 i.1.1 : ℤ) * (D a - D i.1)) =
        ∑ i : {b : ContractedVertex q // b ≠ ⟨p, hpq⟩},
          ((G.contractEdge p q hpq).multiplicity a i.1 : ℤ) *
            (D a - D i.1) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hip : i.1.1 ≠ p := by
        intro hip
        exact i.2 (Subtype.ext hip)
      by_cases hai : a = i.1
      · simp [hai]
      · simp [contractEdge, contractedMultiplicity, hai, hap, hip]
    rw [hmult_p, Nat.cast_add, hsum_eq]
    ring

/-- The integral potential which is one on the left side of a bridge cut and
zero on the right side. -/
def bridgeCutPotential (S : Finset V) : Divisor V :=
  fun v ↦ if v ∈ S then 1 else 0

@[simp]
theorem bridgeCutPotential_apply (S : Finset V) (v : V) :
    bridgeCutPotential S v = if v ∈ S then 1 else 0 :=
  rfl

/-- Firing the bridge-cut potential produces the difference of the two
endpoint divisors. -/
theorem laplacian_bridgeCutPotential
    (G : LooplessMultigraph V) {S : Finset V} {p q : V}
    (h : G.IsBridgeCut S p q) :
    G.laplacian (bridgeCutPotential S) =
      Divisor.vertexDivisor p - Divisor.vertexDivisor q := by
  funext x
  rw [laplacian_apply]
  by_cases hx : x ∈ S
  · have hxq : x ≠ q := fun hxq ↦ h.notMem_right (hxq ▸ hx)
    have hsum :
        (∑ y, (G.multiplicity x y : ℤ) *
          (bridgeCutPotential S x - bridgeCutPotential S y)) =
          if x = p then 1 else 0 := by
      calc
        (∑ y, (G.multiplicity x y : ℤ) *
            (bridgeCutPotential S x - bridgeCutPotential S y)) =
            ∑ y, if x = p ∧ y = q then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro y hy
          by_cases hyS : y ∈ S
          · have hyq : y ≠ q := fun hyq ↦
              h.notMem_right (hyq ▸ hyS)
            simp [bridgeCutPotential, hx, hyS, hyq]
          · rw [h.crossing x hx y hyS]
            by_cases hxp : x = p <;> by_cases hyq : y = q <;>
              simp [bridgeCutPotential, hx, hyS, hxp, hyq,
                h.mem_left, h.notMem_right]
        _ = if x = p then 1 else 0 := by
          by_cases hxp : x = p <;> simp [hxp]
    rw [hsum]
    simp [Divisor.vertexDivisor_apply, hxq]
  · have hxp : x ≠ p := fun hxp ↦ hx (hxp ▸ h.mem_left)
    have hsum :
        (∑ y, (G.multiplicity x y : ℤ) *
          (bridgeCutPotential S x - bridgeCutPotential S y)) =
          if x = q then -1 else 0 := by
      calc
        (∑ y, (G.multiplicity x y : ℤ) *
            (bridgeCutPotential S x - bridgeCutPotential S y)) =
            ∑ y, if y = p ∧ x = q then -1 else 0 := by
          apply Finset.sum_congr rfl
          intro y hy
          by_cases hyS : y ∈ S
          · rw [G.multiplicity_swap, h.crossing y hyS x hx]
            by_cases hyp : y = p <;> by_cases hxq : x = q <;>
              simp [bridgeCutPotential, hx, hyS, hyp, hxq,
                h.mem_left, h.notMem_right]
          · have hyp : y ≠ p := fun hyp ↦ hyS (hyp ▸ h.mem_left)
            simp [bridgeCutPotential, hx, hyS, hyp]
        _ = if x = q then -1 else 0 := by
          by_cases hxq : x = q <;> simp [hxq]
    rw [hsum]
    by_cases hxq : x = q <;>
      simp [Divisor.vertexDivisor_apply, hxp, hxq, h.ne, Ne.symm h.ne]

/-- The difference of the bridge endpoints is principal. -/
theorem bridgeEndpointDifference_mem_laplacianLattice
    (G : LooplessMultigraph V) {S : Finset V} {p q : V}
    (h : G.IsBridgeCut S p q) :
    Divisor.vertexDivisor p - Divisor.vertexDivisor q ∈
      G.laplacianLattice := by
  exact ⟨bridgeCutPotential S, G.laplacian_bridgeCutPotential h⟩

/-- Normalize a potential by translating the bridge-cut side containing
`p`, so that its new values at `p` and `q` agree and it descends through the
contraction. -/
def bridgeNormalizedPotential
    (S : Finset V) (p q : V) (D : Divisor V) :
    Divisor (ContractedVertex q) := fun a ↦
  if a.1 ∈ S then D a.1 - D p + D q else D a.1

/-- Decomposition of a potential into a pullback from the contraction and a
multiple of the bridge-cut potential. -/
theorem contractPull_bridgeNormalizedPotential
    {S : Finset V} {p q : V} (hpq : p ≠ q)
    (hpS : p ∈ S) (hqS : q ∉ S) (D : Divisor V) :
    Divisor.contractPull p q hpq
        (bridgeNormalizedPotential S p q D) +
      (D p - D q) • bridgeCutPotential S = D := by
  funext v
  by_cases hvq : v = q
  · subst v
    simp [Divisor.contractPull, bridgeNormalizedPotential,
      contractVertexMap, hpS, hqS, bridgeCutPotential]
  · by_cases hvS : v ∈ S
    · simp [Divisor.contractPull, bridgeNormalizedPotential,
        contractVertexMap, hvq, hvS, bridgeCutPotential]
    · simp [Divisor.contractPull, bridgeNormalizedPotential,
        contractVertexMap, hvq, hvS, bridgeCutPotential]

/-- Under a bridge contraction, pushing any principal divisor is principal.
The normalized potential is an explicit preimage on the contracted graph. -/
theorem contractPush_laplacian_of_bridge
    (G : LooplessMultigraph V) {S : Finset V} {p q : V}
    (h : G.IsBridgeCut S p q) (D : Divisor V) :
    Divisor.contractPush p q h.ne (G.laplacian D) =
      (G.contractEdge p q h.ne).laplacian
        (bridgeNormalizedPotential S p q D) := by
  let N := bridgeNormalizedPotential S p q D
  have hnorm : Divisor.contractPull p q h.ne N +
      (D p - D q) • bridgeCutPotential S = D :=
    contractPull_bridgeNormalizedPotential h.ne h.mem_left
      h.notMem_right D
  calc
    Divisor.contractPush p q h.ne (G.laplacian D) =
        Divisor.contractPush p q h.ne
          (G.laplacian (Divisor.contractPull p q h.ne N +
            (D p - D q) • bridgeCutPotential S)) := by rw [hnorm]
    _ = (G.contractEdge p q h.ne).laplacian N := by
      simp only [map_add, map_smul]
      rw [contractPush_laplacian_contractPull,
        G.laplacian_bridgeCutPotential h,
        Divisor.contractPush_vertexDifference]
      simp
    _ = (G.contractEdge p q h.ne).laplacian
        (bridgeNormalizedPotential S p q D) := rfl

/-- Divisor pushforward sends the original Laplacian lattice into the
contracted Laplacian lattice. -/
theorem contractPush_mem_laplacianLattice
    (G : LooplessMultigraph V) {S : Finset V} {p q : V}
    (h : G.IsBridgeCut S p q) {D : Divisor V}
    (hD : D ∈ G.laplacianLattice) :
    Divisor.contractPush p q h.ne D ∈
      (G.contractEdge p q h.ne).laplacianLattice := by
  obtain ⟨f, rfl⟩ := hD
  exact ⟨bridgeNormalizedPotential S p q f,
    (contractPush_laplacian_of_bridge G h f).symm⟩

/-- The chosen divisor section sends contracted principal divisors back to
original principal divisors. -/
theorem contractInclude_mem_laplacianLattice
    (G : LooplessMultigraph V) {S : Finset V} {p q : V}
    (h : G.IsBridgeCut S p q) {D : Divisor (ContractedVertex q)}
    (hD : D ∈ (G.contractEdge p q h.ne).laplacianLattice) :
    Divisor.contractInclude q D ∈ G.laplacianLattice := by
  obtain ⟨f, rfl⟩ := hD
  let pullF := Divisor.contractPull p q h.ne f
  have hcomm := contractPush_laplacian_contractPull G p q h.ne f
  have hsub := Divisor.contractInclude_contractPush_sub p q h.ne
    (G.laplacian pullF)
  rw [hcomm] at hsub
  have hsubmem :
      Divisor.contractInclude q ((G.contractEdge p q h.ne).laplacian f) -
          G.laplacian pullF ∈ G.laplacianLattice := by
    rw [hsub]
    exact G.laplacianLattice.smul_mem _
      (G.bridgeEndpointDifference_mem_laplacianLattice h)
  exact (G.laplacianLattice.sub_mem_iff_left
    ⟨pullF, rfl⟩).mp hsubmem

/-- The linear map on Picard groups induced by divisor pushforward. -/
def bridgePicardPush
    (G : LooplessMultigraph V) {S : Finset V} {p q : V}
    (h : G.IsBridgeCut S p q) :
    G.Picard →ₗ[ℤ] (G.contractEdge p q h.ne).Picard :=
  G.laplacianLattice.mapQ
    (G.contractEdge p q h.ne).laplacianLattice
    (Divisor.contractPush p q h.ne)
    (fun _ hD ↦ G.contractPush_mem_laplacianLattice h hD)

@[simp]
theorem bridgePicardPush_divisorClass
    (G : LooplessMultigraph V) {S : Finset V} {p q : V}
    (h : G.IsBridgeCut S p q) (D : Divisor V) :
    G.bridgePicardPush h (G.divisorClass D) =
      (G.contractEdge p q h.ne).divisorClass
        (Divisor.contractPush p q h.ne D) := by
  rfl

/-- The linear map on Picard groups induced by the chosen divisor section. -/
def bridgePicardInclude
    (G : LooplessMultigraph V) {S : Finset V} {p q : V}
    (h : G.IsBridgeCut S p q) :
    (G.contractEdge p q h.ne).Picard →ₗ[ℤ] G.Picard :=
  (G.contractEdge p q h.ne).laplacianLattice.mapQ
    G.laplacianLattice (Divisor.contractInclude q)
    (fun _ hD ↦ G.contractInclude_mem_laplacianLattice h hD)

@[simp]
theorem bridgePicardInclude_divisorClass
    (G : LooplessMultigraph V) {S : Finset V} {p q : V}
    (h : G.IsBridgeCut S p q)
    (D : Divisor (ContractedVertex q)) :
    G.bridgePicardInclude h
        ((G.contractEdge p q h.ne).divisorClass D) =
      G.divisorClass (Divisor.contractInclude q D) := by
  rfl

/-- A specified bridge contraction induces an additive equivalence of Picard
groups.  Its forward map is the correctly typed divisor pushforward. -/
def bridgePicardEquiv
    (G : LooplessMultigraph V) {S : Finset V} {p q : V}
    (h : G.IsBridgeCut S p q) :
    G.Picard ≃+ (G.contractEdge p q h.ne).Picard where
  toFun := G.bridgePicardPush h
  invFun := G.bridgePicardInclude h
  map_add' C D := (G.bridgePicardPush h).map_add C D
  left_inv C := by
    refine Submodule.Quotient.induction_on G.laplacianLattice C ?_
    intro D
    change G.bridgePicardInclude h
      (G.bridgePicardPush h (G.divisorClass D)) = G.divisorClass D
    rw [G.bridgePicardPush_divisorClass,
      G.bridgePicardInclude_divisorClass]
    apply (G.divisorClass_eq_iff_sub_mem _ _).mpr
    rw [Divisor.contractInclude_contractPush_sub]
    exact G.laplacianLattice.smul_mem _
      (G.bridgeEndpointDifference_mem_laplacianLattice h)
  right_inv C := by
    refine Submodule.Quotient.induction_on
      (G.contractEdge p q h.ne).laplacianLattice C ?_
    intro D
    change G.bridgePicardPush h
      (G.bridgePicardInclude h
        ((G.contractEdge p q h.ne).divisorClass D)) =
      (G.contractEdge p q h.ne).divisorClass D
    rw [G.bridgePicardInclude_divisorClass,
      G.bridgePicardPush_divisorClass,
      Divisor.contractPush_contractInclude]

@[simp]
theorem bridgePicardEquiv_divisorClass
    (G : LooplessMultigraph V) {S : Finset V} {p q : V}
    (h : G.IsBridgeCut S p q) (D : Divisor V) :
    G.bridgePicardEquiv h (G.divisorClass D) =
      (G.contractEdge p q h.ne).divisorClass
        (Divisor.contractPush p q h.ne D) :=
  G.bridgePicardPush_divisorClass h D

@[simp]
theorem bridgePicardEquiv_symm_divisorClass
    (G : LooplessMultigraph V) {S : Finset V} {p q : V}
    (h : G.IsBridgeCut S p q)
    (D : Divisor (ContractedVertex q)) :
    (G.bridgePicardEquiv h).symm
        ((G.contractEdge p q h.ne).divisorClass D) =
      G.divisorClass (Divisor.contractInclude q D) :=
  G.bridgePicardInclude_divisorClass h D

/-- The bridge-contraction Picard equivalence preserves degree. -/
theorem picardDegree_bridgePicardEquiv
    (G : LooplessMultigraph V) {S : Finset V} {p q : V}
    (h : G.IsBridgeCut S p q) (C : G.Picard) :
    (G.contractEdge p q h.ne).picardDegree
        (G.bridgePicardEquiv h C) = G.picardDegree C := by
  refine Submodule.Quotient.induction_on G.laplacianLattice C ?_
  intro D
  change (G.contractEdge p q h.ne).picardDegree
      (G.bridgePicardEquiv h (G.divisorClass D)) =
    G.picardDegree (G.divisorClass D)
  rw [G.bridgePicardEquiv_divisorClass,
    (G.contractEdge p q h.ne).picardDegree_divisorClass,
    G.picardDegree_divisorClass, Divisor.degree_contractPush]

/-- A class is effective exactly when its image under bridge contraction is
effective. -/
theorem bridgePicardEquiv_hasEffectiveRepresentative_iff
    (G : LooplessMultigraph V) {S : Finset V} {p q : V}
    (h : G.IsBridgeCut S p q) (C : G.Picard) :
    (G.contractEdge p q h.ne).HasEffectiveRepresentative
        (G.bridgePicardEquiv h C) ↔
      G.HasEffectiveRepresentative C := by
  constructor
  · rintro ⟨E, hE, hclass⟩
    refine ⟨Divisor.contractInclude q E, hE.contractInclude, ?_⟩
    have hclass' := congrArg (G.bridgePicardEquiv h).symm hclass
    rw [(G.bridgePicardEquiv h).symm_apply_apply] at hclass'
    change G.bridgePicardInclude h
      ((G.contractEdge p q h.ne).divisorClass E) = C at hclass'
    rw [G.bridgePicardInclude_divisorClass] at hclass'
    exact hclass'
  · rintro ⟨D, hD, hclass⟩
    refine ⟨Divisor.contractPush p q h.ne D,
      hD.contractPush h.ne, ?_⟩
    rw [← G.bridgePicardPush_divisorClass h D, hclass]
    rfl

/-- The admissible degrees in the minimum defining `h` are unchanged by
bridge contraction. -/
theorem bridgePicardEquiv_hAdmissible_iff
    (G : LooplessMultigraph V) {S : Finset V} {p q : V}
    (h : G.IsBridgeCut S p q) (C : G.Picard) (n : ℕ) :
    (G.contractEdge p q h.ne).HAdmissible
        (G.bridgePicardEquiv h C) n ↔ G.HAdmissible C n := by
  constructor
  · rintro ⟨E, hE, hdeg, hnone⟩
    refine ⟨Divisor.contractInclude q E, hE.contractInclude,
      ?_, ?_⟩
    · simpa [Divisor.degree_contractInclude p q h.ne E] using hdeg
    · intro heff
      have htransport :=
        (G.bridgePicardEquiv_hasEffectiveRepresentative_iff h
          (C - G.divisorClass (Divisor.contractInclude q E))).mpr heff
      apply hnone
      simpa only [map_sub, G.bridgePicardEquiv_divisorClass,
        Divisor.contractPush_contractInclude] using htransport
  · rintro ⟨D, hD, hdeg, hnone⟩
    refine ⟨Divisor.contractPush p q h.ne D, hD.contractPush h.ne,
      ?_, ?_⟩
    · rw [Divisor.degree_contractPush]
      exact hdeg
    · intro heff
      have hsource :=
        (G.bridgePicardEquiv_hasEffectiveRepresentative_iff h
          (C - G.divisorClass D)).mp ?_
      · exact hnone hsource
      · simpa only [map_sub, G.bridgePicardEquiv_divisorClass] using heff

/-- Baker--Norine `h` is preserved by contraction of a specified bridge. -/
theorem h_bridgePicardEquiv
    (G : LooplessMultigraph V) [Nonempty V]
    {S : Finset V} {p q : V} (h : G.IsBridgeCut S p q)
    [Nonempty (ContractedVertex q)] (C : G.Picard) :
    (G.contractEdge p q h.ne).h (G.bridgePicardEquiv h C) = G.h C := by
  apply Nat.le_antisymm
  · apply (G.contractEdge p q h.ne).h_min
    exact (G.bridgePicardEquiv_hAdmissible_iff h C (G.h C)).mpr
      (G.h_spec C)
  · apply G.h_min
    exact (G.bridgePicardEquiv_hAdmissible_iff h C
      ((G.contractEdge p q h.ne).h (G.bridgePicardEquiv h C))).mp
        ((G.contractEdge p q h.ne).h_spec (G.bridgePicardEquiv h C))

/-- Proposition 3.5, for one specified bridge: contracting it leaves the
two-variable graph zeta function unchanged.  Both sides use their genuine
vertex types, and the coefficient sums are reindexed through
`bridgePicardEquiv`. -/
theorem zeta_contractEdge_of_bridge
    (G : LooplessMultigraph V) [Nonempty V]
    {S : Finset V} {p q : V} (h : G.IsBridgeCut S p q)
    [Nonempty (ContractedVertex q)]
    [Fintype G.Jacobian]
    [Fintype (G.contractEdge p q h.ne).Jacobian] :
    G.zeta = (G.contractEdge p q h.ne).zeta := by
  exact G.zeta_eq_of_picardEquiv (G.contractEdge p q h.ne)
    (G.bridgePicardEquiv h)
    (G.picardDegree_bridgePicardEquiv h)
    (G.h_bridgePicardEquiv h)

end LooplessMultigraph

/-! ## Finite iteration and contraction of all bridges -/

universe u

/-- A finite loopless multigraph bundled with exactly the instances needed
to form its zeta function.  Bundling the vertex type lets a contraction
chain change that type at every step. -/
structure BridgeContractionState where
  Vertex : Type u
  fintypeVertex : Fintype Vertex
  decidableEqVertex : DecidableEq Vertex
  nonemptyVertex : Nonempty Vertex
  graph : LooplessMultigraph Vertex
  fintypeJacobian : @Fintype (@LooplessMultigraph.Jacobian Vertex
    fintypeVertex graph)

namespace BridgeContractionState

instance (A : BridgeContractionState) : Fintype A.Vertex :=
  A.fintypeVertex

instance (A : BridgeContractionState) : DecidableEq A.Vertex :=
  A.decidableEqVertex

instance (A : BridgeContractionState) : Nonempty A.Vertex :=
  A.nonemptyVertex

instance (A : BridgeContractionState) : Fintype A.graph.Jacobian :=
  A.fintypeJacobian

/-- The bundled state obtained from one certified bridge contraction. -/
def contract (A : BridgeContractionState)
    {S : Finset A.Vertex} {p q : A.Vertex}
    (h : A.graph.IsBridgeCut S p q)
    (hJac : Fintype (A.graph.contractEdge p q h.ne).Jacobian) :
    BridgeContractionState where
  Vertex := ContractedVertex q
  fintypeVertex := inferInstance
  decidableEqVertex := inferInstance
  nonemptyVertex := ⟨⟨p, h.ne⟩⟩
  graph := A.graph.contractEdge p q h.ne
  fintypeJacobian := hJac

end BridgeContractionState

/-- A finite sequence of certified bridge contractions.  The bundled graph
state allows successive vertex types to differ, avoiding the implicit
identifications in the paper proof. -/
inductive BridgeContractionChain :
    BridgeContractionState → BridgeContractionState → Prop
  | refl (A : BridgeContractionState) : BridgeContractionChain A A
  | step {A B : BridgeContractionState}
      {S : Finset A.Vertex} {p q : A.Vertex}
      (h : A.graph.IsBridgeCut S p q)
      (hJac : Fintype (A.graph.contractEdge p q h.ne).Jacobian)
      (tail : BridgeContractionChain (A.contract h hJac) B) :
      BridgeContractionChain A B

/-- Zeta is invariant along every finite chain of bridge contractions. -/
theorem BridgeContractionChain.zeta_eq
    {A B : BridgeContractionState}
    (c : BridgeContractionChain A B) :
    A.graph.zeta = B.graph.zeta := by
  induction c with
  | refl => rfl
  | @step A B S p q h hJac tail ih =>
      letI : Nonempty (ContractedVertex q) := ⟨⟨p, h.ne⟩⟩
      letI : Fintype (A.graph.contractEdge p q h.ne).Jacobian := hJac
      exact (A.graph.zeta_contractEdge_of_bridge h).trans ih

/-- Proposition 3.5 in its finite, type-correct form: if `B` is obtained
from `A` by a finite bridge-contraction chain and the terminal graph is
bridge-free (so the chain has contracted all bridges), then their zeta
functions agree. -/
theorem BridgeContractionChain.zeta_eq_contractAllBridges
    {A B : BridgeContractionState}
    (c : BridgeContractionChain A B)
    (_hterminal : B.graph.BridgeFree) :
    A.graph.zeta = B.graph.zeta :=
  c.zeta_eq

end

end LeanCo.LaplacianLFunctions
