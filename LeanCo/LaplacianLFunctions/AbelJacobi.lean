import LeanCo.LaplacianLFunctions.RiemannRochBridge

/-!
# Abel--Jacobi maps of graph symmetric powers

This file formalizes Theorems 2.8 and 2.9 and Corollary 2.10 of
arXiv:2608.29981 (the corresponding results are Theorems 1.7 and 1.8 in
Baker--Norine).  For `k : ℕ`, the graph symmetric power is represented by
effective divisors of degree `k`, and its Abel--Jacobi map sends a divisor to
its class in `PicardDegree k`.

The connectivity convention in the paper is made explicit in the theorem
hypotheses.  In particular, the statement at `k = 0` needs no exceptional
case: the effective degree-zero divisor is unique, while a connected graph is
one-edge-connected in the cut sense below.
-/

namespace LeanCo.LaplacianLFunctions

open scoped BigOperators

/-- The `k`-th symmetric power of the vertex set, represented intrinsically
as effective divisors of degree `k`. -/
abbrev EffectiveDivisorDegree (V : Type*) [Fintype V] (k : ℕ) :=
  {D : Divisor V // Divisor.IsEffective D ∧ Divisor.degree D = (k : ℤ)}

namespace LooplessMultigraph

variable {V : Type*} [Fintype V]

/-- The Abel--Jacobi map `S⁽ᵏ⁾ → Picᵏ`: take the linear-equivalence
class of an effective degree-`k` divisor. -/
def abelJacobi (G : LooplessMultigraph V) (k : ℕ) :
    EffectiveDivisorDegree V k → G.PicardDegree (k : ℤ) :=
  fun D ↦ ⟨G.divisorClass D.1, by
    rw [G.picardDegree_divisorClass]
    exact D.2.2⟩

@[simp]
theorem abelJacobi_coe (G : LooplessMultigraph V) (k : ℕ)
    (D : EffectiveDivisorDegree V k) :
    (G.abelJacobi k D : G.Picard) = G.divisorClass D.1 :=
  rfl

/-- A multigraph is `r`-edge-connected when each nontrivial vertex cut has
at least `r` crossing edges (parallel edges counted with multiplicity). -/
def EdgeConnected (G : LooplessMultigraph V) (r : ℕ) : Prop :=
  ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ → r ≤ G.cutWeight S

@[simp]
theorem edgeConnected_two_iff_bridgeFree (G : LooplessMultigraph V) :
    G.EdgeConnected 2 ↔ G.BridgeFree :=
  Iff.rfl

/-- An effective divisor has no more chips on a subset than it has in total. -/
theorem sum_le_degree_of_effective (D : Divisor V)
    (hD : Divisor.IsEffective D) (S : Finset V) :
    ∑ v ∈ S, D v ≤ Divisor.degree D := by
  classical
  change ∑ v ∈ S, D v ≤ ∑ v ∈ Finset.univ, D v
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    (fun v _ _ ↦ hD v)

/-- On any subset, the sum of `D - E` is bounded by the total degree of `D`
when both divisors are effective. -/
theorem sum_sub_le_degree_of_effective (D E : Divisor V)
    (hD : Divisor.IsEffective D) (hE : Divisor.IsEffective E)
    (S : Finset V) :
    ∑ v ∈ S, (D - E) v ≤ Divisor.degree D := by
  classical
  simp only [Pi.sub_apply, Finset.sum_sub_distrib]
  have hEsum : 0 ≤ ∑ v ∈ S, E v :=
    Finset.sum_nonneg (fun v _ ↦ hE v)
  have hDsum := sum_le_degree_of_effective D hD S
  omega

/-- The potential which is one on a cut and zero on its complement. -/
noncomputable def cutPotential (S : Finset V) : Divisor V := by
  classical
  exact fun v ↦ if v ∈ S then 1 else 0

/-- The effective boundary divisor supported on the inside of a cut. -/
noncomputable def innerBoundaryDivisor (G : LooplessMultigraph V)
    (S : Finset V) : Divisor V := by
  classical
  exact fun v ↦ if v ∈ S then
    ((∑ w, if w ∈ S then 0 else G.multiplicity v w : ℕ) : ℤ) else 0

/-- The effective boundary divisor supported on the outside of a cut. -/
noncomputable def outerBoundaryDivisor (G : LooplessMultigraph V)
    (S : Finset V) : Divisor V := by
  classical
  exact fun v ↦ if v ∈ S then 0 else
    ((∑ w, if w ∈ S then G.multiplicity v w else 0 : ℕ) : ℤ)

theorem innerBoundaryDivisor_effective (G : LooplessMultigraph V)
    (S : Finset V) :
    Divisor.IsEffective (G.innerBoundaryDivisor S) := by
  classical
  intro v
  simp only [innerBoundaryDivisor]
  split_ifs <;> positivity

theorem outerBoundaryDivisor_effective (G : LooplessMultigraph V)
    (S : Finset V) :
    Divisor.IsEffective (G.outerBoundaryDivisor S) := by
  classical
  intro v
  simp only [outerBoundaryDivisor]
  split_ifs <;> positivity

@[simp]
theorem degree_innerBoundaryDivisor (G : LooplessMultigraph V)
    (S : Finset V) :
    Divisor.degree (G.innerBoundaryDivisor S) = (G.cutWeight S : ℤ) := by
  classical
  simp only [Divisor.degree_apply, innerBoundaryDivisor, cutWeight,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]
  rw [Finset.sum_ite_mem]
  simp

/-- Firing the indicator of `S` moves precisely the boundary divisor from
the outside of the cut to the inside. -/
theorem laplacian_cutPotential (G : LooplessMultigraph V) (S : Finset V) :
    G.laplacian (cutPotential S) =
      G.innerBoundaryDivisor S - G.outerBoundaryDivisor S := by
  classical
  funext v
  rw [G.laplacian_apply]
  by_cases hv : v ∈ S
  · simp only [cutPotential, innerBoundaryDivisor, outerBoundaryDivisor,
      hv, if_true, Pi.sub_apply, sub_zero, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro w hw
    by_cases hws : w ∈ S
    · simp [hws]
    · simp [hws]
  · simp only [cutPotential, innerBoundaryDivisor, outerBoundaryDivisor,
      hv, if_false, Pi.sub_apply, zero_sub, Nat.cast_sum]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro w hw
    by_cases hws : w ∈ S
    · simp [hws]
    · simp [hws]

@[simp]
theorem degree_outerBoundaryDivisor (G : LooplessMultigraph V)
    (S : Finset V) :
    Divisor.degree (G.outerBoundaryDivisor S) = (G.cutWeight S : ℤ) := by
  have hdeg := G.degree_laplacian (cutPotential S)
  rw [G.laplacian_cutPotential S, Divisor.degree_sub,
    G.degree_innerBoundaryDivisor S] at hdeg
  omega

/-- The two cut-boundary divisors are linearly equivalent. -/
theorem divisorClass_innerBoundary_eq_outerBoundary
    (G : LooplessMultigraph V) (S : Finset V) :
    G.divisorClass (G.innerBoundaryDivisor S) =
      G.divisorClass (G.outerBoundaryDivisor S) := by
  have hzero := G.divisorClass_laplacian (cutPotential S)
  rw [G.laplacian_cutPotential S, LinearMap.map_sub] at hzero
  exact sub_eq_zero.mp hzero

/-- A connected graph has an edge crossing every nontrivial cut. -/
theorem exists_crossing_edge_of_connected (G : LooplessMultigraph V)
    [Nonempty V] [DecidableEq V] (hconn : G.Connected) (S : Finset V)
    (hS : S.Nonempty) (hproper : S ≠ Finset.univ) :
    ∃ v ∈ S, ∃ w ∉ S, 0 < G.multiplicity v w := by
  have hout : ∃ w : V, w ∉ S := by
    by_contra h
    push Not at h
    apply hproper
    ext w
    simp [h w]
  obtain ⟨v₀, hv₀⟩ := hS
  obtain ⟨w₀, hw₀⟩ := hout
  have hcut : ∃ v ∈ S, ∃ w ∉ S,
      num_edges G.toBakerNorineGraph v w > 0 :=
    G.graph_connected_toBakerNorineGraph hconn S
      ⟨v₀, w₀, hv₀, hw₀⟩
  simpa only [G.num_edges_toBakerNorineGraph] using hcut

/-- Connectedness is exactly the lower bound needed at `k = 0`: every
nontrivial cut has at least one edge. -/
theorem edgeConnected_one_of_connected (G : LooplessMultigraph V)
    [Nonempty V] [DecidableEq V] (hconn : G.Connected) :
    G.EdgeConnected 1 := by
  classical
  letI : DecidableEq V := Classical.decEq V
  intro S hS hproper
  obtain ⟨v, hv, w, hw, hpositive⟩ :=
    G.exists_crossing_edge_of_connected hconn S hS hproper
  rw [cutWeight]
  calc
    1 ≤ G.multiplicity v w := hpositive
    _ = if w ∈ S then 0 else G.multiplicity v w := by simp [hw]
    _ ≤ ∑ x, if x ∈ S then 0 else G.multiplicity v x := by
      exact Finset.single_le_sum
        (s := Finset.univ)
        (f := fun x ↦ if x ∈ S then 0 else G.multiplicity v x)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ w)
    _ ≤ ∑ x ∈ S, ∑ y,
        if y ∈ S then 0 else G.multiplicity x y := by
      exact Finset.single_le_sum
        (s := S)
        (f := fun x ↦ ∑ y,
          if y ∈ S then 0 else G.multiplicity x y)
        (fun _ _ ↦ Nat.zero_le _) hv

/-- The inside and outside boundary divisors of a nontrivial cut in a
connected graph are distinct. -/
theorem innerBoundaryDivisor_ne_outerBoundaryDivisor_of_connected
    (G : LooplessMultigraph V) [Nonempty V] [DecidableEq V]
    (hconn : G.Connected) (S : Finset V) (hS : S.Nonempty)
    (hproper : S ≠ Finset.univ) :
    G.innerBoundaryDivisor S ≠ G.outerBoundaryDivisor S := by
  classical
  letI : DecidableEq V := Classical.decEq V
  obtain ⟨v, hv, w, hw, hpositive⟩ :=
    G.exists_crossing_edge_of_connected hconn S hS hproper
  intro heq
  have heval := congrFun heq v
  simp only [innerBoundaryDivisor, outerBoundaryDivisor, hv, if_true] at heval
  have hle : G.multiplicity v w ≤
      ∑ x, if x ∈ S then 0 else G.multiplicity v x := by
    calc
      G.multiplicity v w =
          if w ∈ S then 0 else G.multiplicity v w := by simp [hw]
      _ ≤ ∑ x, if x ∈ S then 0 else G.multiplicity v x := by
        exact Finset.single_le_sum
          (s := Finset.univ)
          (f := fun x ↦ if x ∈ S then 0 else G.multiplicity v x)
          (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ w)
  have hsumPositive : 0 <
      ∑ x, if x ∈ S then 0 else G.multiplicity v x :=
    lt_of_lt_of_le hpositive hle
  have hcastPositive : (0 : ℤ) <
      ((∑ x, if x ∈ S then 0 else G.multiplicity v x : ℕ) : ℤ) := by
    exact_mod_cast hsumPositive
  exact (ne_of_gt hcastPositive) heval

/-- The zero configuration is superstable on a connected chip-firing graph.
This supplies a starting point for the finite maximal-superstable extension
theorem in the vendored Baker--Norine development. -/
noncomputable def zeroConfig (H : CFGraph) (q : H.V) : Config H q where
  chips := 0
  q_zero := rfl
  non_negative := by simp

theorem zeroConfig_superstable (H : CFGraph) (hconn : graph_connected H)
    (q : H.V) : superstable H q (zeroConfig H q) := by
  classical
  intro S hsubset hS
  have hq : q ∉ S := by
    intro hqS
    have := hsubset hqS
    simp only [Vtilde, Finset.mem_filter, Finset.mem_univ, ne_eq,
      not_true_eq_false, and_false] at this
  obtain ⟨v₀, hv₀⟩ := hS
  obtain ⟨v, hv, w, hw, hpositive⟩ :=
    hconn S ⟨v₀, q, hv₀, hq⟩
  refine ⟨v, hv, ?_⟩
  simp only [zeroConfig, Pi.zero_apply]
  unfold outdeg_S
  have hwmem : w ∈ Finset.univ \ S := by simp [hw]
  have hpositiveInt : (0 : ℤ) < (num_edges H v w : ℤ) := by
    exact_mod_cast hpositive
  exact lt_of_lt_of_le hpositiveInt
    (Finset.single_le_sum (fun x _ ↦ Int.natCast_nonneg (num_edges H v x)) hwmem)

/-- On a connected graph there is an unwinnable divisor of every integral
degree strictly below the genus.  Start from a maximal superstable
configuration (degree `g`), subtract one chip at its root, and then subtract
additional effective chips at that root. -/
theorem exists_unwinnable_of_degree_lt_genus (H : CFGraph)
    (hconn : graph_connected H) (q : H.V) {d : ℤ} (hd : d < _root_.genus H) :
    ∃ D : CFDiv H, deg D = d ∧ ¬ winnable H D := by
  classical
  obtain ⟨c, hcmax, hcge⟩ :=
    maximal_superstable_exists H q (zeroConfig H q)
      (zeroConfig_superstable H hconn q)
  obtain ⟨O, hO, hOc⟩ := maximal_superstable_orientation H q c hcmax
  have hcdeg : config_degree c = _root_.genus H := by
    rw [← hOc]
    exact config_degree_from_O O hO
  let M : CFDiv H := c.chips - one_chip q
  have hMdeg : deg M = _root_.genus H - 1 := by
    dsimp only [M]
    rw [deg_chips_sub_one_chip, hcdeg]
  have hMunwinnable : ¬ winnable H M := by
    exact superstable_sub_chip_unwinnable q c hcmax.1
  have hgapNonnegative : 0 ≤ _root_.genus H - 1 - d := by omega
  let n : ℕ := (_root_.genus H - 1 - d).toNat
  have hn : (n : ℤ) = _root_.genus H - 1 - d := by
    exact Int.toNat_of_nonneg hgapNonnegative
  let P : CFDiv H := n • one_chip q
  let D : CFDiv H := M - P
  have hPdeg : deg P = (n : ℤ) := by
    calc
      deg P = n • deg (one_chip q) := AddMonoidHom.map_nsmul deg n (one_chip q)
      _ = (n : ℤ) := by simp
  have hDdeg : deg D = d := by
    dsimp only [D]
    rw [map_sub, hMdeg, hPdeg, hn]
    ring
  refine ⟨D, hDdeg, ?_⟩
  intro hDwinnable
  apply hMunwinnable
  have hPeffective : effective P := by
    dsimp only [P]
    exact (Eff H).nsmul_mem (eff_one_chip q) n
  have hPwinnable : winnable H P :=
    winnable_of_effective H P hPeffective
  have hadd : winnable H (D + P) :=
    winnable_add_winnable H D P hDwinnable hPwinnable
  have heq : D + P = M := by
    dsimp only [D]
    abel
  rwa [heq] at hadd

/-- If a Laplacian is a nonzero difference, the maximum-potential set is a
proper cut. -/
theorem topLevelSet_ne_univ_of_laplacian_eq_sub
    (G : LooplessMultigraph V) (f D E : Divisor V)
    (hne : D ≠ E) (hprincipal : G.laplacian f = D - E) (a : V) :
    topLevelSet f a ≠ Finset.univ := by
  classical
  intro htop
  have hall : ∀ x, f x = f a := by
    intro x
    apply (mem_topLevelSet_iff f a x).mp
    rw [htop]
    exact Finset.mem_univ x
  have hlap : G.laplacian f = 0 := by
    funext x
    simp only [G.laplacian_apply, Pi.zero_apply]
    apply Finset.sum_eq_zero
    intro y hy
    rw [hall x, hall y]
    simp
  apply hne
  apply sub_eq_zero.mp
  rw [← hprincipal, hlap]

/-- The injective direction of Theorem 2.9.  The maximum-potential cut of a
principal difference of two effective degree-`k` divisors has at most `k`
crossing edges, contradicting `(k+1)`-edge-connectivity. -/
theorem abelJacobi_injective_of_edgeConnected
    (G : LooplessMultigraph V) [Nonempty V] [DecidableEq V] (k : ℕ)
    (hedge : G.EdgeConnected (k + 1)) :
    Function.Injective (G.abelJacobi k) := by
  intro D E hclass
  apply Subtype.ext
  by_contra hne
  have hclass' : G.divisorClass D.1 = G.divisorClass E.1 := by
    exact congrArg Subtype.val hclass
  have hmem : D.1 - E.1 ∈ G.laplacianLattice :=
    (G.divisorClass_eq_iff_sub_mem D.1 E.1).mp hclass'
  obtain ⟨f, hf⟩ := (G.mem_laplacianLattice_iff (D.1 - E.1)).mp hmem
  let q : V := Classical.choice (inferInstance : Nonempty V)
  obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image Finset.univ f
    ⟨q, Finset.mem_univ q⟩
  have hmax' : ∀ x, f x ≤ f a :=
    fun x ↦ hmax x (Finset.mem_univ x)
  let S := topLevelSet f a
  have hSnonempty : S.Nonempty := topLevelSet_nonempty f a
  have hSproper : S ≠ Finset.univ :=
    G.topLevelSet_ne_univ_of_laplacian_eq_sub f D.1 E.1 hne hf a
  have hlowerNat : k + 1 ≤ G.cutWeight S := hedge S hSnonempty hSproper
  have hlowerInt : (k : ℤ) + 1 ≤ (G.cutWeight S : ℤ) := by
    exact_mod_cast hlowerNat
  have hboundary : (G.cutWeight S : ℤ) ≤
      ∑ v ∈ S, G.laplacian f v :=
    G.intCast_cutWeight_le_sum_laplacian_of_max f a hmax'
  have hupper : (∑ v ∈ S, G.laplacian f v) ≤ (k : ℤ) := by
    rw [hf]
    calc
      ∑ v ∈ S, (D.1 - E.1) v ≤ Divisor.degree D.1 :=
        sum_sub_le_degree_of_effective D.1 E.1 D.2.1 E.2.1 S
      _ = (k : ℤ) := D.2.2
  omega

/-- A cut of size at most `k` gives two distinct, linearly equivalent
effective divisors of degree `k`: its two boundary divisors, padded by the
same `k - cutWeight` chips.  This is the converse construction in Theorem
2.9. -/
theorem abelJacobi_not_injective_of_not_edgeConnected
    (G : LooplessMultigraph V) [Nonempty V] [DecidableEq V]
    (hconn : G.Connected) (k : ℕ) (hedge : ¬ G.EdgeConnected (k + 1)) :
    ¬ Function.Injective (G.abelJacobi k) := by
  classical
  letI : DecidableEq V := Classical.decEq V
  simp only [EdgeConnected] at hedge
  push Not at hedge
  obtain ⟨S, hS, hproper, hsmall⟩ := hedge
  have hcutLe : G.cutWeight S ≤ k := by omega
  let q : V := Classical.choice (inferInstance : Nonempty V)
  let F : Divisor V := Divisor.vertexMultiple (k - G.cutWeight S) q
  let Din : Divisor V := G.innerBoundaryDivisor S + F
  let Dout : Divisor V := G.outerBoundaryDivisor S + F
  have hFEffective : Divisor.IsEffective F := by
    exact Divisor.isEffective_vertexMultiple (k - G.cutWeight S) q
  have hDinEffective : Divisor.IsEffective Din :=
    (G.innerBoundaryDivisor_effective S).add hFEffective
  have hDoutEffective : Divisor.IsEffective Dout :=
    (G.outerBoundaryDivisor_effective S).add hFEffective
  have hdegreePadding :
      (G.cutWeight S : ℤ) + ((k - G.cutWeight S : ℕ) : ℤ) = (k : ℤ) := by
    exact_mod_cast Nat.add_sub_of_le hcutLe
  have hDinDegree : Divisor.degree Din = (k : ℤ) := by
    dsimp only [Din, F]
    rw [Divisor.degree_add, G.degree_innerBoundaryDivisor,
      Divisor.degree_vertexMultiple]
    exact hdegreePadding
  have hDoutDegree : Divisor.degree Dout = (k : ℤ) := by
    dsimp only [Dout, F]
    rw [Divisor.degree_add, G.degree_outerBoundaryDivisor,
      Divisor.degree_vertexMultiple]
    exact hdegreePadding
  let D : EffectiveDivisorDegree V k :=
    ⟨Din, hDinEffective, hDinDegree⟩
  let E : EffectiveDivisorDegree V k :=
    ⟨Dout, hDoutEffective, hDoutDegree⟩
  have hboundaryNe : G.innerBoundaryDivisor S ≠
      G.outerBoundaryDivisor S :=
    G.innerBoundaryDivisor_ne_outerBoundaryDivisor_of_connected
      hconn S hS hproper
  have hDE : D ≠ E := by
    intro heq
    apply hboundaryNe
    have hval : Din = Dout := congrArg Subtype.val heq
    dsimp only [Din, Dout] at hval
    exact add_right_cancel hval
  intro hinjective
  apply hDE
  apply hinjective
  apply Subtype.ext
  change G.divisorClass
      (G.innerBoundaryDivisor S + F) =
    G.divisorClass (G.outerBoundaryDivisor S + F)
  rw [LinearMap.map_add, LinearMap.map_add,
    G.divisorClass_innerBoundary_eq_outerBoundary S]

/-- Theorem 2.9 (Baker--Norine Theorem 1.8): on a connected graph, the
degree-`k` Abel--Jacobi map is injective exactly when the graph is
`(k+1)`-edge-connected. -/
theorem abelJacobi_injective_iff_edgeConnected
    (G : LooplessMultigraph V) [Nonempty V] [DecidableEq V]
    (hconn : G.Connected) (k : ℕ) :
    Function.Injective (G.abelJacobi k) ↔ G.EdgeConnected (k + 1) := by
  constructor
  · intro hinjective
    by_contra hedge
    exact G.abelJacobi_not_injective_of_not_edgeConnected
      hconn k hedge hinjective
  · exact G.abelJacobi_injective_of_edgeConnected k

/-- Surjectivity of the Abel--Jacobi map is equivalent to every class of
degree `k` having an effective representative. -/
theorem abelJacobi_surjective_iff_every_class_effective
    (G : LooplessMultigraph V) (k : ℕ) :
    Function.Surjective (G.abelJacobi k) ↔
      ∀ C : G.PicardDegree (k : ℤ),
        G.HasEffectiveRepresentative C.1 := by
  constructor
  · intro hsurjective C
    obtain ⟨D, hD⟩ := hsurjective C
    refine ⟨D.1, D.2.1, ?_⟩
    exact congrArg Subtype.val hD
  · intro heffective C
    obtain ⟨D, hDEffective, hclass⟩ := heffective C
    have hdegree : Divisor.degree D = (k : ℤ) := by
      calc
        Divisor.degree D = G.picardDegree (G.divisorClass D) :=
          (G.picardDegree_divisorClass D).symm
        _ = G.picardDegree C.1 := congrArg G.picardDegree hclass
        _ = (k : ℤ) := C.2
    let E : EffectiveDivisorDegree V k := ⟨D, hDEffective, hdegree⟩
    refine ⟨E, ?_⟩
    apply Subtype.ext
    exact hclass

/-- The easy direction of Theorem 2.8: Riemann--Roch implies that every
degree at least the genus is winnable, hence represented by an effective
divisor. -/
theorem abelJacobi_surjective_of_genus_le
    (G : LooplessMultigraph V) [Nonempty V] [DecidableEq V]
    (hconn : G.Connected) (k : ℕ) (hgenus : G.genus ≤ (k : ℤ)) :
    Function.Surjective (G.abelJacobi k) := by
  rw [G.abelJacobi_surjective_iff_every_class_effective k]
  intro C
  obtain ⟨D, hclass⟩ := G.laplacianLattice.mkQ_surjective C.1
  have hclass' : G.divisorClass D = C.1 := hclass
  have hdegree : Divisor.degree D = (k : ℤ) := by
    calc
      Divisor.degree D = G.picardDegree (G.divisorClass D) :=
        (G.picardDegree_divisorClass D).symm
      _ = G.picardDegree C.1 := congrArg G.picardDegree hclass'
      _ = (k : ℤ) := C.2
  have hconnBN : graph_connected G.toBakerNorineGraph :=
    G.graph_connected_toBakerNorineGraph hconn
  have hdegreeBN : deg (G := G.toBakerNorineGraph) D ≥
      _root_.genus G.toBakerNorineGraph := by
    rw [G.deg_toBakerNorineGraph D, G.genus_toBakerNorineGraph]
    omega
  have hwinnable : winnable G.toBakerNorineGraph D :=
    winnable_of_deg_ge_genus hconnBN D hdegreeBN
  have heffective : G.HasEffectiveRepresentative (G.divisorClass D) :=
    (G.winnable_toBakerNorineGraph_iff D).mp hwinnable
  rwa [hclass'] at heffective

/-- Below the genus, a nonwinnable divisor gives a Picard class missed by
the Abel--Jacobi map. -/
theorem abelJacobi_not_surjective_of_lt_genus
    (G : LooplessMultigraph V) [Nonempty V] [DecidableEq V]
    (hconn : G.Connected) (k : ℕ) (hk : (k : ℤ) < G.genus) :
    ¬ Function.Surjective (G.abelJacobi k) := by
  have hconnBN : graph_connected G.toBakerNorineGraph :=
    G.graph_connected_toBakerNorineGraph hconn
  let q : V := Classical.choice (inferInstance : Nonempty V)
  obtain ⟨D, hdegreeBN, hunwinnable⟩ :=
    exists_unwinnable_of_degree_lt_genus G.toBakerNorineGraph hconnBN q
      (by simpa only [G.genus_toBakerNorineGraph] using hk)
  have hdegree : Divisor.degree D = (k : ℤ) := by
    exact hdegreeBN
  have hnotEffective :
      ¬ G.HasEffectiveRepresentative (G.divisorClass D) := by
    intro heffective
    exact hunwinnable ((G.winnable_toBakerNorineGraph_iff D).mpr heffective)
  let C : G.PicardDegree (k : ℤ) :=
    ⟨G.divisorClass D, by
      rw [G.picardDegree_divisorClass]
      exact hdegree⟩
  intro hsurjective
  have hall :=
    (G.abelJacobi_surjective_iff_every_class_effective k).mp hsurjective
  exact hnotEffective (hall C)

/-- Theorem 2.8 (Baker--Norine Theorem 1.7): the degree-`k`
Abel--Jacobi map of a connected graph is surjective exactly for `k ≥ g`. -/
theorem abelJacobi_surjective_iff
    (G : LooplessMultigraph V) [Nonempty V] [DecidableEq V]
    (hconn : G.Connected) (k : ℕ) :
    Function.Surjective (G.abelJacobi k) ↔ G.genus ≤ (k : ℤ) := by
  constructor
  · intro hsurjective
    by_contra hgenus
    have hk : (k : ℤ) < G.genus := lt_of_not_ge hgenus
    exact G.abelJacobi_not_surjective_of_lt_genus hconn k hk hsurjective
  · exact G.abelJacobi_surjective_of_genus_le hconn k

/-- The `k = 0` endpoint is genuinely part of Theorems 2.8 and 2.9: an
effective divisor of degree zero is the zero divisor, so the Abel--Jacobi map
is injective without any extra hypothesis. -/
theorem abelJacobi_zero_injective (G : LooplessMultigraph V) :
    Function.Injective (G.abelJacobi 0) := by
  intro D E h
  apply Subtype.ext
  rw [D.2.1.eq_zero_of_degree_eq_zero D.2.2,
    E.2.1.eq_zero_of_degree_eq_zero E.2.2]

/-- A vertex regarded as an element of the first symmetric power. -/
def vertexEffectiveDivisor [DecidableEq V] (v : V) :
    EffectiveDivisorDegree V 1 :=
  ⟨Divisor.vertexDivisor v, Divisor.isEffective_vertexDivisor v,
    Divisor.degree_vertexDivisor v⟩

@[simp]
theorem abelJacobi_vertexEffectiveDivisor
    (G : LooplessMultigraph V) [DecidableEq V] (v : V) :
    G.abelJacobi 1 (vertexEffectiveDivisor v) = G.vertexClass v :=
  rfl

omit [Fintype V] in
theorem vertexDivisor_injective [DecidableEq V] :
    Function.Injective (Divisor.vertexDivisor : V → Divisor V) := by
  intro v w hvw
  by_contra hne
  have heval := congrFun hvw v
  simp [Divisor.vertexDivisor, hne] at heval

/-- The degree-one symmetric-power map and the vertex-class map have the same
injectivity property. -/
theorem abelJacobi_one_injective_iff_vertexClass_injective
    (G : LooplessMultigraph V) [DecidableEq V] :
    Function.Injective (G.abelJacobi 1) ↔
      Function.Injective G.vertexClass := by
  constructor
  · intro hAbel v w hvw
    have himage :
        G.abelJacobi 1 (vertexEffectiveDivisor v) =
          G.abelJacobi 1 (vertexEffectiveDivisor w) := by
      simpa only [G.abelJacobi_vertexEffectiveDivisor] using hvw
    have hdivisor := congrArg Subtype.val (hAbel himage)
    exact vertexDivisor_injective hdivisor
  · intro hvertex D E himage
    obtain ⟨v, hDv⟩ :=
      D.2.1.eq_vertexDivisor_of_degree_one D.2.2
    obtain ⟨w, hEw⟩ :=
      E.2.1.eq_vertexDivisor_of_degree_one E.2.2
    have hvwClass : G.vertexClass v = G.vertexClass w := by
      apply Subtype.ext
      change G.divisorClass (Divisor.vertexDivisor v) =
        G.divisorClass (Divisor.vertexDivisor w)
      have hclass := congrArg Subtype.val himage
      simpa only [abelJacobi_coe, hDv, hEw] using hclass
    have hvw : v = w := hvertex hvwClass
    apply Subtype.ext
    calc
      D.1 = Divisor.vertexDivisor v := hDv
      _ = Divisor.vertexDivisor w := by rw [hvw]
      _ = E.1 := hEw.symm

/-- Corollary 2.10, with both directions: for a connected graph, the natural
vertex map into `Pic¹` is injective if and only if every nontrivial cut has
at least two edges (equivalently, the graph is bridge-free). -/
theorem vertexClass_injective_iff_bridgeFree
    (G : LooplessMultigraph V) [Nonempty V] [DecidableEq V]
    (hconn : G.Connected) :
    Function.Injective G.vertexClass ↔ G.BridgeFree := by
  rw [← G.abelJacobi_one_injective_iff_vertexClass_injective]
  simpa only [Nat.reduceAdd, G.edgeConnected_two_iff_bridgeFree] using
    G.abelJacobi_injective_iff_edgeConnected hconn 1

end LooplessMultigraph

end LeanCo.LaplacianLFunctions
