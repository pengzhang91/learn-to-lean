import LeanCo.SizeRamsey.GraphBasics
import LeanCo.SizeRamsey.Numerics
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Tactic

/-!
# The random bipartite host

This file supplies the probability space used in Lemma 2.1 of Wang--Wang.
There are `M` vertices on each side.  A sample is a subset of the `M * M`
ordered cross-pairs, chosen with the set-Bernoulli product measure, and each
pair is sent injectively to the corresponding unordered edge.

Keeping the sample space as sets of cross-pairs makes independence literal
and lets us identify the graph's edge count with a binomial random variable
without relying on the unfinished edge-count theorem for mathlib's general
binomial random graph.
-/

open MeasureTheory ProbabilityTheory Set unitInterval
open scoped ENNReal Finset ProbabilityTheory SimpleGraph

namespace LeanCo.SizeRamsey

noncomputable section

/-- The vertex type of a balanced bipartite graph with `M` vertices per side. -/
abbrev BalancedBipartiteVertex (M : ℕ) := Fin M ⊕ Fin M

/-- Indices for the `M * M` possible cross-edges. -/
abbrev BalancedBipartiteEdgeIndex (M : ℕ) := Fin M × Fin M

/-- A left-right pair determines an unordered cross-edge. -/
def crossEdgeEmbedding (M : ℕ) :
    BalancedBipartiteEdgeIndex M ↪ Sym2 (BalancedBipartiteVertex M) where
  toFun e := s(Sum.inl e.1, Sum.inr e.2)
  inj' := by
    intro e f hef
    rcases e with ⟨a, b⟩
    rcases f with ⟨c, d⟩
    simpa [Sym2.eq_iff] using hef

/-- The graph represented by a set of selected left-right pairs. -/
def bipartiteHost {M : ℕ} (E : Set (BalancedBipartiteEdgeIndex M)) :
    SimpleGraph (BalancedBipartiteVertex M) :=
  SimpleGraph.fromEdgeSet (crossEdgeEmbedding M '' E)

/-- Cross-edges are never diagonal. -/
theorem crossEdgeEmbedding_not_isDiag {M : ℕ}
    (e : BalancedBipartiteEdgeIndex M) :
    ¬ (crossEdgeEmbedding M e).IsDiag := by
  rcases e with ⟨a, b⟩
  simp [crossEdgeEmbedding, Sym2.mk_isDiag_iff]

/-- No selected edge is lost by `SimpleGraph.fromEdgeSet`. -/
@[simp]
theorem edgeSet_bipartiteHost {M : ℕ}
    (E : Set (BalancedBipartiteEdgeIndex M)) :
    (bipartiteHost E).edgeSet = crossEdgeEmbedding M '' E := by
  rw [bipartiteHost, SimpleGraph.edgeSet_fromEdgeSet]
  apply sdiff_eq_left.mpr
  rw [Set.disjoint_left]
  rintro _ ⟨e, _, rfl⟩ he
  exact crossEdgeEmbedding_not_isDiag e he

/-- The graph has exactly as many edges as the selected set of cross-pairs. -/
@[simp]
theorem edgeCount_bipartiteHost {M : ℕ}
    (E : Set (BalancedBipartiteEdgeIndex M)) :
    edgeCount (bipartiteHost E) = E.ncard := by
  rw [edgeCount, edgeSet_bipartiteHost, Nat.card_coe_set_eq,
    Set.ncard_image_of_injective _ (crossEdgeEmbedding M).injective]

/-- Every graph produced by `bipartiteHost` is a subgraph of the complete
balanced bipartite graph. -/
theorem bipartiteHost_le_completeBipartiteGraph {M : ℕ}
    (E : Set (BalancedBipartiteEdgeIndex M)) :
    bipartiteHost E ≤ completeBipartiteGraph (Fin M) (Fin M) := by
  rw [bipartiteHost, SimpleGraph.fromEdgeSet_le]
  intro e he
  rw [SimpleGraph.edgeSet_completeBipartiteGraph]
  rcases he.1 with ⟨x, _, rfl⟩
  exact ⟨x, rfl⟩

/-- The canonical left and right copies form a bipartition of every host. -/
theorem bipartiteHost_isBipartiteWith {M : ℕ}
    (E : Set (BalancedBipartiteEdgeIndex M)) :
    (bipartiteHost E).IsBipartiteWith
      (Set.range (Sum.inl : Fin M → BalancedBipartiteVertex M))
      (Set.range (Sum.inr : Fin M → BalancedBipartiteVertex M)) := by
  have hcomplete :
      (completeBipartiteGraph (Fin M) (Fin M)).IsBipartiteWith
        (Set.range (Sum.inl : Fin M → BalancedBipartiteVertex M))
        (Set.range (Sum.inr : Fin M → BalancedBipartiteVertex M)) := by
    refine ⟨Set.isCompl_range_inl_range_inr.disjoint, ?_⟩
    intro v w hvw
    cases v <;> cases w <;> simp_all
  exact
    { disjoint := hcomplete.disjoint
      mem_of_adj := fun {_ _} h =>
        hcomplete.mem_of_adj ((bipartiteHost_le_completeBipartiteGraph E) h) }

/-- In particular, every graph in the support is bipartite. -/
theorem bipartiteHost_isBipartite {M : ℕ}
    (E : Set (BalancedBipartiteEdgeIndex M)) :
    (bipartiteHost E).IsBipartite :=
  (bipartiteHost_isBipartiteWith E).isBipartite

/-- Product Bernoulli measure on all `M * M` possible cross-edges. -/
def bipartiteEdgeMeasure (M : ℕ) (p : I) :
    Measure (Set (BalancedBipartiteEdgeIndex M)) :=
  setBer((Set.univ : Set (BalancedBipartiteEdgeIndex M)), p)

instance (M : ℕ) (p : I) : IsProbabilityMeasure (bipartiteEdgeMeasure M p) :=
  inferInstanceAs (IsProbabilityMeasure setBer((Set.univ :
    Set (BalancedBipartiteEdgeIndex M)), p))

/-- There are exactly `M * M` independently sampled possible edges. -/
theorem ncard_univ_balancedBipartiteEdgeIndex (M : ℕ) :
    (Set.univ : Set (BalancedBipartiteEdgeIndex M)).ncard = M * M := by
  simp [Nat.card_eq_fintype_card]

/-- The number of selected cross-pairs has the binomial distribution
`Bin(M * M, p)`. -/
theorem map_ncard_bipartiteEdgeMeasure (M : ℕ) (p : I) :
    (bipartiteEdgeMeasure M p).map Set.ncard = Bin(M * M, p) := by
  apply Measure.ext_of_singleton
  intro k
  rw [bipartiteEdgeMeasure,
    map_ncard_setBernoulli_singleton (Set.toFinite _),
    binomial_singleton, ncard_univ_balancedBipartiteEdgeIndex]

/-- The selected-pair cardinality, viewed as a random variable on the
set-Bernoulli sample space, has the expected binomial law. -/
theorem hasLaw_ncard_bipartiteEdges (M : ℕ) (p : I) :
    HasLaw (fun E : Set (BalancedBipartiteEdgeIndex M) => E.ncard)
      Bin(M * M, p) (bipartiteEdgeMeasure M p) where
  aemeasurable := by fun_prop
  map_eq := map_ncard_bipartiteEdgeMeasure M p

/-- Consequently the actual graph edge count has law `Bin(M * M, p)`. -/
theorem hasLaw_edgeCount_bipartiteHost (M : ℕ) (p : I) :
    HasLaw (fun E : Set (BalancedBipartiteEdgeIndex M) =>
      edgeCount (bipartiteHost E)) Bin(M * M, p) (bipartiteEdgeMeasure M p) := by
  apply (hasLaw_ncard_bipartiteEdges M p).congr
  filter_upwards [] with E
  exact edgeCount_bipartiteHost E

/-! ## Finite union bounds and exponential binomial bounds -/

/-- Finite union bound in the event notation used below.  No measurability
hypothesis on the individual events is needed. -/
theorem measureReal_exists_mem_finset_le {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (indices : Finset ι) (A : ι → Set Ω) :
    P.real {ω | ∃ i ∈ indices, ω ∈ A i} ≤
      ∑ i ∈ indices, P.real (A i) := by
  have heq : {ω | ∃ i ∈ indices, ω ∈ A i} = ⋃ i ∈ indices, A i := by
    ext ω
    simp
  rw [heq]
  exact measureReal_biUnion_finset_le indices A

/-- A convenient fully explicit binomial-coefficient bound.  The usual
constant is `exp 1`; the slightly weaker constant `3` avoids carrying a
transcendental constant through the numerical union-bound calculation. -/
theorem natChoose_cast_le_three_mul_div_pow (a b : ℕ) (hb : 1 ≤ b) :
    (a.choose b : ℝ) ≤ ((3 * (a : ℝ)) / b) ^ b := by
  have hbpos : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * b) := by
    rw [Real.one_le_sqrt]
    have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
    nlinarith [Real.pi_gt_three]
  have hbase : (b : ℝ) / 3 ≤ (b : ℝ) / Real.exp 1 := by
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg b) (Real.exp_pos 1)
      Real.exp_one_lt_three.le
  have hfac : ((b : ℝ) / 3) ^ b ≤ (b.factorial : ℝ) := by
    calc
      ((b : ℝ) / 3) ^ b ≤ ((b : ℝ) / Real.exp 1) ^ b := by
        exact pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg b) (by norm_num)) hbase b
      _ ≤ Real.sqrt (2 * Real.pi * b) *
          ((b : ℝ) / Real.exp 1) ^ b := by
        calc
          ((b : ℝ) / Real.exp 1) ^ b =
              1 * ((b : ℝ) / Real.exp 1) ^ b := by ring
          _ ≤ Real.sqrt (2 * Real.pi * b) *
              ((b : ℝ) / Real.exp 1) ^ b :=
            mul_le_mul_of_nonneg_right hsqrt
              (pow_nonneg (div_nonneg (Nat.cast_nonneg b) (Real.exp_pos 1).le) b)
      _ ≤ (b.factorial : ℝ) := Stirling.le_factorial_stirling b
  calc
    (a.choose b : ℝ) ≤ (a : ℝ) ^ b / (b.factorial : ℝ) :=
      Nat.choose_le_pow_div b a
    _ ≤ (a : ℝ) ^ b / (((b : ℝ) / 3) ^ b) := by
      exact div_le_div_of_nonneg_left (pow_nonneg (Nat.cast_nonneg a) b)
        (pow_pos (div_pos hbpos (by norm_num)) b) hfac
    _ = ((3 * (a : ℝ)) / b) ^ b := by
      rw [← div_pow]
      congr 1
      field_simp

/-- Exact moment-generating function of a binomial random variable. -/
theorem integral_exp_nat_binomial (trials : ℕ) (p : I) (t : ℝ) :
    ∫ x : ℕ, Real.exp (t * x) ∂Bin(trials, p) =
      (1 - (p : ℝ) + (p : ℝ) * Real.exp t) ^ trials := by
  rw [integral_binomial]
  rw [← Nat.range_succ_eq_Iic]
  rw [show (1 - (p : ℝ) + (p : ℝ) * Real.exp t) ^ trials =
    ((p : ℝ) * Real.exp t + (1 - (p : ℝ))) ^ trials by ring]
  rw [add_pow]
  apply Finset.sum_congr rfl
  intro k _
  have hexp : Real.exp (t * (k : ℝ)) = Real.exp t ^ k := by
    rw [mul_comm, Real.exp_nat_mul]
  rw [hexp]
  ring

/-- Chernoff's exponential-transform upper-tail bound for a binomial law.
The free positive parameter `t` can later be optimized or instantiated by a
convenient constant. -/
theorem binomial_chernoff_upper (trials : ℕ) (p : I)
    {t : ℝ} (ht : 0 < t) (a : ℝ) :
    Bin(trials, p).real {x : ℕ | a ≤ x} ≤
      Real.exp (-t * a) *
        (1 - (p : ℝ) + (p : ℝ) * Real.exp t) ^ trials := by
  let f : ℕ → ℝ := fun x => Real.exp (t * x)
  have hmarkov := MeasureTheory.mul_meas_ge_le_integral_of_nonneg
    (μ := Bin(trials, p)) (f := f)
    (ae_of_all _ fun _ => (Real.exp_pos _).le)
    (integrable_binomial f) (Real.exp (t * a))
  have hevent :
      {x : ℕ | Real.exp (t * a) ≤ f x} = {x : ℕ | a ≤ x} := by
    ext x
    simp only [Set.mem_setOf_eq, f, Real.exp_le_exp]
    exact mul_le_mul_iff_right₀ ht
  rw [hevent, integral_exp_nat_binomial] at hmarkov
  calc
    Bin(trials, p).real {x : ℕ | a ≤ x} ≤
        (1 - (p : ℝ) + (p : ℝ) * Real.exp t) ^ trials /
          Real.exp (t * a) := by
      rw [le_div_iff₀ (Real.exp_pos _)]
      simpa [mul_comm] using hmarkov
    _ = Real.exp (-t * a) *
        (1 - (p : ℝ) + (p : ℝ) * Real.exp t) ^ trials := by
      rw [show -t * a = -(t * a) by ring, Real.exp_neg]
      ring

/-- Chernoff's exponential-transform lower-tail bound for a binomial law. -/
theorem binomial_chernoff_lower (trials : ℕ) (p : I)
    {t : ℝ} (ht : t < 0) (a : ℝ) :
    Bin(trials, p).real {x : ℕ | (x : ℝ) ≤ a} ≤
      Real.exp (-t * a) *
        (1 - (p : ℝ) + (p : ℝ) * Real.exp t) ^ trials := by
  let f : ℕ → ℝ := fun x => Real.exp (t * x)
  have hmarkov := MeasureTheory.mul_meas_ge_le_integral_of_nonneg
    (μ := Bin(trials, p)) (f := f)
    (ae_of_all _ fun _ => (Real.exp_pos _).le)
    (integrable_binomial f) (Real.exp (t * a))
  have hevent :
      {x : ℕ | Real.exp (t * a) ≤ f x} = {x : ℕ | (x : ℝ) ≤ a} := by
    ext x
    simp only [Set.mem_setOf_eq, f, Real.exp_le_exp]
    constructor <;> intro h <;> nlinarith
  rw [hevent, integral_exp_nat_binomial] at hmarkov
  calc
    Bin(trials, p).real {x : ℕ | (x : ℝ) ≤ a} ≤
        (1 - (p : ℝ) + (p : ℝ) * Real.exp t) ^ trials /
          Real.exp (t * a) := by
      rw [le_div_iff₀ (Real.exp_pos _)]
      simpa [mul_comm] using hmarkov
    _ = Real.exp (-t * a) *
        (1 - (p : ℝ) + (p : ℝ) * Real.exp t) ^ trials := by
      rw [show -t * a = -(t * a) by ring, Real.exp_neg]
      ring

/-- A small numerical exponential bound used to keep the final Chernoff
calculation rational. -/
theorem exp_neg_two_lt_one_six : Real.exp (-2) < (1 : ℝ) / 6 := by
  have hexpTwo : (6 : ℝ) < Real.exp 2 := by
    rw [show (2 : ℝ) = (2 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
    nlinarith [Real.exp_one_gt_d9]
  rw [Real.exp_neg]
  simpa only [one_div] using
    (one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 6) hexpTwo)

/-- A deliberately coarse upper-tail estimate at twice the mean. -/
theorem binomial_two_mean_upper_lt_one_six (trials : ℕ) (p : I)
    (hmean : 100 ≤ (trials : ℝ) * (p : ℝ)) :
    Bin(trials, p).real
        {x : ℕ | 2 * ((trials : ℝ) * (p : ℝ)) ≤ x} < 1 / 6 := by
  let μ : ℝ := (trials : ℝ) * (p : ℝ)
  have hlogpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hchern := binomial_chernoff_upper trials p hlogpos (2 * μ)
  have hmgf :
      1 - (p : ℝ) + (p : ℝ) * Real.exp (Real.log 2) = 1 + (p : ℝ) := by
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    ring
  rw [hmgf] at hchern
  have hpow : (1 + (p : ℝ)) ^ trials ≤ Real.exp μ := by
    have hbase0 : 0 ≤ 1 + (p : ℝ) := by
      exact add_nonneg (by norm_num) p.property.1
    have hbaseExp : 1 + (p : ℝ) ≤ Real.exp (p : ℝ) := by
      simpa only [add_comm] using Real.add_one_le_exp (p : ℝ)
    calc
      (1 + (p : ℝ)) ^ trials ≤ Real.exp (p : ℝ) ^ trials := by
        exact pow_le_pow_left₀ hbase0 hbaseExp trials
      _ = Real.exp ((trials : ℝ) * (p : ℝ)) := by
        rw [Real.exp_nat_mul]
      _ = Real.exp μ := rfl
  have hexponent : (1 - 2 * Real.log 2) * μ ≤ -2 := by
    have hgap : 0 ≤ 2 * Real.log 2 - 1 - (3 : ℝ) / 10 := by
      nlinarith [Real.log_two_gt_d9]
    have hmean' : 0 ≤ μ - 100 := by simpa only [μ] using sub_nonneg.mpr hmean
    nlinarith [mul_nonneg hgap hmean']
  calc
    Bin(trials, p).real {x : ℕ | 2 * ((trials : ℝ) * (p : ℝ)) ≤ x} ≤
        Real.exp (-Real.log 2 * (2 * μ)) * (1 + (p : ℝ)) ^ trials :=
      hchern
    _ ≤ Real.exp (-Real.log 2 * (2 * μ)) * Real.exp μ := by
      exact mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
    _ = Real.exp ((1 - 2 * Real.log 2) * μ) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-2) := Real.exp_le_exp.mpr hexponent
    _ < 1 / 6 := exp_neg_two_lt_one_six

/-- A deliberately coarse lower-tail estimate at half the mean. -/
theorem binomial_half_mean_lower_lt_one_six (trials : ℕ) (p : I)
    (hmean : 100 ≤ (trials : ℝ) * (p : ℝ)) :
    Bin(trials, p).real
        {x : ℕ | (x : ℝ) ≤ ((trials : ℝ) * (p : ℝ)) / 2} < 1 / 6 := by
  let μ : ℝ := (trials : ℝ) * (p : ℝ)
  have hlogpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hchern := binomial_chernoff_lower trials p (neg_lt_zero.mpr hlogpos) (μ / 2)
  have hexpneglog : Real.exp (-Real.log 2) = (1 : ℝ) / 2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hmgf :
      1 - (p : ℝ) + (p : ℝ) * Real.exp (-Real.log 2) =
        1 - (p : ℝ) / 2 := by
    rw [hexpneglog]
    ring
  rw [hmgf] at hchern
  have hbase0 : 0 ≤ 1 - (p : ℝ) / 2 := by
    have hp1 : (p : ℝ) ≤ 1 := p.property.2
    nlinarith
  have hbaseExp : 1 - (p : ℝ) / 2 ≤ Real.exp (-(p : ℝ) / 2) := by
    have h := Real.add_one_le_exp (-(p : ℝ) / 2)
    nlinarith
  have hpow : (1 - (p : ℝ) / 2) ^ trials ≤ Real.exp (-μ / 2) := by
    calc
      (1 - (p : ℝ) / 2) ^ trials ≤
          Real.exp (-(p : ℝ) / 2) ^ trials :=
        pow_le_pow_left₀ hbase0 hbaseExp trials
      _ = Real.exp ((trials : ℝ) * (-(p : ℝ) / 2)) := by
        rw [Real.exp_nat_mul]
      _ = Real.exp (-μ / 2) := by
        congr 1
        dsimp only [μ]
        ring
  have hexponent : (Real.log 2 - 1) * μ / 2 ≤ -2 := by
    have hgap : 0 ≤ 1 - Real.log 2 - (3 : ℝ) / 10 := by
      nlinarith [Real.log_two_lt_d9]
    have hmean' : 0 ≤ μ - 100 := by simpa only [μ] using sub_nonneg.mpr hmean
    nlinarith [mul_nonneg hgap hmean']
  calc
    Bin(trials, p).real
        {x : ℕ | (x : ℝ) ≤ ((trials : ℝ) * (p : ℝ)) / 2} ≤
      Real.exp (-(-Real.log 2) * (μ / 2)) *
        (1 - (p : ℝ) / 2) ^ trials := hchern
    _ ≤ Real.exp (-(-Real.log 2) * (μ / 2)) * Real.exp (-μ / 2) := by
      exact mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
    _ = Real.exp ((Real.log 2 - 1) * μ / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-2) := Real.exp_le_exp.mpr hexponent
    _ < 1 / 6 := exp_neg_two_lt_one_six

/-! ## Fixed-set selection bounds -/

/-- Under a set-Bernoulli law, every edge in a fixed finite set is present
with probability exactly `p ^ |A|`. -/
theorem setBernoulli_superset_apply {ι : Type*} [Countable ι]
    (u : Set ι) (p : I) (A : Finset ι) (hA : (A : Set ι) ⊆ u) :
    setBer(u, p) {s : Set ι | (A : Set ι) ⊆ s} =
      (toNNReal p : ℝ≥0∞) ^ #A := by
  rw [setBernoulli_apply']
  let S : Set ((i : A) → Prop) := {q | ∀ i, q i}
  have hevent :
      (fun q : ι → Prop => {i | q i}) ⁻¹'
          {s : Set ι | (A : Set ι) ⊆ s} = cylinder A S := by
    ext q
    simp only [Set.mem_preimage, Set.mem_setOf_eq, mem_cylinder, S]
    constructor
    · intro h i
      exact h i.property
    · intro h i hi
      exact h ⟨i, hi⟩
  rw [hevent, Measure.infinitePi_cylinder _ (by measurability : MeasurableSet S)]
  have hS : S = {fun _ => True} := by
    ext q
    simp [S, funext_iff]
  rw [hS, Measure.pi_singleton]
  have hfactor (i : A) :
      (toNNReal p • Measure.dirac ((i : ι) ∈ u) +
        toNNReal (σ p) • Measure.dirac False) {True} =
          (toNNReal p : ℝ≥0∞) := by
    simp [hA i.property]
  simp_rw [hfactor]
  simp

/-- The selected elements of `A` in a sample set `E`. -/
noncomputable def selectedFinset {ι : Type*} (A : Finset ι) (E : Set ι) : Finset ι := by
  classical
  exact A.filter fun e => e ∈ E

@[simp]
theorem mem_selectedFinset {ι : Type*} {A : Finset ι} {E : Set ι} {e : ι} :
    e ∈ selectedFinset A E ↔ e ∈ A ∧ e ∈ E := by
  classical
  simp [selectedFinset]

/-- Union-bound tail estimate used for local sparsity: if at least `m`
elements of a fixed finite candidate set are selected, then some `m`-subset
of candidates is selected in full. -/
theorem setBernoulli_fixedSet_tail {ι : Type*} [Countable ι]
    (u : Set ι) (p : I) (A : Finset ι) (hA : (A : Set ι) ⊆ u) (m : ℕ) :
    setBer(u, p) {E : Set ι | m ≤ #(selectedFinset A E)} ≤
      (A.card.choose m : ℝ≥0∞) * (toNNReal p : ℝ≥0∞) ^ m := by
  classical
  let event : Finset ι → Set (Set ι) := fun B => {E | (B : Set ι) ⊆ E}
  have hsubset : {E : Set ι | m ≤ #(selectedFinset A E)} ⊆
      ⋃ B ∈ A.powersetCard m, event B := by
    intro E hE
    obtain ⟨B, hB, hBcard⟩ := Finset.exists_subset_card_eq hE
    have hBA : B ⊆ A := fun e he => (mem_selectedFinset.mp (hB he)).1
    have hBE : (B : Set ι) ⊆ E := by
      intro e he
      exact (mem_selectedFinset.mp (hB he)).2
    simp only [Set.mem_iUnion, event, Set.mem_setOf_eq]
    exact ⟨B, ⟨by simpa [Finset.mem_powersetCard] using And.intro hBA hBcard, hBE⟩⟩
  calc
    setBer(u, p) {E : Set ι | m ≤ #(selectedFinset A E)} ≤
        setBer(u, p) (⋃ B ∈ A.powersetCard m, event B) := measure_mono hsubset
    _ ≤ ∑ B ∈ A.powersetCard m, setBer(u, p) (event B) :=
      measure_biUnion_finset_le _ _
    _ = (A.card.choose m : ℝ≥0∞) * (toNNReal p : ℝ≥0∞) ^ m := by
      have hterm (B : Finset ι) (hB : B ∈ A.powersetCard m) :
          setBer(u, p) (event B) = (toNNReal p : ℝ≥0∞) ^ m := by
        rw [setBernoulli_superset_apply]
        · congr 1
          exact (Finset.mem_powersetCard.mp hB).2
        · intro e he
          exact hA ((Finset.mem_powersetCard.mp hB).1 he)
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul,
        Finset.card_powersetCard]

/-- Real-valued form of `setBernoulli_fixedSet_tail`. -/
theorem setBernoulli_fixedSet_tail_real {ι : Type*} [Countable ι]
    (u : Set ι) (p : I) (A : Finset ι) (hA : (A : Set ι) ⊆ u) (m : ℕ) :
    setBer(u, p).real {E : Set ι | m ≤ #(selectedFinset A E)} ≤
      (A.card.choose m : ℝ) * (p : ℝ) ^ m := by
  rw [measureReal_def]
  calc
    (setBer(u, p) {E : Set ι | m ≤ #(selectedFinset A E)}).toReal ≤
        ((A.card.choose m : ℝ≥0∞) * (toNNReal p : ℝ≥0∞) ^ m).toReal := by
      rw [ENNReal.toReal_le_toReal (measure_ne_top _ _) (by finiteness)]
      exact setBernoulli_fixedSet_tail u p A hA m
    _ = (A.card.choose m : ℝ) * (p : ℝ) ^ m := by
      simp [unitInterval.coe_toNNReal]

/-! ## Candidate edges spanned by a vertex set -/

/-- Cross-edge indices whose two endpoints lie in `U`. -/
def eligibleCrossEdgeFinset (M : ℕ)
    (U : Finset (BalancedBipartiteVertex M)) :
    Finset (BalancedBipartiteEdgeIndex M) :=
  Finset.univ.filter fun e => Sum.inl e.1 ∈ U ∧ Sum.inr e.2 ∈ U

@[simp]
theorem mem_eligibleCrossEdgeFinset {M : ℕ}
    {U : Finset (BalancedBipartiteVertex M)}
    {e : BalancedBipartiteEdgeIndex M} :
    e ∈ eligibleCrossEdgeFinset M U ↔
      Sum.inl e.1 ∈ U ∧ Sum.inr e.2 ∈ U := by
  simp [eligibleCrossEdgeFinset]

/-- The number of host edges spanned by `U` is exactly the number of selected
eligible cross-edge indices. -/
theorem spannedEdgeCount_bipartiteHost {M : ℕ}
    (E : Set (BalancedBipartiteEdgeIndex M))
    (U : Finset (BalancedBipartiteVertex M)) :
    spannedEdgeCount (bipartiteHost E)
        (U : Set (BalancedBipartiteVertex M)) =
      #(selectedFinset (eligibleCrossEdgeFinset M U) E) := by
  classical
  letI : Fintype (U : Set (BalancedBipartiteVertex M)) :=
    Subtype.fintype (Membership.mem (U : Set (BalancedBipartiteVertex M)))
  have hedge :
      (bipartiteHost E).edgeFinset ∩ U.sym2 =
        (selectedFinset (eligibleCrossEdgeFinset M U) E).map
          (crossEdgeEmbedding M) := by
    apply Finset.ext
    intro e
    constructor
    · intro h
      rw [Finset.mem_inter] at h
      obtain ⟨he, hU⟩ := h
      rw [SimpleGraph.mem_edgeFinset, edgeSet_bipartiteHost] at he
      rcases he with ⟨x, hx, rfl⟩
      apply Finset.mem_map.mpr
      refine ⟨x, ?_, rfl⟩
      rw [mem_selectedFinset]
      refine ⟨?_, hx⟩
      simpa [eligibleCrossEdgeFinset] using
        (Finset.mk_mem_sym2_iff.mp hU)
    · intro he
      rcases Finset.mem_map.mp he with ⟨x, hx, rfl⟩
      rw [mem_selectedFinset] at hx
      rw [Finset.mem_inter]
      constructor
      · rw [SimpleGraph.mem_edgeFinset, edgeSet_bipartiteHost]
        exact ⟨x, hx.2, rfl⟩
      · change s(Sum.inl x.1, Sum.inr x.2) ∈ U.sym2
        rw [Finset.mk_mem_sym2_iff]
        simpa [eligibleCrossEdgeFinset] using hx.1
  calc
    spannedEdgeCount (bipartiteHost E)
        (U : Set (BalancedBipartiteVertex M)) =
        #((bipartiteHost E).induce
          (U : Set (BalancedBipartiteVertex M))).edgeFinset :=
      edgeCount_eq_card_edgeFinset _
    _ = #(((bipartiteHost E).induce
        (U : Set (BalancedBipartiteVertex M))).edgeFinset.map
        (Function.Embedding.subtype
          (fun x => x ∈ (U : Set (BalancedBipartiteVertex M)))).sym2Map) :=
      (Finset.card_map _).symm
    _ = #((bipartiteHost E).edgeFinset ∩ U.sym2) := by
      have hmap := SimpleGraph.map_edgeFinset_induce
        (G := bipartiteHost E)
        (s := (U : Set (BalancedBipartiteVertex M)))
      have hcard := congrArg Finset.card hmap
      simpa using hcard
    _ = #((selectedFinset (eligibleCrossEdgeFinset M U) E).map
        (crossEdgeEmbedding M)) := by rw [hedge]
    _ = #(selectedFinset (eligibleCrossEdgeFinset M U) E) := Finset.card_map _

/-- The number of possible cross-edges inside `U` is the product of the
numbers of left and right vertices in `U`. -/
theorem card_eligibleCrossEdgeFinset {M : ℕ}
    (U : Finset (BalancedBipartiteVertex M)) :
    #(eligibleCrossEdgeFinset M U) = #U.toLeft * #U.toRight := by
  classical
  have h : eligibleCrossEdgeFinset M U = U.toLeft.product U.toRight := by
    ext e
    simp [eligibleCrossEdgeFinset]
  rw [h]
  simp

/-- Bipartiteness gives the extremal bound `4 e(U) ≤ |U|²` already at
the level of possible cross-edges. -/
theorem four_mul_card_eligibleCrossEdgeFinset_le_sq {M : ℕ}
    (U : Finset (BalancedBipartiteVertex M)) :
    4 * #(eligibleCrossEdgeFinset M U) ≤ #U ^ 2 := by
  rw [card_eligibleCrossEdgeFinset, ← Finset.card_toLeft_add_card_toRight]
  simpa [Nat.mul_assoc] using
    (four_mul_le_sq_add (#U.toLeft : ℕ) (#U.toRight : ℕ))

/-- Fixed-vertex-set upper tail for the number of induced host edges. -/
theorem bipartiteHost_fixedSet_tail_real (M : ℕ) (p : I)
    (U : Finset (BalancedBipartiteVertex M)) (m : ℕ) :
    (bipartiteEdgeMeasure M p).real
        {E | m ≤ spannedEdgeCount (bipartiteHost E)
          (U : Set (BalancedBipartiteVertex M))} ≤
      ((eligibleCrossEdgeFinset M U).card.choose m : ℝ) * (p : ℝ) ^ m := by
  simpa only [bipartiteEdgeMeasure, spannedEdgeCount_bipartiteHost] using
    setBernoulli_fixedSet_tail_real
      (Set.univ : Set (BalancedBipartiteEdgeIndex M)) p
      (eligibleCrossEdgeFinset M U) (by simp) m

/-- Failure event for one prescribed vertex-set size and edge threshold. -/
def badSpannedEventAtSize (M u m : ℕ) :
    Set (Set (BalancedBipartiteEdgeIndex M)) :=
  {E | ∃ U ∈ (Finset.univ : Finset (BalancedBipartiteVertex M)).powersetCard u,
    m ≤ spannedEdgeCount (bipartiteHost E)
      (U : Set (BalancedBipartiteVertex M))}

/-- The direct finite union bound over all `u`-vertex sets. -/
theorem measureReal_badSpannedEventAtSize_le_sum (M u m : ℕ) (p : I) :
    (bipartiteEdgeMeasure M p).real (badSpannedEventAtSize M u m) ≤
      ∑ U ∈ (Finset.univ : Finset (BalancedBipartiteVertex M)).powersetCard u,
        ((eligibleCrossEdgeFinset M U).card.choose m : ℝ) * (p : ℝ) ^ m := by
  let vertexSets :=
    (Finset.univ : Finset (BalancedBipartiteVertex M)).powersetCard u
  let event : Finset (BalancedBipartiteVertex M) →
      Set (Set (BalancedBipartiteEdgeIndex M)) := fun U =>
    {E | m ≤ spannedEdgeCount (bipartiteHost E)
      (U : Set (BalancedBipartiteVertex M))}
  calc
    (bipartiteEdgeMeasure M p).real (badSpannedEventAtSize M u m) ≤
        ∑ U ∈ vertexSets,
          (bipartiteEdgeMeasure M p).real (event U) := by
      exact measureReal_exists_mem_finset_le
        (bipartiteEdgeMeasure M p) vertexSets event
    _ ≤ ∑ U ∈ vertexSets,
        ((eligibleCrossEdgeFinset M U).card.choose m : ℝ) * (p : ℝ) ^ m := by
      exact Finset.sum_le_sum fun U _ => bipartiteHost_fixedSet_tail_real M p U m

/-- The number of `u`-subsets of the `2M` host vertices. -/
theorem card_vertexPowersetCard (M u : ℕ) :
    #((Finset.univ : Finset (BalancedBipartiteVertex M)).powersetCard u) =
      (2 * M).choose u := by
  rw [Finset.card_powersetCard]
  rw [Finset.card_univ]
  simp only [Fintype.card_sum, Fintype.card_fin]
  congr 1
  omega

/-- Every `u`-vertex set has at most `⌊u²/4⌋` possible cross-edges. -/
theorem card_eligibleCrossEdgeFinset_le_quarter_sq {M u : ℕ}
    {U : Finset (BalancedBipartiteVertex M)} (hU : #U = u) :
    #(eligibleCrossEdgeFinset M U) ≤ u ^ 2 / 4 := by
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).2
  rw [← hU]
  simpa [Nat.mul_comm] using four_mul_card_eligibleCrossEdgeFinset_le_sq U

/-- Paper-form fixed-size estimate:
`choose(2M,u) * choose(⌊u²/4⌋,m) * p^m`. -/
theorem measureReal_badSpannedEventAtSize_le (M u m : ℕ) (p : I) :
    (bipartiteEdgeMeasure M p).real (badSpannedEventAtSize M u m) ≤
      ((2 * M).choose u : ℝ) *
        (((u ^ 2 / 4).choose m : ℝ) * (p : ℝ) ^ m) := by
  have hsum :
      (∑ U ∈ (Finset.univ : Finset (BalancedBipartiteVertex M)).powersetCard u,
          ((eligibleCrossEdgeFinset M U).card.choose m : ℝ) * (p : ℝ) ^ m) ≤
        ((2 * M).choose u : ℝ) *
          (((u ^ 2 / 4).choose m : ℝ) * (p : ℝ) ^ m) := by
    have hle :
        (∑ U ∈ (Finset.univ : Finset (BalancedBipartiteVertex M)).powersetCard u,
            ((eligibleCrossEdgeFinset M U).card.choose m : ℝ) * (p : ℝ) ^ m) ≤
          ∑ _U ∈
            (Finset.univ : Finset (BalancedBipartiteVertex M)).powersetCard u,
              (((u ^ 2 / 4).choose m : ℝ) * (p : ℝ) ^ m) := by
      apply Finset.sum_le_sum
      intro U hU
      have hchoose :
          ((eligibleCrossEdgeFinset M U).card.choose m : ℝ) ≤
            ((u ^ 2 / 4).choose m : ℝ) := by
        exact_mod_cast Nat.choose_le_choose m
          (card_eligibleCrossEdgeFinset_le_quarter_sq
            ((Finset.mem_powersetCard.mp hU).2))
      exact mul_le_mul_of_nonneg_right hchoose
        (pow_nonneg (show 0 ≤ (p : ℝ) from p.property.1) m)
    rw [Finset.sum_const, nsmul_eq_mul, card_vertexPowersetCard] at hle
    exact hle
  exact le_trans (measureReal_badSpannedEventAtSize_le_sum M u m p) hsum

/-- After the elementary estimate `choose(a,b) ≤ (3a/b)^b`, the
fixed-size failure term has the analytic form used in the paper. -/
theorem fixedSizeCombinationTerm_le (M u m : ℕ) (p : I)
    (hu : 1 ≤ u) (hm : 1 ≤ m) :
    ((2 * M).choose u : ℝ) *
        (((u ^ 2 / 4).choose m : ℝ) * (p : ℝ) ^ m) ≤
      ((6 * (M : ℝ)) / u) ^ u *
        ((3 * (u : ℝ) ^ 2 * (p : ℝ)) / (4 * m)) ^ m := by
  have huR : (0 : ℝ) < u := by exact_mod_cast (show 0 < u by omega)
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hp0 : (0 : ℝ) ≤ p := p.property.1
  have hq0 : (0 : ℝ) ≤ (u ^ 2 / 4 : ℕ) := by positivity
  have hq : ((u ^ 2 / 4 : ℕ) : ℝ) ≤ (u : ℝ) ^ 2 / 4 := by
    have hnat : 4 * (u ^ 2 / 4) ≤ u ^ 2 := Nat.mul_div_le _ _
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).2
    exact_mod_cast (by simpa [Nat.mul_comm] using hnat)
  have hfirst := natChoose_cast_le_three_mul_div_pow (2 * M) u hu
  have hsecond := natChoose_cast_le_three_mul_div_pow (u ^ 2 / 4) m hm
  have hsecond' :
      ((u ^ 2 / 4).choose m : ℝ) * (p : ℝ) ^ m ≤
        ((3 * (u : ℝ) ^ 2 * (p : ℝ)) / (4 * m)) ^ m := by
    calc
      ((u ^ 2 / 4).choose m : ℝ) * (p : ℝ) ^ m ≤
          ((3 * ((u ^ 2 / 4 : ℕ) : ℝ)) / m) ^ m *
            (p : ℝ) ^ m :=
        mul_le_mul_of_nonneg_right hsecond (pow_nonneg hp0 m)
      _ = (((3 * ((u ^ 2 / 4 : ℕ) : ℝ)) / m) * (p : ℝ)) ^ m := by
        rw [mul_pow]
      _ ≤ (((3 * ((u : ℝ) ^ 2 / 4) / m) * (p : ℝ))) ^ m := by
        apply pow_le_pow_left₀
        · positivity
        · apply mul_le_mul_of_nonneg_right _ hp0
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hq (by norm_num)) hmR.le
      _ = ((3 * (u : ℝ) ^ 2 * (p : ℝ)) / (4 * m)) ^ m := by
        congr 1
        field_simp
  calc
    ((2 * M).choose u : ℝ) *
        (((u ^ 2 / 4).choose m : ℝ) * (p : ℝ) ^ m) ≤
      ((3 * ((2 * M : ℕ) : ℝ)) / u) ^ u *
        (((u ^ 2 / 4).choose m : ℝ) * (p : ℝ) ^ m) := by
      exact mul_le_mul_of_nonneg_right hfirst
        (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp0 m))
    _ ≤ ((3 * ((2 * M : ℕ) : ℝ)) / u) ^ u *
        ((3 * (u : ℝ) ^ 2 * (p : ℝ)) / (4 * m)) ^ m := by
      exact mul_le_mul_of_nonneg_left hsecond' (pow_nonneg (by positivity) u)
    _ = ((6 * (M : ℝ)) / u) ^ u *
        ((3 * (u : ℝ) ^ 2 * (p : ℝ)) / (4 * m)) ^ m := by
      have hbase : (3 * ((2 * M : ℕ) : ℝ)) / u =
          (6 * (M : ℝ)) / u := by
        norm_num
        ring
      rw [hbase]

/-- Transfer of upper-tail events from graph edge count to its binomial law. -/
theorem measureReal_edgeCount_ge_eq_binomial (M : ℕ) (p : I) (a : ℝ) :
    (bipartiteEdgeMeasure M p).real
        {E | a ≤ edgeCount (bipartiteHost E)} =
      Bin(M * M, p).real {x : ℕ | a ≤ x} := by
  exact (hasLaw_edgeCount_bipartiteHost M p).measureReal_eq
    (p := fun x : ℕ => a ≤ x) (by measurability)

/-- Transfer of lower-tail events from graph edge count to its binomial law. -/
theorem measureReal_edgeCount_le_eq_binomial (M : ℕ) (p : I) (a : ℝ) :
    (bipartiteEdgeMeasure M p).real
        {E | (edgeCount (bipartiteHost E) : ℝ) ≤ a} =
      Bin(M * M, p).real {x : ℕ | (x : ℝ) ≤ a} := by
  exact (hasLaw_edgeCount_bipartiteHost M p).measureReal_eq
    (p := fun x : ℕ => (x : ℝ) ≤ a) (by measurability)

/-- Mean edge count of the balanced binomial host. -/
def bipartiteHostMean (M : ℕ) (p : I) : ℝ :=
  ((M * M : ℕ) : ℝ) * (p : ℝ)

/-- Failure of the deliberately closed interval used for the host edge
count.  Avoiding this event is slightly stronger than Lemma 2.1(1). -/
def badEdgeCountEvent (M : ℕ) (p : I) :
    Set (Set (BalancedBipartiteEdgeIndex M)) :=
  {E | (edgeCount (bipartiteHost E) : ℝ) ≤ bipartiteHostMean M p / 2 ∨
    2 * bipartiteHostMean M p ≤ edgeCount (bipartiteHost E)}

/-- Once the mean is at least `100`, the two Chernoff tails together have
probability strictly below `1/3`. -/
theorem measureReal_badEdgeCountEvent_lt_third (M : ℕ) (p : I)
    (hmean : 100 ≤ bipartiteHostMean M p) :
    (bipartiteEdgeMeasure M p).real (badEdgeCountEvent M p) < 1 / 3 := by
  let lower : Set (Set (BalancedBipartiteEdgeIndex M)) :=
    {E | (edgeCount (bipartiteHost E) : ℝ) ≤ bipartiteHostMean M p / 2}
  let upper : Set (Set (BalancedBipartiteEdgeIndex M)) :=
    {E | 2 * bipartiteHostMean M p ≤ edgeCount (bipartiteHost E)}
  have hevent : badEdgeCountEvent M p = lower ∪ upper := by
    ext E
    simp only [badEdgeCountEvent, lower, upper, Set.mem_setOf_eq, Set.mem_union]
  have hlower : (bipartiteEdgeMeasure M p).real lower < 1 / 6 := by
    dsimp only [lower]
    rw [measureReal_edgeCount_le_eq_binomial]
    exact binomial_half_mean_lower_lt_one_six (M * M) p hmean
  have hupper : (bipartiteEdgeMeasure M p).real upper < 1 / 6 := by
    dsimp only [upper]
    rw [measureReal_edgeCount_ge_eq_binomial]
    exact binomial_two_mean_upper_lt_one_six (M * M) p hmean
  rw [hevent]
  calc
    (bipartiteEdgeMeasure M p).real (lower ∪ upper) ≤
        (bipartiteEdgeMeasure M p).real lower +
          (bipartiteEdgeMeasure M p).real upper := measureReal_union_le _ _
    _ < 1 / 6 + 1 / 6 := add_lt_add hlower hupper
    _ = 1 / 3 := by norm_num

/-! ## Integer rounding and the all-set local-sparsity event -/

/-- The paper's integer threshold for a bad `u`-vertex set.  Thus the good
event says `e(U) < ⌈100 log(k) u⌉`. -/
def localFailureThreshold (k u : ℕ) : ℕ :=
  ⌈100 * Real.log (k : ℝ) * u⌉₊

/-- Integer-tail threshold tailored to the final `IsLocallySparse` contract.
Its complement is exactly the inequality `e(U) ≤ ⌈100 log k⌉·|U|`. -/
def integerLocalFailureThreshold (k u : ℕ) : ℕ :=
  localSparsityFactor k * u + 1

/-- Rounding once, before multiplication by `u`, only increases the local
edge threshold.  This is the bridge from the paper's strict real bound to
the integer-valued `IsLocallySparse` interface. -/
theorem localFailureThreshold_le (k u : ℕ) :
    localFailureThreshold k u ≤ localSparsityFactor k * u := by
  rw [localFailureThreshold, Nat.ceil_le]
  simp only [localSparsityFactor, Nat.cast_mul]
  exact mul_le_mul_of_nonneg_right (Nat.le_ceil _)
    (Nat.cast_nonneg u)

/-- A real edge probability satisfying the paper's admissibility condition
canonically determines a point of the unit interval. -/
def hostProbabilityUnit (k n : ℕ) (hk : 2 ≤ k)
    (hn : 100 * Real.log (k : ℝ) ≤ n) : I := by
  refine ⟨hostProbability k n, ?_, ?_⟩
  · exact div_nonneg (log_natCast_pos hk).le (Nat.cast_nonneg n)
  · have hnpos : (0 : ℝ) < n := by
      have hlog := log_natCast_pos hk
      nlinarith
    rw [hostProbability, div_le_one hnpos]
    have hlog := log_natCast_pos hk
    nlinarith

@[simp]
theorem coe_hostProbabilityUnit (k n : ℕ) (hk : 2 ≤ k)
    (hn : 100 * Real.log (k : ℝ) ≤ n) :
    (hostProbabilityUnit k n hk hn : ℝ) = hostProbability k n := rfl

/-- The abstract binomial mean agrees with the paper's `pM²`. -/
theorem bipartiteHostMean_hostParameters (k n : ℕ) (hk : 2 ≤ k)
    (hn : 100 * Real.log (k : ℝ) ≤ n) :
    bipartiteHostMean (hostPartSize k n) (hostProbabilityUnit k n hk hn) =
      hostProbability k n * (hostPartSize k n : ℝ) ^ 2 := by
  simp only [bipartiteHostMean, coe_hostProbabilityUnit, Nat.cast_mul]
  ring

/-- In the admissible range the expected number of host edges is far above
the coarse threshold needed by the Chernoff calculation. -/
theorem hundred_le_bipartiteHostMean_hostParameters
    {k n : ℕ} (hk : 2 ≤ k)
    (hn : 100 * Real.log (k : ℝ) ≤ n) :
    100 ≤ bipartiteHostMean (hostPartSize k n)
      (hostProbabilityUnit k n hk hn) := by
  have hnpos : 0 < n := by
    have hlog := log_natCast_pos hk
    have hnR : (0 : ℝ) < n := by nlinarith
    exact_mod_cast hnR
  rw [bipartiteHostMean_hostParameters, probability_mul_partSize_sq hnpos]
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkSq : (4 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have hlog : (69 : ℝ) / 100 ≤ Real.log (k : ℝ) := by
    have hmono : Real.log 2 ≤ Real.log (k : ℝ) :=
      Real.log_le_log (by norm_num) hkR
    nlinarith [Real.log_two_gt_d9]
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  calc
    (100 : ℝ) ≤ 10 ^ 10 * 4 * ((69 : ℝ) / 100) * 1 := by norm_num
    _ ≤ 10 ^ 10 * (k : ℝ) ^ 2 * Real.log (k : ℝ) * n := by
      gcongr

/-- The local sparsity factor has enormous slack already at `k = 2`. -/
theorem seventy_le_localSparsityFactor {k : ℕ} (hk : 2 ≤ k) :
    70 ≤ localSparsityFactor k := by
  have hceil : 100 * Real.log (k : ℝ) ≤
      (localSparsityFactor k : ℝ) := Nat.le_ceil _
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hmono : Real.log 2 ≤ Real.log (k : ℝ) :=
    Real.log_le_log (by norm_num) hkR
  have h69 : (69 : ℝ) < localSparsityFactor k := by
    nlinarith [Real.log_two_gt_d9]
  exact_mod_cast h69

/-- A coarse exponential consequence of the ceiling definition, useful for
closing the fixed-size numerical bound without real powers. -/
theorem natCast_le_two_pow_localSparsityFactor {k : ℕ} (hk : 2 ≤ k) :
    (k : ℝ) ≤ 2 ^ localSparsityFactor k := by
  have hkpos : (0 : ℝ) < k := by positivity
  have hceil : 100 * Real.log (k : ℝ) ≤
      (localSparsityFactor k : ℝ) := Nat.le_ceil _
  have hlog : Real.log (k : ℝ) ≤
      (localSparsityFactor k : ℝ) / 100 := by nlinarith
  have hsmall : Real.exp ((1 : ℝ) / 100) ≤ 2 := by
    calc
      Real.exp ((1 : ℝ) / 100) ≤ Real.exp (Real.log 2) := by
        rw [Real.exp_le_exp]
        nlinarith [Real.log_two_gt_d9]
      _ = 2 := Real.exp_log (by norm_num)
  calc
    (k : ℝ) = Real.exp (Real.log (k : ℝ)) :=
      (Real.exp_log hkpos).symm
    _ ≤ Real.exp ((localSparsityFactor k : ℝ) / 100) :=
      Real.exp_le_exp.mpr hlog
    _ = Real.exp ((1 : ℝ) / 100) ^ localSparsityFactor k := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ 2 ^ localSparsityFactor k :=
      pow_le_pow_left₀ (Real.exp_pos _).le hsmall _

/-- The final constant estimate in the local-sparsity union bound. -/
theorem localSparsityNumericalBase_lt_quarter {k : ℕ} (hk : 2 ≤ k) :
    4500 * (k : ℝ) *
        ((9 : ℝ) / 400) ^ (localSparsityFactor k - 1) < 1 / 4 := by
  let s := localSparsityFactor k
  have hs70 : 70 ≤ s := seventy_le_localSparsityFactor hk
  have ht4 : 4 ≤ s - 1 := by omega
  have hkpow : (k : ℝ) ≤ 2 ^ s :=
    natCast_le_two_pow_localSparsityFactor hk
  have hsmallpow : ((9 : ℝ) / 200) ^ (s - 1) ≤
      ((9 : ℝ) / 200) ^ 4 := by
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) ht4
  calc
    4500 * (k : ℝ) * ((9 : ℝ) / 400) ^ (s - 1) ≤
        4500 * (2 : ℝ) ^ s * ((9 : ℝ) / 400) ^ (s - 1) := by
      gcongr
    _ = 9000 * ((9 : ℝ) / 200) ^ (s - 1) := by
      rw [show s = (s - 1) + 1 by omega, pow_succ]
      have hsub : s - 1 + 1 - 1 = s - 1 := by omega
      rw [hsub]
      calc
        4500 * (2 ^ (s - 1) * 2) * (9 / 400) ^ (s - 1) =
            9000 * (2 ^ (s - 1) * (9 / 400) ^ (s - 1)) := by ring
        _ = 9000 * ((2 : ℝ) * (9 / 400)) ^ (s - 1) := by
          rw [mul_pow]
        _ = 9000 * (9 / 200) ^ (s - 1) := by norm_num
    _ ≤ 9000 * ((9 : ℝ) / 200) ^ 4 := by gcongr
    _ < 1 / 4 := by norm_num

/-- For each `1 ≤ u ≤ 3n`, the exact fixed-size union-bound term is
strictly smaller than `4⁻ᵘ`.  This is the numerical heart of Lemma 2.1(2). -/
theorem integerLocalFailureTerm_lt_fourInvPow
    {k n u : ℕ} (hk : 2 ≤ k)
    (hn : 100 * Real.log (k : ℝ) ≤ n)
    (hu : 1 ≤ u) (hu3n : u ≤ 3 * n) :
    ((2 * hostPartSize k n).choose u : ℝ) *
        (((u ^ 2 / 4).choose (integerLocalFailureThreshold k u) : ℝ) *
          (hostProbabilityUnit k n hk hn : ℝ) ^
            (integerLocalFailureThreshold k u)) <
      ((1 : ℝ) / 4) ^ u := by
  let s := localSparsityFactor k
  let m := s * u + 1
  let r : ℝ := 3 * (u : ℝ) / (400 * n)
  have hnR : (0 : ℝ) < n := by
    have hlog := log_natCast_pos hk
    nlinarith
  have huR : (0 : ℝ) < u := by exact_mod_cast (show 0 < u by omega)
  have hs70 : 70 ≤ s := seventy_le_localSparsityFactor hk
  have hspos : 0 < s := by omega
  have hmpos : 0 < m := by simp [m]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hsceil : 100 * Real.log (k : ℝ) ≤ (s : ℝ) := by
    dsimp only [s, localSparsityFactor]
    exact Nat.le_ceil _
  have hmlower :
      100 * Real.log (k : ℝ) * (u : ℝ) ≤ (m : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hsceil (Nat.cast_nonneg u)
    dsimp only [m]
    norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hmul ⊢
    nlinarith
  have hr0 : 0 ≤ r := by
    dsimp only [r]
    positivity
  have hrle : r ≤ (9 : ℝ) / 400 := by
    dsimp only [r]
    rw [div_le_iff₀ (mul_pos (by norm_num) hnR)]
    have hu3nR : (u : ℝ) ≤ 3 * n := by exact_mod_cast hu3n
    nlinarith
  have hrone : r ≤ 1 := hrle.trans (by norm_num)
  have hbase :
      (3 * (u : ℝ) ^ 2 * (hostProbabilityUnit k n hk hn : ℝ)) /
          (4 * (m : ℝ)) ≤ r := by
    have hratio :
        (100 * (u : ℝ) * Real.log (k : ℝ)) / (m : ℝ) ≤ 1 := by
      rw [div_le_one hmR]
      nlinarith
    have hid :
        (3 * (u : ℝ) ^ 2 * (hostProbabilityUnit k n hk hn : ℝ)) /
            (4 * (m : ℝ)) =
          r * ((100 * (u : ℝ) * Real.log (k : ℝ)) / (m : ℝ)) := by
      rw [coe_hostProbabilityUnit, hostProbability]
      dsimp only [r]
      field_simp
      ring
    rw [hid]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hratio hr0
  have hA0 : (0 : ℝ) ≤ (6 * (hostPartSize k n : ℝ)) / u := by positivity
  have hinner :
      (6 * (hostPartSize k n : ℝ)) / u * r ^ s < (1 : ℝ) / 4 := by
    have hrpow : r ^ (s - 1) ≤ ((9 : ℝ) / 400) ^ (s - 1) :=
      pow_le_pow_left₀ hr0 hrle _
    have hid :
        (6 * (hostPartSize k n : ℝ)) / u * r ^ s =
          4500 * (k : ℝ) * r ^ (s - 1) := by
      rw [← pow_sub_one_mul (show s ≠ 0 by omega) r]
      simp only [hostPartSize, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      dsimp only [r]
      field_simp
      ring
    rw [hid]
    exact (mul_le_mul_of_nonneg_left hrpow (by positivity)).trans_lt
      (localSparsityNumericalBase_lt_quarter hk)
  have hcomb := fixedSizeCombinationTerm_le
    (hostPartSize k n) u m (hostProbabilityUnit k n hk hn) hu
      (show 1 ≤ m by omega)
  change
    ((2 * hostPartSize k n).choose u : ℝ) *
        (((u ^ 2 / 4).choose m : ℝ) *
          (hostProbabilityUnit k n hk hn : ℝ) ^ m) <
      ((1 : ℝ) / 4) ^ u
  have hfixedBase0 :
      0 ≤ (3 * (u : ℝ) ^ 2 * (hostProbabilityUnit k n hk hn : ℝ)) /
        (4 * (m : ℝ)) := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg (u : ℝ)))
        (hostProbabilityUnit k n hk hn).property.1)
      (mul_nonneg (by norm_num) (Nat.cast_nonneg m))
  calc
    ((2 * hostPartSize k n).choose u : ℝ) *
        (((u ^ 2 / 4).choose m : ℝ) *
          (hostProbabilityUnit k n hk hn : ℝ) ^ m) ≤
      ((6 * (hostPartSize k n : ℝ)) / u) ^ u *
        ((3 * (u : ℝ) ^ 2 * (hostProbabilityUnit k n hk hn : ℝ)) /
          (4 * m)) ^ m := hcomb
    _ ≤ ((6 * (hostPartSize k n : ℝ)) / u) ^ u * r ^ m := by
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hfixedBase0 hbase m)
        (pow_nonneg hA0 u)
    _ ≤ ((6 * (hostPartSize k n : ℝ)) / u) ^ u * r ^ (s * u) := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one hr0 hrone (show s * u ≤ m by simp [m]))
        (pow_nonneg hA0 u)
    _ = (((6 * (hostPartSize k n : ℝ)) / u) * r ^ s) ^ u := by
      rw [pow_mul, mul_pow]
    _ < ((1 : ℝ) / 4) ^ u :=
      pow_lt_pow_left₀ hinner (mul_nonneg hA0 (pow_nonneg hr0 s))
        (show u ≠ 0 by omega)

/-- Failure of the paper's local sparsity condition for at least one set of
size between `1` and `vertexBound`. -/
def badLocalSparsityEvent (M k vertexBound : ℕ) :
    Set (Set (BalancedBipartiteEdgeIndex M)) :=
  {E | ∃ u ∈ Finset.Icc 1 vertexBound,
    E ∈ badSpannedEventAtSize M u (localFailureThreshold k u)}

/-- Direct all-size union bound.  The remaining numerical work in Lemma 2.1
is precisely to bound each summand by `4⁻ᵘ`. -/
theorem measureReal_badLocalSparsityEvent_le (M k vertexBound : ℕ) (p : I) :
    (bipartiteEdgeMeasure M p).real
        (badLocalSparsityEvent M k vertexBound) ≤
      ∑ u ∈ Finset.Icc 1 vertexBound,
        ((2 * M).choose u : ℝ) *
          (((u ^ 2 / 4).choose (localFailureThreshold k u) : ℝ) *
            (p : ℝ) ^ (localFailureThreshold k u)) := by
  let event : ℕ → Set (Set (BalancedBipartiteEdgeIndex M)) := fun u =>
    badSpannedEventAtSize M u (localFailureThreshold k u)
  have hunion :
      (bipartiteEdgeMeasure M p).real
          (badLocalSparsityEvent M k vertexBound) ≤
      ∑ u ∈ Finset.Icc 1 vertexBound,
        (bipartiteEdgeMeasure M p).real (event u) := by
    simpa only [badLocalSparsityEvent, Set.mem_setOf_eq, event] using
      (measureReal_exists_mem_finset_le
        (bipartiteEdgeMeasure M p) (Finset.Icc 1 vertexBound) event)
  have hsum :
      (∑ u ∈ Finset.Icc 1 vertexBound,
        (bipartiteEdgeMeasure M p).real (event u)) ≤
      ∑ u ∈ Finset.Icc 1 vertexBound,
        ((2 * M).choose u : ℝ) *
          (((u ^ 2 / 4).choose (localFailureThreshold k u) : ℝ) *
            (p : ℝ) ^ (localFailureThreshold k u)) := by
    exact Finset.sum_le_sum fun u _ =>
      measureReal_badSpannedEventAtSize_le
        M u (localFailureThreshold k u) p
  exact le_trans hunion hsum

/-- Avoiding every bad threshold event implies the exact integer local
sparsity predicate consumed by `HostExpansion`. -/
theorem isLocallySparse_bipartiteHost_of_not_mem_bad
    {M k vertexBound : ℕ} {E : Set (BalancedBipartiteEdgeIndex M)}
    (hgood : E ∉ badLocalSparsityEvent M k vertexBound) :
    IsLocallySparse (bipartiteHost E) vertexBound
      (localSparsityFactor k) := by
  intro U hU
  by_cases hU0 : U = ∅
  · subst U
    simp only [Finset.coe_empty, spannedEdgeCount_empty, Finset.card_empty, mul_zero]
    exact le_rfl
  · have hUpos : 1 ≤ #U := (Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hU0))
    have hsize : #U ∈ Finset.Icc 1 vertexBound := Finset.mem_Icc.mpr ⟨hUpos, hU⟩
    have hnot : E ∉ badSpannedEventAtSize M #U
        (localFailureThreshold k #U) := by
      intro hbad
      exact hgood ⟨#U, hsize, hbad⟩
    have hthreshold : spannedEdgeCount (bipartiteHost E)
        (U : Set (BalancedBipartiteVertex M)) <
          localFailureThreshold k #U := by
      apply Nat.lt_of_not_ge
      intro hge
      apply hnot
      exact ⟨U, Finset.mem_powersetCard.mpr ⟨by simp, rfl⟩, hge⟩
    exact (Nat.le_of_lt hthreshold).trans (localFailureThreshold_le k #U)

/-- Failure of integer local sparsity for one of the prescribed set sizes. -/
def badIntegerLocalSparsityEvent (M k vertexBound : ℕ) :
    Set (Set (BalancedBipartiteEdgeIndex M)) :=
  {E | ∃ u ∈ Finset.Icc 1 vertexBound,
    E ∈ badSpannedEventAtSize M u (integerLocalFailureThreshold k u)}

theorem measureReal_badIntegerLocalSparsityEvent_le
    (M k vertexBound : ℕ) (p : I) :
    (bipartiteEdgeMeasure M p).real
        (badIntegerLocalSparsityEvent M k vertexBound) ≤
      ∑ u ∈ Finset.Icc 1 vertexBound,
        ((2 * M).choose u : ℝ) *
          (((u ^ 2 / 4).choose (integerLocalFailureThreshold k u) : ℝ) *
            (p : ℝ) ^ (integerLocalFailureThreshold k u)) := by
  let event : ℕ → Set (Set (BalancedBipartiteEdgeIndex M)) := fun u =>
    badSpannedEventAtSize M u (integerLocalFailureThreshold k u)
  have hunion :
      (bipartiteEdgeMeasure M p).real
          (badIntegerLocalSparsityEvent M k vertexBound) ≤
        ∑ u ∈ Finset.Icc 1 vertexBound,
          (bipartiteEdgeMeasure M p).real (event u) := by
    simpa only [badIntegerLocalSparsityEvent, Set.mem_setOf_eq, event] using
      (measureReal_exists_mem_finset_le
        (bipartiteEdgeMeasure M p) (Finset.Icc 1 vertexBound) event)
  have hsum :
      (∑ u ∈ Finset.Icc 1 vertexBound,
        (bipartiteEdgeMeasure M p).real (event u)) ≤
      ∑ u ∈ Finset.Icc 1 vertexBound,
        ((2 * M).choose u : ℝ) *
          (((u ^ 2 / 4).choose (integerLocalFailureThreshold k u) : ℝ) *
            (p : ℝ) ^ (integerLocalFailureThreshold k u)) := by
    exact Finset.sum_le_sum fun u _ =>
      measureReal_badSpannedEventAtSize_le
        M u (integerLocalFailureThreshold k u) p
  exact le_trans hunion hsum

theorem isLocallySparse_bipartiteHost_of_not_mem_badInteger
    {M k vertexBound : ℕ} {E : Set (BalancedBipartiteEdgeIndex M)}
    (hgood : E ∉ badIntegerLocalSparsityEvent M k vertexBound) :
    IsLocallySparse (bipartiteHost E) vertexBound
      (localSparsityFactor k) := by
  intro U hU
  by_cases hU0 : U = ∅
  · subst U
    simp only [Finset.coe_empty, spannedEdgeCount_empty, Finset.card_empty, mul_zero]
    exact le_rfl
  · have hUpos : 1 ≤ #U :=
      Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hU0)
    have hsize : #U ∈ Finset.Icc 1 vertexBound :=
      Finset.mem_Icc.mpr ⟨hUpos, hU⟩
    have hnot : E ∉ badSpannedEventAtSize M #U
        (integerLocalFailureThreshold k #U) := by
      intro hbad
      exact hgood ⟨#U, hsize, hbad⟩
    have hthreshold : spannedEdgeCount (bipartiteHost E)
        (U : Set (BalancedBipartiteVertex M)) <
          integerLocalFailureThreshold k #U := by
      apply Nat.lt_of_not_ge
      intro hge
      apply hnot
      exact ⟨U, Finset.mem_powersetCard.mpr ⟨by simp, rfl⟩, hge⟩
    rw [integerLocalFailureThreshold] at hthreshold
    omega

/-- Finite initial segments of `∑_{u≥1} 4⁻ᵘ` are strictly below `1/3`. -/
theorem sum_fourInvPow_Icc_lt_third (N : ℕ) :
    (∑ u ∈ Finset.Icc 1 N, ((1 : ℝ) / 4) ^ u) < 1 / 3 := by
  rw [← Finset.Ico_add_one_right_eq_Icc]
  rw [geom_sum_Ico' (by norm_num) (by omega : 1 ≤ N + 1)]
  have hpow : 0 < ((1 : ℝ) / 4) ^ (N + 1) := pow_pos (by norm_num) _
  norm_num only [pow_one]
  nlinarith

/-- Lemma 2.1(2), in the integer form consumed downstream: the probability
that some set of at most `3n` violates local sparsity is less than `1/3`. -/
theorem measureReal_badIntegerLocalSparsityEvent_lt_third
    {k n : ℕ} (hk : 2 ≤ k)
    (hn : 100 * Real.log (k : ℝ) ≤ n) :
    (bipartiteEdgeMeasure (hostPartSize k n)
        (hostProbabilityUnit k n hk hn)).real
      (badIntegerLocalSparsityEvent (hostPartSize k n) k (3 * n)) < 1 / 3 := by
  let p := hostProbabilityUnit k n hk hn
  let M := hostPartSize k n
  have hnpos : 0 < n := by
    have hlog := log_natCast_pos hk
    have hnR : (0 : ℝ) < n := by nlinarith
    exact_mod_cast hnR
  have hsnonempty : (Finset.Icc 1 (3 * n)).Nonempty := by
    refine ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, ?_⟩⟩
    omega
  have hmeasure := measureReal_badIntegerLocalSparsityEvent_le
    M k (3 * n) p
  have hsum :
      (∑ u ∈ Finset.Icc 1 (3 * n),
        ((2 * M).choose u : ℝ) *
          (((u ^ 2 / 4).choose (integerLocalFailureThreshold k u) : ℝ) *
            (p : ℝ) ^ (integerLocalFailureThreshold k u))) <
        ∑ u ∈ Finset.Icc 1 (3 * n), ((1 : ℝ) / 4) ^ u := by
    apply Finset.sum_lt_sum_of_nonempty hsnonempty
    intro u hu
    have hurange := Finset.mem_Icc.mp hu
    simpa only [M, p] using
      integerLocalFailureTerm_lt_fourInvPow hk hn hurange.1 hurange.2
  exact hmeasure.trans_lt (hsum.trans (sum_fourInvPow_Icc_lt_third (3 * n)))

/-- The two good host events occur simultaneously. -/
theorem exists_edgeSet_not_bad_hostEvents
    {k n : ℕ} (hk : 2 ≤ k)
    (hn : 100 * Real.log (k : ℝ) ≤ n) :
    ∃ E : Set (BalancedBipartiteEdgeIndex (hostPartSize k n)),
      E ∉ badEdgeCountEvent (hostPartSize k n)
          (hostProbabilityUnit k n hk hn) ∧
      E ∉ badIntegerLocalSparsityEvent (hostPartSize k n) k (3 * n) := by
  let M := hostPartSize k n
  let p := hostProbabilityUnit k n hk hn
  let edgeBad := badEdgeCountEvent M p
  let localBad := badIntegerLocalSparsityEvent M k (3 * n)
  have hedge : (bipartiteEdgeMeasure M p).real edgeBad < 1 / 3 := by
    exact measureReal_badEdgeCountEvent_lt_third M p
      (hundred_le_bipartiteHostMean_hostParameters hk hn)
  have hlocal : (bipartiteEdgeMeasure M p).real localBad < 1 / 3 := by
    exact measureReal_badIntegerLocalSparsityEvent_lt_third hk hn
  have hunion : (bipartiteEdgeMeasure M p).real (edgeBad ∪ localBad) < 1 := by
    calc
      (bipartiteEdgeMeasure M p).real (edgeBad ∪ localBad) ≤
          (bipartiteEdgeMeasure M p).real edgeBad +
            (bipartiteEdgeMeasure M p).real localBad := measureReal_union_le _ _
      _ < 1 / 3 + 1 / 3 := add_lt_add hedge hlocal
      _ < 1 := by norm_num
  have hne : edgeBad ∪ localBad ≠ Set.univ := by
    intro heq
    rw [heq] at hunion
    simp at hunion
  obtain ⟨E, hE⟩ := (Set.ne_univ_iff_exists_notMem (edgeBad ∪ localBad)).mp hne
  refine ⟨E, ?_, ?_⟩
  · intro hbad
    exact hE (Or.inl hbad)
  · intro hbad
    exact hE (Or.inr hbad)

/-- Final random-host interface for Lemma 2.1(1)--(2).  The vertex type
itself records two classes of size `M = 10⁵kn`; all numerical rounding is
explicit, and the local factor is immediately compatible with
`six_mul_localSparsityFactor_lt_localDegreeThreshold`. -/
theorem exists_bipartiteHost_edgeBounds_isLocallySparse
    {k n : ℕ} (hk : 2 ≤ k)
    (hn : 100 * Real.log (k : ℝ) ≤ n) :
    ∃ Γ : SimpleGraph (BalancedBipartiteVertex (hostPartSize k n)),
      Γ.IsBipartite ∧
      hostProbability k n * (hostPartSize k n : ℝ) ^ 2 / 2 ≤
        edgeCount Γ ∧
      (edgeCount Γ : ℝ) ≤
        2 * hostProbability k n * (hostPartSize k n : ℝ) ^ 2 ∧
      IsLocallySparse Γ (3 * n) (localSparsityFactor k) := by
  obtain ⟨E, hedgeGood, hlocalGood⟩ :=
    exists_edgeSet_not_bad_hostEvents hk hn
  let p := hostProbabilityUnit k n hk hn
  let M := hostPartSize k n
  have hmean : bipartiteHostMean M p =
      hostProbability k n * (hostPartSize k n : ℝ) ^ 2 := by
    exact bipartiteHostMean_hostParameters k n hk hn
  have hedgeNot :
      ¬ ((edgeCount (bipartiteHost E) : ℝ) ≤ bipartiteHostMean M p / 2) ∧
      ¬ (2 * bipartiteHostMean M p ≤ edgeCount (bipartiteHost E)) := by
    exact not_or.mp hedgeGood
  refine ⟨bipartiteHost E, bipartiteHost_isBipartite E, ?_, ?_, ?_⟩
  · rw [← hmean]
    exact (lt_of_not_ge hedgeNot.1).le
  · calc
      (edgeCount (bipartiteHost E) : ℝ) ≤ 2 * bipartiteHostMean M p :=
        (lt_of_not_ge hedgeNot.2).le
      _ = 2 * hostProbability k n * (hostPartSize k n : ℝ) ^ 2 := by
        rw [hmean]
        ring
  · exact isLocallySparse_bipartiteHost_of_not_mem_badInteger hlocalGood

end

end LeanCo.SizeRamsey
