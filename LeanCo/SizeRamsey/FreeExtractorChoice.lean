import LeanCo.SizeRamsey.FreeExtractionIteration
import LeanCo.SizeRamsey.Defs

/-!
# Total choice function for conditional free-subgraph extraction

The Key Lemma only supplies a useful subgraph when the current residual is
admissible.  Iteration is cleaner with a total function on graphs.  We choose
the promised subgraph on admissible inputs and the empty graph otherwise,
and expose the three properties consumed by `FreeExtractionIteration`.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open SimpleGraph

noncomputable section

universe u w

variable {V : Type u} {W : Type w}

/-- Totalise a conditional subgraph extractor by returning the empty graph
outside the admissible region. -/
def conditionalFreeExtractor
    (F : SimpleGraph W) (Good : SimpleGraph V → Prop)
    (gain : SimpleGraph V → SimpleGraph V → Prop)
    (hextract : ∀ R, Good R → ∃ H : SimpleGraph V,
      H ≤ R ∧ F.Free H ∧ gain R H) :
    SimpleGraph V → SimpleGraph V := by
  classical
  exact fun R =>
    if h : Good R then Classical.choose (hextract R h) else ⊥

theorem conditionalFreeExtractor_spec_of_good
    (F : SimpleGraph W) (Good : SimpleGraph V → Prop)
    (gain : SimpleGraph V → SimpleGraph V → Prop)
    (hextract : ∀ R, Good R → ∃ H : SimpleGraph V,
      H ≤ R ∧ F.Free H ∧ gain R H)
    {R : SimpleGraph V} (hR : Good R) :
    conditionalFreeExtractor F Good gain hextract R ≤ R ∧
      F.Free (conditionalFreeExtractor F Good gain hextract R) ∧
      gain R (conditionalFreeExtractor F Good gain hextract R) := by
  classical
  rw [conditionalFreeExtractor, dif_pos hR]
  exact Classical.choose_spec (hextract R hR)

/-- The totalised extractor always returns a subgraph of its input. -/
theorem conditionalFreeExtractor_le
    (F : SimpleGraph W) (Good : SimpleGraph V → Prop)
    (gain : SimpleGraph V → SimpleGraph V → Prop)
    (hextract : ∀ R, Good R → ∃ H : SimpleGraph V,
      H ≤ R ∧ F.Free H ∧ gain R H) :
    ∀ R, conditionalFreeExtractor F Good gain hextract R ≤ R := by
  classical
  intro R
  by_cases hR : Good R
  · exact (conditionalFreeExtractor_spec_of_good
      F Good gain hextract hR).1
  · rw [conditionalFreeExtractor, dif_neg hR]
    exact bot_le

/-- If the empty graph is `F`-free, every value of the totalised extractor
is `F`-free. -/
theorem conditionalFreeExtractor_free
    (F : SimpleGraph W) (Good : SimpleGraph V → Prop)
    (gain : SimpleGraph V → SimpleGraph V → Prop)
    (hextract : ∀ R, Good R → ∃ H : SimpleGraph V,
      H ≤ R ∧ F.Free H ∧ gain R H)
    (hbot : F.Free (⊥ : SimpleGraph V)) :
    ∀ R, F.Free (conditionalFreeExtractor F Good gain hextract R) := by
  classical
  intro R
  by_cases hR : Good R
  · exact (conditionalFreeExtractor_spec_of_good
      F Good gain hextract hR).2.1
  · simpa only [conditionalFreeExtractor, dif_neg hR] using hbot

/-- The advertised gain holds whenever the current graph is admissible. -/
theorem conditionalFreeExtractor_gain
    (F : SimpleGraph W) (Good : SimpleGraph V → Prop)
    (gain : SimpleGraph V → SimpleGraph V → Prop)
    (hextract : ∀ R, Good R → ∃ H : SimpleGraph V,
      H ≤ R ∧ F.Free H ∧ gain R H) :
    ∀ R, Good R →
      gain R (conditionalFreeExtractor F Good gain hextract R) := by
  intro R hR
  exact (conditionalFreeExtractor_spec_of_good
    F Good gain hextract hR).2.2

/-- Existential package convenient for callers that do not want to unfold
the choice function. -/
theorem exists_total_conditionalFreeExtractor
    (F : SimpleGraph W) (Good : SimpleGraph V → Prop)
    (gain : SimpleGraph V → SimpleGraph V → Prop)
    (hextract : ∀ R, Good R → ∃ H : SimpleGraph V,
      H ≤ R ∧ F.Free H ∧ gain R H)
    (hbot : F.Free (⊥ : SimpleGraph V)) :
    ∃ pick : SimpleGraph V → SimpleGraph V,
      (∀ R, pick R ≤ R) ∧
      (∀ R, F.Free (pick R)) ∧
      (∀ R, Good R → gain R (pick R)) := by
  let pick := conditionalFreeExtractor F Good gain hextract
  exact ⟨pick,
    conditionalFreeExtractor_le F Good gain hextract,
    conditionalFreeExtractor_free F Good gain hextract hbot,
    conditionalFreeExtractor_gain F Good gain hextract⟩

end

end LeanCo.SizeRamsey
