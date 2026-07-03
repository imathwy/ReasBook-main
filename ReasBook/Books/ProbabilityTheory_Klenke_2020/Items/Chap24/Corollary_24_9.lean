import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u u' v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {Ω' : Type u'} [MeasurableSpace Ω']
variable {E : Type v} [MeasurableSpace E] [TopologicalSpace E] [Bornology E]

/-- Independent increments for a random measure mean that evaluations on every finite family of
pairwise disjoint bounded measurable sets are independent random variables. -/
def HasIndependentIncrements (P : ProbabilityMeasure Ω) (X : Ω → Measure E) : Prop :=
  ∀ n, ∀ A : Fin n → Set E,
    (∀ i, MeasurableSet (A i)) →
    (∀ i, Bornology.IsBounded (A i)) →
    Pairwise (fun i j ↦ Disjoint (A i) (A j)) →
    iIndepFun (fun i ω ↦ X ω (A i)) (P : Measure Ω)

-- Proof sketch: this is the defining elimination rule for `HasIndependentIncrements`; unfold the
-- definition and apply the resulting hypothesis to the given family of sets.
/-- Evaluating a random measure with independent increments on a finite family of pairwise disjoint
bounded measurable sets yields an independent family. -/
theorem HasIndependentIncrements.iIndepFun_eval
    {P : ProbabilityMeasure Ω} {X : Ω → Measure E} (hX : HasIndependentIncrements P X)
    {ι : Type*} [Finite ι] (A : ι → Set E)
    (hA_meas : ∀ i, MeasurableSet (A i)) (hA_bdd : ∀ i, Bornology.IsBounded (A i))
    (hA_disjoint : (Set.univ : Set ι).PairwiseDisjoint A) :
    iIndepFun (fun i ω ↦ X ω (A i)) (P : Measure Ω) := sorry

-- Proof sketch: apply the uniqueness theorem for independently scattered random measures from the
-- preceding development: finite-dimensional laws of the evaluations on pairwise disjoint bounded
-- measurable sets are products of the one-dimensional marginals, so equality of all marginals
-- forces equality of the law of the measure-valued random variable.
/-- Corollary 24.9: the distribution of a random measure with independent increments is uniquely
determined by the laws of the evaluations `X(A)` on bounded measurable sets `A`. -/
theorem identDistrib_of_bounded_eval_identDistrib_of_independentIncrements
    {P : ProbabilityMeasure Ω} {Q : ProbabilityMeasure Ω'} {X : Ω → Measure E}
    {Y : Ω' → Measure E} (hX_meas : Measurable X) (hY_meas : Measurable Y)
    (hX_locallyFinite : ∀ᵐ ω ∂(P : Measure Ω), IsLocallyFiniteMeasure (X ω))
    (hY_locallyFinite : ∀ᵐ ω ∂(Q : Measure Ω'), IsLocallyFiniteMeasure (Y ω))
    (hX_indep : HasIndependentIncrements P X) (hY_indep : HasIndependentIncrements Q Y)
    (h_eval :
      ∀ A : Set E, MeasurableSet A → Bornology.IsBounded A →
        IdentDistrib (fun ω ↦ X ω A) (fun ω ↦ Y ω A) (P : Measure Ω) (Q : Measure Ω')) :
    IdentDistrib X Y (P : Measure Ω) (Q : Measure Ω') := sorry

end ProbabilityTheory
