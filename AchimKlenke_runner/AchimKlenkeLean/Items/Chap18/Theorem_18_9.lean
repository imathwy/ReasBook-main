import AchimKlenkeLean.Items.Chap18.Theorem_18_12
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]

-- Proof sketch: choose a successful Markov coupling `Z` from `HasSuccessfulCoupling p`. For
-- each pair of starting states `x` and `y`, apply Lemma 17.45 to the two coordinate realizations
-- given by `IsSuccessfulMarkovCoupling.toIsMarkovCoupling` to obtain martingales
-- `(f ((Z n).1))` and `(f ((Z n).2))`. The initial-state identities come from the underlying
-- `IsMarkovProcessRealization` fields, while the tail-disagreement hypothesis bounds the event
-- `{ω | (Z m ω).1 ≠ (Z m ω).2 for some m ≥ n}` and hence also the time-`n` disagreement event.
-- Boundedness then forces `|f x - f y|` to vanish, so `f` is constant.
/-- Theorem 18.9: if the discrete Markov chain with transition matrix `p` admits a successful
coupling, then every bounded harmonic function for `p` is constant. -/
theorem bounded_harmonicFunction_constant_of_hasSuccessfulCoupling
    {p : E → E → ℝ≥0∞}
    (hcoupling : HasSuccessfulCoupling p)
    {f : E → ℝ} (hf_bdd : Bornology.IsBounded (Set.range f))
    (hf_harmonic : IsHarmonic (discreteMatrixKernel p) f) :
    ∀ x y : E, f x = f y := sorry

end ProbabilityTheory
