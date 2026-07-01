import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u

variable {Ω : Type u} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω] [PolishSpace Ω]

/- Exercise 13.1.3 is source-facing in the measurability/regularity domain. Its core owner
abstraction for clause `(i)` is `AEMeasurable`; bridge facts such as `AEMeasurable.mk`,
`ContinuousOn.aemeasurable`, and the `σ`-finite exhaustion `spanningSets μ` support the proof
strategy without changing the main public statement. -/
/-- Exercise 13.1.3 (Lusin's theorem): for a map `f : Ω → ℝ` on a Polish space with a `σ`-finite
Borel measure `μ`, the following are equivalent: (i) `f` is `μ`-almost everywhere measurable;
(ii) for every `ε > 0` there is a compact set `K` with `μ Kᶜ < ENNReal.ofReal ε` such that `f` is
continuous on `K`. -/
-- Proof sketch: for `(i) → (ii)`, use `AEMeasurable` to choose a measurable representative and
-- apply the finite-measure Lusin/tightness API on the members of a `σ`-finite exhaustion by
-- `spanningSets μ`, patching the exceptional sets so that the total discarded mass is `< ε`. For
-- `(ii) → (i)`, continuity on each compact set gives measurable restrictions, and the hypothesis
-- that the complements have arbitrarily small measure implies that `f` agrees almost everywhere
-- with a Borel measurable map.
theorem aemeasurable_iff_forall_exists_isCompact_continuousOn_compl_lt
    (μ : Measure Ω) [SigmaFinite μ] (f : Ω → ℝ) :
    AEMeasurable f μ ↔
      ∀ ε > 0, ∃ K : Set Ω,
        IsCompact K ∧ μ Kᶜ < ENNReal.ofReal ε ∧ ContinuousOn f K := sorry

omit [TopologicalSpace Ω] [BorelSpace Ω] [PolishSpace Ω] in
/- Almost-everywhere measurability is the canonical owner notion for the existence of a
measurable representative. -/
recall AEMeasurable
