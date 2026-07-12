import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap13.Definition_13_26

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped ENNReal NNReal Topology

namespace MeasureTheory
namespace FiniteMeasure

/- Layer triage for Exercise 13.3.1.
- `source-facing`: existence of a measurable coercive weight with uniformly bounded integrals.
- `core/canonical`: `MeasureTheory.IsTightMeasureSet`.
- `bridge/view`: `tight_family_iff_forall_exists_isCompact_measure_compl_lt` is the chapter's
  compact-control reformulation of the same owner predicate for finite-measure families.
-/

-- Proof sketch: for the forward implication, extract compact sets with uniformly small complement
-- mass and assemble from them a measurable coercive weight by summing suitably scaled indicators of
-- those compacts. For the reverse implication, use Markov-type estimates on the sublevel sets of
-- the coercive weight to obtain compact sets whose complement mass is uniformly small over the
-- family.
/-
This is a source-facing bridge theorem over the canonical owner abstraction
`MeasureTheory.IsTightMeasureSet`, specialized to families of finite measures on `ℝ`.
-/
/-- Exercise 13.3.1: a family `ℱ` of finite measures on `ℝ` is tight if and only if there exists
a measurable weight `f : ℝ → [0, ∞)` that tends to `∞` along `cocompact ℝ` and whose integrals
are uniformly bounded on `ℱ`. -/
theorem tight_family_iff_exists_measurable_coercive_weight (ℱ : Set (FiniteMeasure ℝ)) :
    IsTightMeasureSet (toMeasure '' ℱ) ↔
      ∃ f : ℝ → ℝ≥0,
        Measurable f ∧
          Tendsto f (cocompact ℝ) atTop ∧
            (⨆ μ ∈ ℱ, ∫⁻ x, ↑(f x) ∂μ) < ∞ := sorry

end FiniteMeasure
end MeasureTheory
