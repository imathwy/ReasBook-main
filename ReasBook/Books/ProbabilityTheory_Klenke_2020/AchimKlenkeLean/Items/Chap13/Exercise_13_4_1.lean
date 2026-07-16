import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap13.Definition_13_26

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set

open scoped ENNReal

universe u

namespace MeasureTheory

section

variable {E : Type u} [MeasurableSpace E] [TopologicalSpace E] [PolishSpace E] [BorelSpace E]

/- Layer triage for Exercise 13.4.1.
- `source-facing`: a tightness criterion for families of probability measures on
  `ProbabilityMeasure E`, phrased using small escape-mass events in the base space `E`.
- `core/canonical`: `IsTightMeasureSet` on measures over `ProbabilityMeasure E`.
- `bridge/view`: the chapter owner bridge
  `FiniteMeasure.tight_family_iff_forall_exists_isCompact_measure_compl_lt`, applied on the
  ambient space `ProbabilityMeasure E`, together with the canonical Prokhorov compactness API for
  compact families of probability measures on `E`.
-/

-- Proof sketch: first use the owner bridge
-- `FiniteMeasure.tight_family_iff_forall_exists_isCompact_measure_compl_lt` on the ambient space
-- `ProbabilityMeasure E` to reduce meta-tightness to compact control by subsets of
-- `ProbabilityMeasure E`. For the forward implication, apply this to a compact family of
-- probability measures on `E`, then use Prokhorov tightness on `E` to obtain one compact
-- `K ⊆ E` controlling the escape mass of every measure in the compact family. For the reverse
-- implication, choose compact sets in `E` for a summable sequence of tolerances, replace them by
-- finite unions to get a monotone compact sequence, and apply the Prokhorov compactness theorem
-- to the set of probability measures whose masses outside these compacts are uniformly small.
/-- Exercise 13.4.1: a family of probability measures on `ProbabilityMeasure E` is tight if and
only if, for every `ε > 0`, there is a compact set `K ⊆ E` such that every meta-measure in the
family gives mass `< ε` to the set of probability measures assigning mass `> ε` to `Kᶜ`. -/
theorem tight_probabilityMeasureFamily_iff_forall_exists_isCompact_small_escape
    (𝒦 : Set (ProbabilityMeasure (ProbabilityMeasure E))) :
    IsTightMeasureSet (ProbabilityMeasure.toMeasure '' 𝒦) ↔
      ∀ ε : ℝ, 0 < ε → ∃ K : Set E, IsCompact K ∧
        ∀ μbar ∈ 𝒦,
          μbar {μ : ProbabilityMeasure E | ENNReal.ofReal ε < μ Kᶜ} < ENNReal.ofReal ε := sorry

end

end MeasureTheory
