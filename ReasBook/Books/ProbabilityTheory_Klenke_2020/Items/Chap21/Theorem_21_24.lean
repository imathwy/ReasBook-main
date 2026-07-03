import Mathlib
import AchimKlenkeLean.Items.Chap21.Definition_21_1
import AchimKlenkeLean.Items.Chap21.Definition_21_21
import AchimKlenkeLean.Items.Chap21.Definition_21_22

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory Set
open MeasureTheory.Filtration
open scoped Topology ProbabilityTheory

universe u

namespace ProbabilityTheory

variable {Ω : Type u}
variable {X : NNReal → Ω → ℝ}

variable [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {ℱ : Filtration NNReal mΩ}
variable [UsualConditions ℱ μ]

-- Proof sketch: apply Doob's upcrossing inequality on the rational times to obtain, outside a
-- measurable null set, finite upcrossings and bounded rational-time oscillation on each compact
-- interval. These yield right limits along `ℚ≥0` and hence a càdlàg regularization. Completeness
-- and right continuity of the filtration make the regularized process adapted, and the right
-- continuity of `t ↦ μ[X t]` upgrades the supermartingale inequalities to show that the
-- regularization is a modification of `X`.
/-- Theorem 21.24: Doob's regularization theorem. A supermartingale on a filtration satisfying the
usual conditions whose expectation function `t ↦ μ[X t]` is right continuous admits a
modification with càdlàg paths. -/
theorem exists_modification_with_cadlag_paths_of_supermartingale
    (hX : Supermartingale X ℱ μ)
    (hEX_rc :
      ∀ t : NNReal, ContinuousWithinAt (fun s : NNReal ↦ μ[X s]) (Set.Ici t) t) :
    ∃ Xtilde : NNReal → Ω → ℝ,
      AreModifications μ X Xtilde ∧ HasCadlagPaths Xtilde := sorry

end ProbabilityTheory
