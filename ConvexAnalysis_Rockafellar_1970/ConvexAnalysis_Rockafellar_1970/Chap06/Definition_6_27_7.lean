import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.ParaboloidEpigraph
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section LEPseudoMetric

universe u

variable {𝕜 : Type u} [LE 𝕜] [Pow 𝕜 ℕ] [PseudoMetricSpace (𝕜 × 𝕜)]

open scoped Rockafellar

local notation "R2" => (𝕜 × 𝕜)
local notation "P" => (paraboloidEpigraph : Set R2)

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.27.7 introduces the function `f₀`, the squared metric
distance to the Section 27 parabola set `P`.
- `core/canonical`: the ambient owners are the shared paraboloid-set owner
  `paraboloidEpigraph : Set (𝕜 × 𝕜)` and the Chapter 1 point-to-set distance owner
  `d(x, C) = Metric.infEDist x C`; the real-valued `Metric.infDist` formula is a bridge view.
- Primitive data vs derived API: the primitive source data are the point `x` and the fixed
source-facing set `paraboloidEpigraph`.

Domain-style sampling used here:
- `d(x, C)` / `Metric.infEDist`;
- `distanceToSet_toReal_eq_infDist`;
- the source-facing set `paraboloidEpigraph` from `Chap02/ParaboloidEpigraph`.

Layer target: `source-facing`, defined from the canonical point-to-set distance owner and then
read on the finite real branch.
-/

/-- Definition 6.27.7: the squared metric distance from `x` to the parabola set `P`
in `𝕜 × 𝕜`. -/
def parabolicF0 (x : R2) : ℝ :=
  (d(x, P)).toReal ^ 2

local notation "f₀" => parabolicF0

/-- The source-facing branch `f₀` is exactly squared `Metric.infDist` on the source set `P`. -/
@[simp] theorem parabolicF0_eq_infDist_sq (x : R2) :
    f₀ x = Metric.infDist x P ^ 2 :=
  by
    simp [parabolicF0, distanceToSet_toReal_eq_infDist]

end LEPseudoMetric
