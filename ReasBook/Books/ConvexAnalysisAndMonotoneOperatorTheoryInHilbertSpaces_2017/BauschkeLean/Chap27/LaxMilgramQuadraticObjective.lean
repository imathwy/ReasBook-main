import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace

universe u

noncomputable section

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The quadratic-affine functional attached to a continuous bilinear form `F` and a continuous
linear functional `ℓ`. -/
def laxMilgramQuadraticObjective
    (F : H →L[ℝ] H →L[ℝ] ℝ) (ℓ : H →L[ℝ] ℝ) (x : H) : ℝ :=
  (1 / 2 : ℝ) * F x x - ℓ x
