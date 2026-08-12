import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section

universe u v

namespace LinearMap

section

variable {E : Type u} {V : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The canonical operator norm on `E →ₗ[ℝ] V`, induced from the associated continuous linear map
when the domain `E` is finite-dimensional. -/
instance instNormFiniteDimensional : Norm (E →ₗ[ℝ] V) where
  norm A := ‖A.toContinuousLinearMap‖

/-- On a finite-dimensional real normed space, the norm of a linear map is the operator norm of
its associated continuous linear map. -/
theorem norm_def (A : E →ₗ[ℝ] V) : ‖A‖ = ‖A.toContinuousLinearMap‖ :=
  rfl

@[simp] theorem toContinuousLinearMap_norm (A : E →ₗ[ℝ] V) :
    ‖A.toContinuousLinearMap‖ = ‖A‖ :=
  rfl

end

end LinearMap
