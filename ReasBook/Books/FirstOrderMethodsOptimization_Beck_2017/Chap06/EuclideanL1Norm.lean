import Mathlib

noncomputable section

open WithLp (toLp)
open scoped BigOperators

section

variable {ι : Type*} [Fintype ι]

local notation "E" => EuclideanSpace ℝ ι

namespace EuclideanSpace

/-- The Euclidean `ℓ¹` norm on a finite product, specializing to `ℝ^n` when `ι = Fin n`. -/
abbrev l1Norm (x : E) : ℝ :=
  ‖toLp 1 fun i ↦ x i‖

/-- The Euclidean `ℓ¹` norm is the finite sum of the coordinate absolute values. -/
@[simp] theorem l1Norm_eq_sum_abs (x : E) :
    l1Norm x = ∑ i, |x i| := by
  rw [l1Norm, PiLp.norm_eq_sum]
  · simp
  · norm_num

end EuclideanSpace

/-- Textbook notation for the Euclidean `ℓ¹` norm on a finite product. -/
notation "‖" x "‖₁" => EuclideanSpace.l1Norm x

end
