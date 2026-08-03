module

public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.Equiv

public section

namespace EuclideanPlane

/-- The standard coordinate homeomorphism from the Euclidean plane to `ℝ × ℝ`. -/
noncomputable def productHomeomorph : EuclideanSpace ℝ (Fin 2) ≃ₜ ℝ × ℝ :=
  ((EuclideanSpace.equiv (Fin 2) ℝ).trans
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)).toHomeomorph

@[simp] theorem productHomeomorph_apply (x : EuclideanSpace ℝ (Fin 2)) :
    productHomeomorph x = (x 0, x 1) := by
  rfl

@[simp] theorem productHomeomorph_symm_apply (x : ℝ × ℝ) :
    productHomeomorph.symm x = !₂[x.1, x.2] := by
  apply productHomeomorph.injective
  simp

end EuclideanPlane
