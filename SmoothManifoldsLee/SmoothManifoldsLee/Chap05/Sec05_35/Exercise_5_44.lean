import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import SmoothManifoldsLee.Chap05.Sec05_35.Definition_5_35_extra_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff
open Manifold

noncomputable section

universe uM

section

variable {n : ℕ} [NeZero n]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
variable [IsManifold (𝓡∂ n) ∞ M]

/-- The derivative of a real-valued boundary defining function in the tangent direction `v`,
viewed in the canonical tangent-space model `ℝ`. -/
def boundary_defining_derivative {p : M} (f : M → ℝ) (v : TangentSpace (𝓡∂ n) p) : ℝ :=
  NormedSpace.fromTangentSpace (f p) (mfderiv (𝓡∂ n) 𝓘(ℝ) f p v)

/-- A boundary defining function at a boundary point vanishes exactly on the local boundary,
is positive on the local interior, and is smooth at the chosen point. -/
def IsBoundaryDefiningFunctionAt (p : M) (f : M → ℝ) : Prop :=
  p ∈ (𝓡∂ n).boundary M ∧
    ContMDiffAt (𝓡∂ n) 𝓘(ℝ) ∞ f p ∧
    ∃ s : Set M, IsOpen s ∧ p ∈ s ∧
      (∀ x ∈ s, x ∈ (𝓡∂ n).boundary M ↔ f x = 0) ∧
      ∀ x ∈ s, x ∈ (𝓡∂ n).interior M ↔ 0 < f x

local notation "BoundaryDefiningAt" => @IsBoundaryDefiningFunctionAt n _ M _ _

/-- A boundary defining function vanishes at the boundary point where it is defined. -/
-- Proof sketch: use the local characterization of the boundary as the zero set of the function and
-- evaluate it at the distinguished boundary point.
theorem IsBoundaryDefiningFunctionAt.eq_zero {p : M} {f : M → ℝ}
    (hf : BoundaryDefiningAt p f) : f p = 0 := sorry

/-- Exercise 5.44 (1): a tangent vector at a boundary point is inward-pointing exactly when the
boundary defining function has positive derivative on that vector. -/
-- Proof sketch: pass to a boundary chart in which the manifold is identified with a half-space and
-- the boundary defining function is a local defining equation for the boundary. In these
-- coordinates, both sides measure the sign of the same normal component.
theorem inwardPointing_iff_boundaryDefiningDerivative_pos {p : M} {f : M → ℝ}
    (hf : BoundaryDefiningAt p f) (v : TangentSpace (𝓡∂ n) p) :
    IsInwardPointing p v ↔ 0 < boundary_defining_derivative f v := sorry

/-- Exercise 5.44 (2): a tangent vector at a boundary point is outward-pointing exactly when the
boundary defining function has negative derivative on that vector. -/
-- Proof sketch: use the same boundary-chart comparison as in the inward-pointing case; the normal
-- derivative changes sign precisely when the normal component of the tangent vector is negative.
theorem outwardPointing_iff_boundaryDefiningDerivative_neg {p : M} {f : M → ℝ}
    (hf : BoundaryDefiningAt p f) (v : TangentSpace (𝓡∂ n) p) :
    IsOutwardPointing p v ↔ boundary_defining_derivative f v < 0 := sorry

/-- Exercise 5.44 (3): a tangent vector at a boundary point is tangent to the boundary exactly when
the boundary defining function has zero derivative on that vector. -/
-- Proof sketch: in boundary coordinates, both conditions say that the normal component of the
-- tangent vector vanishes, so the derivative of the defining function in that direction is zero.
theorem tangentToBoundary_iff_boundaryDefiningDerivative_eq_zero {p : M} {f : M → ℝ}
    (hf : BoundaryDefiningAt p f) (v : TangentSpace (𝓡∂ n) p) :
    IsBoundaryTangentVector p v ↔
      boundary_defining_derivative f v = 0 := sorry

end
