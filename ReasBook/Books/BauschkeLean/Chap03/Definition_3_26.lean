import Mathlib
import BauschkeLean.Chap03.Definition_3_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open ContinuousLinearMap
open scoped InnerProductSpace

variable {𝓗 : Type u} {𝓚 : Type v}
variable [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]
variable [NormedAddCommGroup 𝓚] [InnerProductSpace ℝ 𝓚] [CompleteSpace 𝓚]

/- Definition 3.26 introduces the affine normal-equation solution set
`C_y = {x | T⋆ (T x) = T⋆ y}`. -/
abbrev moorePenroseSolutionSet (T : 𝓗 →L[ℝ] 𝓚) (y : 𝓚) : Set 𝓗 :=
  {x | adjoint T (T x) = adjoint T y}

/-- Membership in the normal-equation solution set is exactly the equation
`T⋆ (T x) = T⋆ y`. -/
theorem mem_moorePenroseSolutionSet_iff (T : 𝓗 →L[ℝ] 𝓚) (y : 𝓚) (x : 𝓗) :
    x ∈ moorePenroseSolutionSet T y ↔ adjoint T (T x) = adjoint T y := by
  rfl

/-- For a closed-range operator, the normal-equation solution set is a Chebyshev set. -/
theorem isChebyshev_moorePenroseSolutionSet (T : 𝓗 →L[ℝ] 𝓚)
    (hT_closed : IsClosed (T.range : Set 𝓚)) (y : 𝓚) :
    IsChebyshev (moorePenroseSolutionSet T y) := sorry
