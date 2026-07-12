import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_2
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

section

open Metric

variable {E : Type u} [NormedAddCommGroup E]

-- Proof sketch: unfold `infimal_convolution`, expand `extendedIndicator C`, and use
-- `infDist_eq_iInf` to identify the infimum over `C` of the distances `dist x y = ‖x - y‖`
-- with the pointwise infimum over all `y : E` of `δ_C y + ‖x - y‖`.
/-- Example 2.6 (1): for a nonempty set `C`, the distance to `C` is the infimal convolution of
the extended indicator `δ_C` with the norm function `h₁(z) = ‖z‖`. -/
theorem infimal_convolution_extendedIndicator_norm_eq_infDist
    (C : Set E) (hC : C.Nonempty) (x : E) :
    (extendedIndicator C □ fun z ↦ (‖z‖ : EReal)) x =
      (infDist x C : EReal) := sorry

end

section

open Metric

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

-- Proof sketch: rewrite `infDist · C` using
-- `infimal_convolution_extendedIndicator_norm_eq_infDist`, note that the indicator of a convex set
-- is convex and that `z ↦ ‖z‖` is convex by `convexOn_univ_norm`, then apply the convexity
-- owner theorem `infimal_convolution_is_convex` and convert back to a real-valued `ConvexOn`
-- statement on the full effective domain.
/-- Example 2.6 (2): if `C` is convex, then its distance function `x ↦ infDist x C` is
convex on the whole space. -/
theorem convexOn_infDist (C : Set E) (hC : Convex ℝ C) :
    ConvexOn ℝ Set.univ (fun x ↦ infDist x C) := sorry

end

end
