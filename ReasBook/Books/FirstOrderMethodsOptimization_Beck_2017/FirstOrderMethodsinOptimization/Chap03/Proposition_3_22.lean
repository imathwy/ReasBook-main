import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap03.Definition_3_18
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap03.Proposition_3_12
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap03.Theorem_3_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open Metric
open InnerProductSpace (toDual)
open scoped RealInnerProductSpace

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable (C : Set E) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C)
  (hC_convex : Convex ℝ C)

local notation "P" => fun y ↦
  (metricProjection C hC_nonempty hC_closed.isComplete hC_convex y : E)

-- Proof sketch: if `x ∉ C`, use Proposition 3.12 to identify the gradient of
-- `y ↦ (infDist y C)^2 / 2` with `y - P_C(y)` and combine it with the singleton-extendedRealSubdifferential
-- criterion for differentiable convex functions to obtain the unique normalized subgradient vector.
-- If `x ∈ C`, rewrite the subgradient inequality for `y ↦ infDist y C` in Euclidean coordinates:
-- one inclusion follows by testing the inequality on points of `C` and on `x + v`, and the reverse
-- inclusion follows from the projection formula `infDist y C = ‖y - P_C(y)‖` together with the
-- normal-cone inequality and Cauchy-Schwarz.
/- Proposition 3.22 is a `bridge/view` theorem in the chapter extendedRealSubdifferential API: the owner
notion remains `subdifferentialAt`, and the left-hand side is stated through its canonical
Euclidean bridge `euclideanSubdifferentialAt`. The right-hand side still uses the owner
`normal_cone`, since the textbook formula is intrinsically the dual normal cone intersected with
the closed unit ball. -/
open Classical in
theorem euclidean_subdifferentialAt_infDist_eq_piecewise
    (x : E) :
    euclideanSubdifferentialAt (fun y ↦ infDist y C) x =
      if x ∈ C then
        {v : E | (toDual ℝ E v : Module.Dual ℝ E) ∈ normal_cone C x} ∩ closedBall (0 : E) 1
      else
        {((infDist x C)⁻¹ : ℝ) • (x - P x)} := sorry

end
