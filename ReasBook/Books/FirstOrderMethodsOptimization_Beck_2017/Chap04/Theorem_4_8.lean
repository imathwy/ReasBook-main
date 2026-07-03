import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_8
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 4.8 is `source-facing` in the chapter conjugacy calculus. Its ambient notions are the
project owner declarations `IsProperExtendedRealFunction`, `is_convex_function`,
`infimal_convolution`, and `conjugate_function`, so this file reuses those owners directly rather
than restating parallel local copies. -/

-- Proof sketch: fix `y : Module.Dual ℝ E` and apply Fenchel--Rockafellar duality to the pair
-- `h₁` and `g x = h₂ x - y x`. Because `h₂` is finite everywhere, the qualification condition is
-- automatic from properness of `h₁`. Rewriting `g* z` as
-- `conjugate_function (fun x ↦ (h₂ x : EReal)) (y - z)` yields the infimal-convolution formula.
/-- Theorem 4.8: if `h₁` is a proper convex extended-real-valued function and `h₂` is a real-valued
convex function, then the Fenchel conjugate of the pointwise sum `h₁ + h₂` is the infimal
convolution of the conjugates `h₁*` and `h₂*`. The real-valued convexity of `h₂` is encoded by
`ConvexOn ℝ Set.univ h₂`. -/
theorem conjugate_function_add_eq_infimal_convolution
    (h₁ : E → EReal) (h₂ : E → ℝ) (hh₁_proper : IsProperExtendedRealFunction h₁)
    (hh₁_convex : is_convex_function h₁) (hh₂_convex : ConvexOn ℝ Set.univ h₂) :
    conjugate_function (fun x ↦ h₁ x + (h₂ x : EReal)) =
      conjugate_function h₁ □ conjugate_function (fun x ↦ (h₂ x : EReal)) := sorry

end
