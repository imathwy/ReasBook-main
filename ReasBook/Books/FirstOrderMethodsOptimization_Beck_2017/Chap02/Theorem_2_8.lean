import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

-- Proof sketch: consider the jointly convex function `(x, y) ↦ h₁ y + h₂ (x - y)`, obtained by
-- combining the convexity of `h₁` with the convexity of `h₂` under the affine map `(x, y) ↦ x - y`;
-- then apply the partial-minimization theorem to the infimum over the second variable.
/-- Theorem 2.8: if `h₁` is a convex extended-real-valued function and `h₂` is a real-valued
convex function, then their infimal convolution `h₁ □ h₂` is convex. In the chapter owner
formulation, the textbook properness hypothesis on `h₁` is redundant for this convexity
conclusion, so it is omitted from the Lean statement. -/
theorem infimal_convolution_is_convex (h₁ : E → EReal) (h₂ : E → ℝ)
    (hh₁_convex : is_convex_function h₁) (hh₂ : ConvexOn ℝ Set.univ h₂) :
    is_convex_function (h₁ □ fun x ↦ (h₂ x : EReal)) := sorry

end

end
