import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap03.Definition_3_2
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap03.Definition_3_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise

universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/- Theorem 3.15 is `source-facing` at the chapter owner
`subdifferential : Set (Module.Dual ℝ E)`. The continuous-dual object
`strongDualSubdifferential` from Theorem 3.1 is only a `bridge/view`, so the main declarations
here stay on the owner abstraction instead of restating the theorem after passing to `StrongDual`.
-/
recall subdifferential

-- Proof sketch: expand membership in the pointwise sum
-- `subdifferential f₁ x + subdifferential f₂ x`, choose `g₁ ∈ subdifferential f₁ x` and
-- `g₂ ∈ subdifferential f₂ x` with sum `g`,
-- and add the two defining subgradient inequalities to obtain the supporting inequality for
-- `f₁ + f₂` at `x`. Membership in the left-hand side already supplies the effective-domain
-- condition for both summands, so no extra hypotheses are primitive in this weak inclusion.
/-- Theorem 3.15 (1): any sum of a subgradient of `f₁` at `x` and a subgradient of `f₂` at `x`
is a subgradient of the pointwise sum `f₁ + f₂` at `x`. -/
theorem sum_subdifferential_subset_subdifferential_add
    (f₁ f₂ : E → EReal) (x : E) :
    subdifferential f₁ x + subdifferential f₂ x ⊆
      subdifferential (f₁ + f₂) x := sorry

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

recall finite_domain
recall is_convex_function

/- Part (2) stays on the same owner `subdifferential`; `finite_domain` is only the source-faithful
interior-point qualification and not a second public owner abstraction. -/

-- Proof sketch: the inclusion `⊇` is the weak sum rule from part (1). For the converse inclusion,
-- apply the max formula to the proper convex function `f₁ + f₂` at an interior point of its
-- finite domain, use additivity of directional derivatives together with the max formula for each
-- summand, and identify compact convex sets with equal support functions. Stating the qualification
-- on `finite_domain` matches the textbook `dom` directly, so no extra global no-`⊥` hypotheses are
-- primitive public data.
/-- Theorem 3.15 (2): if `x` lies in the interior of the finite domains of `f₁` and `f₂`, then
the subdifferential of the pointwise sum is exactly the pointwise sum of the two
subdifferentials. -/
theorem subdifferential_add_eq_sum_subdifferential_of_mem_interiors
    (f₁ f₂ : E → EReal) (x : E)
    (hconvex₁ : is_convex_function f₁)
    (hconvex₂ : is_convex_function f₂)
    (hx₁ : x ∈ interior (finite_domain f₁))
    (hx₂ : x ∈ interior (finite_domain f₂)) :
    subdifferential (f₁ + f₂) x =
      subdifferential f₁ x + subdifferential f₂ x := sorry

end
