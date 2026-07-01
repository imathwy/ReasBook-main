import Mathlib
import FirstOrderMethodsinOptimization.Chap02.Definition_2_5
import FirstOrderMethodsinOptimization.Chap02.Definition_2_6
import FirstOrderMethodsinOptimization.Chap03.Definition_3_2
import FirstOrderMethodsinOptimization.Chap03.Definition_3_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 3.31 is `source-facing` in the chapter constrained convex-optimization API. The owner
abstractions are already upstream: `effective_domain` from Definition 2.5,
`is_convex_function` from Definition 2.6, `subdifferential` from Definition 3.2,
`normal_cone` from Definition 3.3, and mathlib's `IsMinOn` for minimizers on a set. The theorem
therefore stays as the textbook optimality criterion itself, with no parallel local wrapper API.
As in the chapter sum rule, the relative-interior qualification already forces
`(effective_domain f).Nonempty`, so only the no-`⊥` half of properness is primitive data. -/
recall effective_domain
recall is_convex_function
recall subdifferential
recall normal_cone
recall IsMinOn

-- Proof sketch: rewrite constrained optimality on `C` as unconstrained optimality of
-- `f + δ_C`, then apply Fermat's criterion to that extended-real objective. Use the
-- relative-interior qualification to invoke the convex sum rule
-- `∂ (f + δ_C) (xStar) = ∂ f xStar + ∂ δ_C xStar`, and identify
-- `∂ δ_C xStar` with `normal_cone C xStar`; finally rewrite
-- `0 ∈ ∂ f xStar + normal_cone C xStar` as the existence of
-- `g ∈ ∂ f xStar` with `-g ∈ normal_cone C xStar`.
/-- Theorem 3.31: necessary and sufficient optimality conditions for convex constrained
optimization. If `f` is a convex extended-real-valued function that never takes the value `-∞`,
`C` is convex, and `ri(dom f) ∩ ri(C) ≠ ∅`, then a feasible point `xStar ∈ C` minimizes `f` on
`C` if and only if there exists a subgradient `g ∈ ∂ f(xStar)` whose negation belongs to the
normal cone `N_C(xStar)`. -/
theorem isMinOn_iff_exists_subgradient_neg_mem_normal_cone
    {f : E → EReal} (h_ne_bot : ∀ x : E, f x ≠ ⊥) (hconv : is_convex_function f)
    {C : Set E} (hC : Convex ℝ C)
    (hri : (intrinsicInterior ℝ (effective_domain f) ∩ intrinsicInterior ℝ C).Nonempty)
    {xStar : E} (hxStar : xStar ∈ C) :
    IsMinOn f C xStar ↔
      ∃ g : Module.Dual ℝ E, g ∈ subdifferential f xStar ∧ -g ∈ normal_cone C xStar := sorry

end
