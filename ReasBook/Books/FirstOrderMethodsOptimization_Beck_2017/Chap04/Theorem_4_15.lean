import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 4.15 is `source-facing` in the Chapter 4 conjugacy API. Its primitive data are the
owner predicates `IsProperExtendedRealFunction` and `is_convex_function`, while the conjugate is
the Chapter 4 owner `conjugate_function` on the dual space from Definition 4.1. -/

-- Proof sketch: choose `x₀ ∈ effective_domain f` from properness. Then `(y x₀ : EReal) - f x₀`
-- is finite for every dual vector `y`, so `conjugate_function f y` is never `⊥` because it
-- dominates this affine value. For finiteness at some dual vector, choose a point of the effective
-- domain with a subgradient and use the subgradient inequality to bound the supremum defining the
-- conjugate above.
/-- Theorem 4.15: properness of conjugate functions. In the finite-dimensional real normed-space
setting of the chapter, the conjugate of a proper convex extended-real-valued function is proper.
-/
theorem isProperExtendedRealFunction_conjugate_function
    (f : E → EReal) (hproper : IsProperExtendedRealFunction f)
    (hconvex : is_convex_function f) :
    IsProperExtendedRealFunction (conjugate_function f) := sorry

end
