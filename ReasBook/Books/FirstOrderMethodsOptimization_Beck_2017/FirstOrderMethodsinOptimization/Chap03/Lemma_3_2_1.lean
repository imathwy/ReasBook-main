import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap02.Definition_2_7
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap03.Definition_3_8
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap03.Definition_3_10

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Topology

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (f : E → EReal) (x : E)
variable (hconvex : is_convex_function f) (hx : x ∈ interior (finite_domain f))

/- Lemma 3.2.1 is `source-facing` in the chapter directional-derivative API. The ambient owner
objects already live upstream: `directional_derivative` from Chapter 3 and
`is_convex_function`, together with its canonical source bridge
`is_convex_function_iff_segment_ineq`, from Chapter 2. Under the present `NormedSpace`
hypotheses the project has no stronger owner abstraction bundling convexity and positive
homogeneity of `directional_derivative f x`, so the public API stays with these two atomic
owner-level consequences instead of introducing a parallel wrapper. The primitive local hypothesis
is the chapter owner `x ∈ interior (finite_domain f)`, from which nearby finiteness is derived as
needed; the earlier split `effective_domain`/`≠ ⊥` assumptions are therefore not kept as public
data. -/
recall directional_derivative
recall is_convex_function
recall is_convex_function_iff_segment_ineq
recall finite_domain

-- Proof sketch: apply the chapter owner characterization of convexity from
-- `is_convex_function_iff_segment_ineq` to the function `d ↦ directional_derivative f x d`. For
-- `t ∈ [0, 1]`, compare the directional difference quotient in the mixed direction
-- `t • d₁ + (1 - t) • d₂` with the corresponding convex combination of the quotients in the
-- directions `d₁` and `d₂` using convexity of `f`, then pass to the right-hand limit. The
-- hypothesis `hx` already supplies the local finite-valued neighborhood needed to keep those
-- quotients meaningful near `0`.
/-- Lemma 3.2.1 (1): for a convex extended-real-valued function and an interior point of its finite
domain, the directional derivative is a convex extended-real-valued function of the direction. -/
theorem directional_derivative_is_convex_function :
    is_convex_function (directional_derivative f x) := sorry

-- Proof sketch: if `a = 0`, compute directly from the difference quotient. For `a > 0`, rewrite
-- the quotient in direction `a • d` by the change of variables `β = α * a`, factor out the scalar
-- `(a : EReal)`, and pass to the right-hand limit defining `directional_derivative`.
/-- Lemma 3.2.1 (2): for a convex extended-real-valued function and an interior point of its finite
domain, the directional derivative is positively homogeneous in the direction variable. -/
theorem directional_derivative_nonneg_smul (a : ℝ) (ha : 0 ≤ a) (d : E) :
    directional_derivative f x (a • d) = (a : EReal) * directional_derivative f x d := sorry

end
