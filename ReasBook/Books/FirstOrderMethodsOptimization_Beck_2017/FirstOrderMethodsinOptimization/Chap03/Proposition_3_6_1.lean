import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap03.Definition_3_2
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap03.Definition_3_15

-- Declarations for this item will be appended below by the statement pipeline.

section

/- Proposition 3.6.1 is `source-facing`: it studies one concrete extended-real-valued example.
The owner abstraction for “equal to a function on a feasible set and `⊤` outside” already exists
upstream as `constrained_problem_objective`, so the only primitive data kept here are the concrete
objective `x ↦ -√x` and the feasible set `[0, ∞)`. The proposition clauses themselves stay at the
chapter owners `is_convex_function` and `subdifferential`; no extra helper API is exposed beyond
that concrete source object. -/

/-- The extended-real function equal to `-√x` on the nonnegative ray and `∞` on the negative
half-line. -/
noncomputable def negative_sqrt_extension : ℝ → EReal :=
  constrained_problem_objective (fun x ↦ ((-Real.sqrt x : ℝ) : EReal)) (Set.Ici (0 : ℝ))

-- Proof sketch: `negative_sqrt_extension` never takes the value `⊥`, so the bridge
-- `is_convex_function_iff_convexOn_toReal` reduces the owner-level convexity claim to convexity of
-- the finite restriction on its effective domain, computed locally as `[0, ∞)`. On that ray the
-- function is `x ↦ -Real.sqrt x`, which is convex because `Real.sqrt` is concave on the
-- nonnegative ray.
/-- Proposition 3.6.1 (1): the function `negative_sqrt_extension` is convex. -/
theorem negative_sqrt_extension_is_convex_function :
    is_convex_function negative_sqrt_extension := sorry

-- Proof sketch: assume `g ∈ subdifferential negative_sqrt_extension 0`. The subgradient inequality
-- then gives `-Real.sqrt y ≥ g * y` for every `y ≥ 0`. Evaluating at `y = 1` forces `g < 0`, and
-- taking `y = 1 / (2 * g ^ 2)` yields a contradiction.
/-- Proposition 3.6.1 (2): the subdifferential of `negative_sqrt_extension` at `0` is empty, so
the function is not subdifferentiable there. -/
theorem negative_sqrt_extension_subdifferential_zero :
    subdifferential negative_sqrt_extension (0 : ℝ) = ∅ := sorry

end
