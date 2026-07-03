

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_3_16 (from Chap03) -/
section

/- Proposition 3.16 is a `bridge/view` item in the chapter real-valued subdifferential API. The
owner abstraction is `subdifferentialAt`, and the source-facing scalar-slope statement is expressed
through its canonical one-dimensional vector-side bridge `euclideanSubdifferentialAt` from Theorem
3.4 rather than through an ad hoc encoding of real slopes as elements of `StrongDual ℝ ℝ`. -/

recall euclideanSubdifferentialAt

-- Proof sketch: split into the cases `x > 0`, `x < 0`, and `x = 0`. For `x ≠ 0`, the function
-- `t ↦ |t|` is differentiable at `x`, so the supporting-line inequality forces the only possible
-- slope to be `Real.sign x`, and that slope indeed works. At `x = 0`, the inequality becomes
-- `|y| ≥ v * y` for all `y`; testing it on `1` and `-1` gives `-1 ≤ v ≤ 1`, and conversely every
-- `v ∈ [-1, 1]` defines a valid supporting line at the origin.
/-- Proposition 3.16: for the one-dimensional function `g(x) = |x|`, the subdifferential is the
singleton with slope `Real.sign x` away from `0`, and at `0` it is the interval `[-1, 1]`. The
left-hand side is the canonical one-dimensional bridge `euclideanSubdifferentialAt`, so the
result is stated directly as a set of real slopes. -/
theorem euclidean_subdifferentialAt_abs_eq_piecewise (x : ℝ) :
    euclideanSubdifferentialAt (fun y : ℝ ↦ |y|) x =
      if x = 0 then Set.Icc (-1 : ℝ) 1 else {Real.sign x} := sorry

end

/-! ### Theorem_3_16 (from Chap03) -/
open scoped BigOperators Pointwise

universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/- Theorem 3.16 is `source-facing` in the chapter subdifferential API. The owner notions
`effective_domain`, `is_convex_function`, and `subdifferential` are already defined earlier in the
chapter, while Theorem 3.15 supplies the canonical two-function sum rules
`sum_subdifferential_subset_subdifferential_add` and
`subdifferential_add_eq_sum_subdifferential_of_mem_interiors`. This file keeps only the finite
family extension of that owner-level calculus, without introducing any parallel wrapper API. -/
recall subdifferential
recall sum_subdifferential_subset_subdifferential_add

-- Proof sketch: induct on `m`. For `m = 0`, both sides are the singleton sum/empty sum object.
-- For `m + 1`, split off the last summand and apply the canonical two-function weak sum rule from
-- Theorem 3.15 to `f 0` and `fun y ↦ ∑ i : Fin m, f i.succ y`, then use the induction hypothesis
-- on the tail family.
/-- Theorem 3.16 (1): weak finite-sum rule for the chapter owner `subdifferential`. Any finite
pointwise sum of subgradients at `x` is a subgradient of the pointwise sum at `x`. -/
theorem sum_subdifferential_subset_subdifferential_finset_sum
    {m : ℕ} (f : Fin m → E → EReal) (x : E) :
    (∑ i, subdifferential (f i) x) ⊆
      subdifferential (fun y ↦ ∑ i, f i y) x := sorry

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

recall finite_domain
recall subdifferential_add_eq_sum_subdifferential_of_mem_interiors

-- Proof sketch: induct on `m`. For `m = 0`, the statement is immediate. For `m + 1`, split off
-- `f 0` from the tail family, apply the canonical two-function exact sum rule from Theorem 3.15
-- to `f 0` and `fun y ↦ ∑ i : Fin m, f i.succ y`, and then invoke the induction hypothesis on the
-- tail. The hypothesis `x ∈ ⋂ i, interior (finite_domain (f i))` supplies the required
-- interior-point qualification at each step, so the public data is just convexity together with
-- the source-faithful finite-valued domain condition.
/-- Theorem 3.16 (2): if each summand is convex and the point lies in the interior of every
finite domain, then the subdifferential of the finite pointwise sum is exactly the pointwise sum
of the individual subdifferentials. -/
theorem subdifferential_finset_sum_eq_sum_subdifferential_of_mem_iInter_interior
    {m : ℕ} (f : Fin m → E → EReal) (x : E)
    (hconvex : ∀ i, is_convex_function (f i))
    (hx : x ∈ ⋂ i, interior (finite_domain (f i))) :
    subdifferential (fun y ↦ ∑ i, f i y) x =
      ∑ i, subdifferential (f i) x := sorry

end
