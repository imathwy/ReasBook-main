import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_15
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Pointwise

universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/- Theorem 3.16 is `source-facing` in the chapter extendedRealSubdifferential API. The owner notions
`effective_domain`, `is_convex_function`, and `extendedRealSubdifferential` are already defined earlier in the
chapter, while Theorem 3.15 supplies the canonical two-function sum rules
`sum_subdifferential_subset_subdifferential_add` and
`subdifferential_add_eq_sum_subdifferential_of_mem_interiors`. This file keeps only the finite
family extension of that owner-level calculus, without introducing any parallel wrapper API. -/
recall extendedRealSubdifferential
recall sum_subdifferential_subset_subdifferential_add

-- Proof sketch: induct on `m`. For `m = 0`, both sides are the singleton sum/empty sum object.
-- For `m + 1`, split off the last summand and apply the canonical two-function weak sum rule from
-- Theorem 3.15 to `f 0` and `fun y ↦ ∑ i : Fin m, f i.succ y`, then use the induction hypothesis
-- on the tail family.
/-- Theorem 3.16 (1): weak finite-sum rule for the chapter owner `extendedRealSubdifferential`. Any finite
pointwise sum of subgradients at `x` is a subgradient of the pointwise sum at `x`. -/
theorem sum_subdifferential_subset_subdifferential_finset_sum
    {m : ℕ} (f : Fin m → E → EReal) (x : E) :
    (∑ i, extendedRealSubdifferential (f i) x) ⊆
      extendedRealSubdifferential (fun y ↦ ∑ i, f i y) x := sorry

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
finite domain, then the extendedRealSubdifferential of the finite pointwise sum is exactly the pointwise sum
of the individual subdifferentials. -/
theorem subdifferential_finset_sum_eq_sum_subdifferential_of_mem_iInter_interior
    {m : ℕ} (f : Fin m → E → EReal) (x : E)
    (hconvex : ∀ i, is_convex_function (f i))
    (hx : x ∈ ⋂ i, interior (finite_domain (f i))) :
    extendedRealSubdifferential (fun y ↦ ∑ i, f i y) x =
      ∑ i, extendedRealSubdifferential (f i) x := sorry

end
