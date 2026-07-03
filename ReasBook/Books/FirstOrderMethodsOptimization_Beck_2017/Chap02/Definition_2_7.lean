import FirstOrderMethodsinOptimization.Chap02.Definition_2_1
import FirstOrderMethodsinOptimization.Chap02.Definition_2_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [AddCommMonoid E] [Module ℝ E] {f : E → EReal}

/- Definition 2.7 reuses the chapter owner `is_convex_function` from Definition 2.6 for convexity
of an extended-real-valued function. -/
recall is_convex_function

/-- Definition 2.7: convexity is equivalent to the two-point Jensen inequality along every segment
joining two points of the effective domain, with weight in `[0, 1]`. -/
theorem is_convex_function_iff_segment_ineq :
    is_convex_function f ↔
      ∀ x ∈ effective_domain f, ∀ y ∈ effective_domain f, ∀ {t : ℝ},
        t ∈ Set.Icc (0 : ℝ) 1 →
        f (t • x + (1 - t) • y) ≤ (t : EReal) * f x + ((1 - t : ℝ) : EReal) * f y := sorry

-- Proof sketch: identify the real epigraph from Definition 2.6 with the epigraph of the finite
-- restriction `x ↦ (f x).toReal` on `effective_domain f`; the local hypothesis `h_ne_bot` rules
-- out `-∞` on the domain, and membership in `effective_domain f` rules out `∞`, so
-- `convexOn_iff_convex_epigraph` applies to a genuine real-valued restriction.
/-- Companion bridge: if an extended-real-valued function never takes the value `-∞` on its
effective domain, then the source Jensen formulation is equivalent to convexity of the finite-valued
restriction `x ↦ (f x).toReal` on that domain. -/
theorem is_convex_function_iff_convexOn_toReal
    (h_ne_bot : ∀ x ∈ effective_domain f, f x ≠ ⊥) :
    is_convex_function f ↔ ConvexOn ℝ (effective_domain f) (fun x ↦ (f x).toReal) := sorry

/-- If a convex extended-real-valued function never takes the value `-∞` on its effective domain,
then its finite-valued restriction is convex on that domain. -/
theorem convexOn_toReal_of_is_convex_function (hf : is_convex_function f)
    (h_ne_bot : ∀ x ∈ effective_domain f, f x ≠ ⊥) :
    ConvexOn ℝ (effective_domain f) (fun x ↦ (f x).toReal) :=
  (is_convex_function_iff_convexOn_toReal h_ne_bot).1 hf

-- Proof sketch: the convexity of the effective domain is the set component of
-- the real epigraph under the first-coordinate projection.
/-- If an extended-real-valued function is convex, then its effective domain is a convex set. -/
theorem effective_domain_convex_of_is_convex_function (hf : is_convex_function f) :
    Convex ℝ (effective_domain f) := sorry

-- Proof sketch: apply `effective_domain_convex_of_is_convex_function` to `hx`, `hy`, and the
-- bounds encoded by `ht`.
/-- If an extended-real-valued function is convex and finite at two points of its effective
domain, then it is also finite at every convex combination of those points with weight in `[0,
1]`. -/
theorem combo_mem_effective_domain_of_is_convex_function (hf : is_convex_function f)
    {x y : E} (hx : x ∈ effective_domain f)
    (hy : y ∈ effective_domain f) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    t • x + (1 - t) • y ∈ effective_domain f := by
  exact
    effective_domain_convex_of_is_convex_function hf hx hy ht.1
      (sub_nonneg.2 ht.2) (by ring)

end
