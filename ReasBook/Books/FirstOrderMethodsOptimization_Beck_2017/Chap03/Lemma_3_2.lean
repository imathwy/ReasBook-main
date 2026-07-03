import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_7
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_10
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Topology

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Lemma 3.2 is a `source-facing` consequence in the chapter directional-derivative API. The owner
objects are the Chapter 3 directional-derivative declarations
`has_directional_derivative_at`/`directional_derivative`, together with the owner existence theorem
`exists_real_has_directional_derivative_at_of_convex_interior_point` from Theorem 3.8 and the
Chapter 2 convexity API `is_convex_function`, with
`is_convex_function_iff_segment_ineq` supplying the canonical segment-inequality view. Unlike
Theorem 3.11, this lemma does not assume an inner-product or finite-dimensional structure, so its
main statement should remain a direct affine lower bound rather than being collapsed into a
subdifferential-max formula. -/
recall effective_domain
recall is_convex_function
recall is_convex_function_iff_segment_ineq
recall has_directional_derivative_at
recall directional_derivative
recall directional_derivative_eq_of_has_directional_derivative_at
recall exists_real_has_directional_derivative_at_of_convex_interior_point

-- Proof sketch: if `y ∉ effective_domain f`, then `f y = ⊤` and the inequality is automatic. For
-- `y ∈ effective_domain f`, restrict `f` to the segment from `x` to `y`. Convexity gives
-- `(f (x + t • (y - x)) - f x) / t ≤ f y - f x` for every `t ∈ (0, 1)`. Since `x` is an interior
-- point of `finite_domain f`, the right-hand limit of these
-- difference quotients is the directional derivative at `x` along `y - x`, and passing to the
-- limit yields the claimed affine lower bound.
/-- Lemma 3.2: if `f` is a convex extended-real-valued function that never takes the value `-∞`
and `x` lies in the interior of its effective domain, then every point `y` satisfies the affine
lower bound determined by the directional derivative of `f` at `x` in the direction `y - x`. -/
theorem value_ge_value_add_directional_derivative_of_mem_effective_domain
    (f : E → EReal) (x y : E) (hconvex : is_convex_function f)
    (h_ne_bot : ∀ z, f z ≠ ⊥) (hx : x ∈ interior (effective_domain f)) :
    f y ≥ f x + directional_derivative f x (y - x) := by
  by_cases hy : y ∈ effective_domain f
  · rcases
      exists_real_has_directional_derivative_at_of_convex_interior_point
        f x (y - x)
        hconvex
        (by
          have hfinite : finite_domain f = effective_domain f :=
            finite_domain_eq_effective_domain h_ne_bot
          simpa [hfinite] using hx) with
      ⟨ℓ, hℓ⟩
    rw [directional_derivative_eq_of_has_directional_derivative_at hℓ]
    sorry
  · have hfy_top : f y = ⊤ := by
      have hy' : ¬ f y < ⊤ := by
        simpa [effective_domain] using hy
      exact le_antisymm le_top (not_lt.mp hy')
    simp [hfy_top]

end
