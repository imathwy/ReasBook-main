import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Chapter 2's `effective_domain` is the canonical finite-valued-domain owner, while mathlib's
`StrongConvexOn` supplies the canonical owner abstraction for the real-valued bridge. -/

/-- Definition 5.16: an extended-real-valued function is `σ`-strongly convex if it never takes
the value `-∞`, its effective domain is convex, and it satisfies the quadratic Jensen inequality on
that domain for every weight `t ∈ [0, 1]`. -/
class is_strongly_convex_function (f : E → EReal) (σ : ℝ) : Prop where
  /-- A strongly convex extended-real-valued function never takes the value `-∞`. -/
  ne_bot : ∀ x, f x ≠ ⊥
  /-- The effective domain of a strongly convex function is convex. -/
  convex_effective_domain : Convex ℝ (effective_domain f)
  /-- The defining quadratic Jensen inequality holds along every segment in the effective domain. -/
  segment_ineq :
    ∀ ⦃x⦄, x ∈ effective_domain f → ∀ ⦃y⦄, y ∈ effective_domain f → ∀ ⦃t : ℝ⦄,
      t ∈ Set.Icc (0 : ℝ) 1 →
        f (t • x + (1 - t) • y) ≤
          (t : EReal) * f x + ((1 - t : ℝ) : EReal) * f y -
            (((σ / 2) * t * (1 - t) * ‖x - y‖ ^ (2 : ℕ) : ℝ) : EReal)
  /-- The strong-convexity modulus is strictly positive. -/
  sigma_pos : 0 < σ

-- Proof sketch: use the global `ne_bot` hypothesis to make `(f x).toReal` finite on
-- `effective_domain f`, translate `segment_ineq` into the `UniformConvexOn` inequality defining
-- `StrongConvexOn`, and read convexity of the domain from `convex_effective_domain`. For the
-- converse, extract convexity and the segment inequality from `StrongConvexOn` and coerce them
-- back to `EReal`, while keeping the source-side no-`⊥` condition explicit.
/-- The source strong-convexity predicate is equivalent to strong convexity of the real-valued
restriction `x ↦ (f x).toReal` on the effective domain, together with the ambient no-`-∞`
condition. -/
theorem is_strongly_convex_function_iff_strongConvexOn_toReal
    {f : E → EReal} {σ : ℝ} :
    is_strongly_convex_function f σ ↔
      0 < σ ∧
        (∀ x, f x ≠ ⊥) ∧
        StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal) := sorry

/-- The source-facing strong-convexity class exposes the canonical `StrongConvexOn` owner
abstraction on the real-valued restriction to the effective domain. -/
theorem strongConvexOn_toReal_of_is_strongly_convex_function
    {f : E → EReal} {σ : ℝ} (hf : is_strongly_convex_function f σ) :
    StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal) :=
  (is_strongly_convex_function_iff_strongConvexOn_toReal.mp hf).2.2

/-- Strong convexity exposes the canonical `StrongConvexOn` owner abstraction to typeclass
search. -/
instance instFactStrongConvexOnToReal {f : E → EReal} {σ : ℝ}
    [hf : is_strongly_convex_function f σ] :
    Fact (StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal)) where
  out := strongConvexOn_toReal_of_is_strongly_convex_function hf

end
