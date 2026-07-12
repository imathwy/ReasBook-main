import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_15_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ConvexFunctionPolar RealInnerProductSpace Rockafellar

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 15.5.1 states that, on the Chapter 15 class of nonnegative closed
  convex functions on a finite-dimensional real inner-product space and vanishing at the origin,
  Fenchel conjugation and polarity commute. Specializing `E = EuclideanSpace ℝ (Fin n)` recovers
  the textbook `R^n` statement.
- `core/canonical`: the owner abstraction is `Function.IsNonnegativeClosedConvexZero`, and the
  owner-level Chapter 15 exchange theorems are
  `obverse_convex_function_polar_eq_convexConjugate_of_nonnegative_closed_convex_zero` and
  `convex_function_polar_obverse_eq_convexConjugate_of_nonnegative_closed_convex_zero`.
- `bridge/view`: the present corollary is the source-facing commutation identity obtained by
  rewriting `(fᵒ)⋆` through the Chapter 15 exchange theorem applied to `fᵒ`, then rewriting
  `obverse fᵒ` through the companion exchange theorem for `f`.

Domain-style sampling used here:
- `Function.IsNonnegativeClosedConvexZero`;
- `convex_function_polar`;
- `obverse_convex_function_polar_eq_convexConjugate_of_nonnegative_closed_convex_zero`;
- `convex_function_polar_obverse_eq_convexConjugate_of_nonnegative_closed_convex_zero`.

Primitive data vs derived API:
- primitive input: a function `f : E → EReal` with owner hypothesis
  `f.IsNonnegativeClosedConvexZero`;
- derived API: the target commutation identity between `f⋆` and the Chapter 15 polar owner `ᵒ`.

Layer target: `source-facing`; the theorem is stated directly at the Chapter 15 owner layer, with
the Euclidean `R^n` reading treated only as a specialization.
-/

variable (f : E → EReal)

-- Proof sketch: Theorem 15.5 applied to `fᵒ` rewrites `(fᵒ)⋆` as `(obverse fᵒ)ᵒ`. The companion
-- exchange theorem for `f` then rewrites `obverse fᵒ` as `f⋆`.
/-- Corollary 15.5.1: if `f` is a nonnegative closed convex function on a finite-dimensional real
inner-product space with `f 0 = 0`, then the Fenchel conjugate of its polar equals the polar of
its Fenchel conjugate, equivalently
`convexConjugate (convex_function_polar f) =
  convex_function_polar ((convexConjugate f : E → EReal))`,
i.e. `f^{∘*} = f^{*∘}`. Specializing `E = EuclideanSpace ℝ (Fin n)` recovers the textbook `R^n`
statement. -/
theorem convexConjugate_convex_function_polar_eq_convex_function_polar_convexConjugate_of_nonnegative_closed_convex_zero
    (hf : f.IsNonnegativeClosedConvexZero) :
    (fun x : E ↦ (fᵒ)⋆ x) = fun x ↦ (f⋆)ᵒ x := by
  funext x
  letI : f.IsNonnegativeClosedConvexZero := hf
  letI : fᵒ.IsNonnegativeClosedConvexZero := inferInstance
  calc
    (fᵒ)⋆ x = (obverse fᵒ)ᵒ x := by
      simpa using congrFun
        (convex_function_polar_obverse_eq_convexConjugate_of_nonnegative_closed_convex_zero
          fᵒ inferInstance).symm x
    _ = (f⋆)ᵒ x := by
      rw [obverse_convex_function_polar_eq_convexConjugate_of_nonnegative_closed_convex_zero
        f hf]

end
