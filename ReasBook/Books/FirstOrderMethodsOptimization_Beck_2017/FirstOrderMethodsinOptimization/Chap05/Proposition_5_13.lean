import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Proposition 5.13 is `source-facing`: the textbook object is the extended-real-valued function
`x ↦ (1 / 2) ‖x‖² + δ_C(x)`. In item-per-file mode, the unavailable project-local bridge imports are
repaired away by stating the mathematically equivalent `core/canonical` owner formulation directly:
strong convexity of the real-valued half squared norm on the convex set `C`. -/

-- Proof sketch: use the standard inner-product-space characterization
-- `strongConvexOn_iff_convex` with `m = 1`. After subtracting `(1 / 2) ‖x‖²`, the remaining
-- function is constant `0` on `C`, hence convex; this is the canonical owner-level form of the
-- source statement about `x ↦ (1 / 2) ‖x‖² + δ_C(x)`.
/-- Proposition 5.13: on a convex set `C` in a real inner product space, the half squared norm is
`1`-strongly convex. This is the canonical real-valued formulation of the source statement that the
extended-real-valued function `x ↦ (‖x‖² / 2 : ℝ) + δ_C(x)` is `1`-strongly convex. -/
theorem half_squared_norm_is_one_strongly_convex_on
    (C : Set E) (hC : Convex ℝ C) :
    StrongConvexOn C 1 (fun x : E ↦ ‖x‖ ^ (2 : ℕ) / 2) := sorry

end
