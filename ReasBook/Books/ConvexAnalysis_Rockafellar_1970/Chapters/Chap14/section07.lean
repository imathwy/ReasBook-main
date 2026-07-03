import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_14_7 (from Chap03) -/
noncomputable section

open scoped Pointwise RealInnerProductSpace Rockafellar
open Function

section

universe u

variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 14.7 states that if `f` is a nonnegative closed convex function with
  `f 0 = 0`, then its Fenchel conjugate is again nonnegative and normalized at the origin, and for
  every positive finite level `α` the polar of the `α`-sublevel set of `f` is contained in the
  reciprocal dilation of the corresponding `α`-sublevel set of `f⋆`, with the latter contained in
  twice that polar.
- `core/canonical`: the owner abstractions already present in the project are `convexConjugate`
  with notation `f⋆`, the source-facing set polar `Set.polar` with notation `Cᵒ`, the global
  convexity predicate `Function.IsConvex ℝ f`, and `LowerSemicontinuous` for closedness.
- `bridge/view`: the source parameter range `0 < α < ∞` is rendered by a positive scalar
  `α : Set.Ioi (0 : ℝ)`, since finiteness is automatic for real levels; the source's `R^n`
  ambient is upgraded
  to the canonical real inner-product-space layer already used by the owner declarations.

Domain-style sampling used here:
- `convexConjugate`;
- `Set.polar`;
- the support-function and gauge polarity interface around Theorem 14.5;
- the generated positively homogeneous function interface used in Theorems 13.5 and 9.7.

Primitive data vs derived API:
- primitive input: the function `f : E → EReal`;
- primitive source hypotheses: convexity, lower semicontinuity, nonnegativity, and the
  normalization `f 0 = 0`;
- derived API: the source-facing consequences that `f⋆` is nonnegative and vanishes at the origin,
  together with the two atomic sublevel-set polarity statements.

The source sentence is split into four atomic declarations to avoid a single oversized conjunction.
Layer target: `source-facing`, stated directly on the canonical owner ambient rather than the
coordinate model `EuclideanSpace ℝ (Fin n)`.
-/

variable (f : E → EReal)

-- Proof sketch: evaluate the defining supremum at `x = 0`; the term
-- `⟪0, xStar⟫ - f 0` is `0`, so `f⋆ xStar` is at least `0`.
/-- Theorem 14.7 (1): if `f 0 = 0`, then its conjugate `f* = f⋆` is nonnegative.
This is the first consequence used under the theorem's stronger standing hypotheses. -/
theorem convexConjugate_nonneg_of_map_zero
    (hf_zero : f 0 = 0)
    (xStar : E) :
    (0 : EReal) ≤ f⋆ xStar := by
  have h_zero : f 0 = 0 := hf_zero
  have h_at_zero : (0 : EReal) ≤ ((⟪(0 : E), xStar⟫ : ℝ) : EReal) - f 0 := by
    simp [h_zero]
  rw [convexConjugate]
  exact h_at_zero.trans (le_iSup (fun x : E ↦ ((⟪x, xStar⟫ : ℝ) : EReal) - f x) 0)

-- Proof sketch: clause (1) gives the lower bound. For the upper bound, every term
-- `⟪0, x⟫ - f x = -f x` is at most `0` when `f` is nonnegative.
/-- Theorem 14.7 (2): if `f` is nonnegative and `f 0 = 0`, then the conjugate `f* = f⋆`
vanishes at the origin. -/
theorem convexConjugate_zero_of_nonneg_map_zero
    (hf_nonneg : ∀ x : E, (0 : EReal) ≤ f x) (hf_zero : f 0 = 0) :
    f⋆ (0 : E) = 0 := sorry

section

variable (hf_convex : Function.IsConvex ℝ f) (hf_closed : LowerSemicontinuous f)
variable (hf_nonneg : ∀ x : E, (0 : EReal) ≤ f x) (hf_zero : f 0 = 0)

-- Proof sketch: set `C = {x | f x ≤ α}`. For `xStar ∈ Set.polar C`, the defining inequality
-- `⟪x, xStar⟫ ≤ 1` on `C` implies `⟪x, α • xStar⟫ ≤ α ≤ f x + α` for every `x`, so the Fenchel
-- supremum formula gives `f⋆ (α • xStar) ≤ α`. Rewriting this says exactly
-- `xStar ∈ α⁻¹ • {xStar | f⋆ xStar ≤ α}`.
/-- Theorem 14.7 (3): for every positive scalar `α`, the polar of the closed `α`-sublevel set of
`f` is contained in the reciprocal dilation of the `α`-sublevel set of `f* = f⋆`. -/
theorem polar_sublevelSet_subset_inv_smul_conjugate_sublevelSet_of_nonnegative_closed_convex_zero
    (α : Set.Ioi (0 : ℝ)) :
    ({x : E | f x ≤ ((α : ℝ) : EReal)}ᵒ[ℝ]) ⊆
      ((α : ℝ)⁻¹ : ℝ) • {xStar : E | f⋆ xStar ≤ ((α : ℝ) : EReal)} := sorry

-- Proof sketch: with the same notation `C = {x | f x ≤ α}`, the gauge estimate complementary to
-- clause (3) gives `γ(xStar | Cᵒ) ≤ f* xStar + α`. Hence the dual sublevel set
-- `{xStar | f⋆ xStar ≤ α}` lies in `2 α • Cᵒ`, and scaling by `α⁻¹`
-- gives the stated upper inclusion in the sandwich from Theorem 14.7.
/-- Theorem 14.7 (4): for every positive scalar `α`, the reciprocal dilation of the
`α`-sublevel set of `f* = f⋆` is contained in twice the polar of the `α`-sublevel set of `f`. -/
theorem
    inv_smul_conjugateSublevel_subset_two_smul_polar_sublevel_of_nonnegative_closed_convex_zero
    (α : Set.Ioi (0 : ℝ)) :
    ((α : ℝ)⁻¹ : ℝ) • {xStar : E | f⋆ xStar ≤ ((α : ℝ) : EReal)} ⊆
      (2 : ℝ) • ({x : E | f x ≤ ((α : ℝ) : EReal)}ᵒ[ℝ]) := sorry

end

end
