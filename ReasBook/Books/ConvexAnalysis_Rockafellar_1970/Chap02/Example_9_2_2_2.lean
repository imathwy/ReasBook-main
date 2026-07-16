import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap01.Remark_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_4_0
import ConvexAnalysis_Rockafellar_1970.Chap02.Corollary_9_2_2
import ConvexAnalysis_Rockafellar_1970.Chap02.Definition_8_0_2
import ConvexAnalysis_Rockafellar_1970.Chap02.Definiton_8_5_0

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

attribute [local instance] Classical.propDecidable

open scoped Pointwise Rockafellar
open Set

/-!
Source/core/bridge triage for this item.

- `source-facing`: the example specializes Corollary 9.2.2 to the case where `f₁` is the
  `0/+∞` indicator of `-C`, so that `f₁ □ f` becomes the infimum of `f` over the translate
  `C + x`.
- `core/canonical`: the owner declarations already present in the project are
  `indicatorFunction`, `infimal_convolution`, `recessionCone`, object-prefix
  `(·).recessionCone`, the
  recession owner `Function.recessionFunction` with chapter notation `(·)₀⁺`,
  `LowerSemicontinuous`, and `Function.IsConvex`.
- `bridge/view`: the textbook condition "no common direction of recession" is rendered by saying
  that the only vector lying in both `recessionCone C` and
  `((f)₀⁺).recessionCone` is `0`.

Domain-style sampling used here:
- `infimal_convolution` / `□` from Text 5.4.0;
- `exists_argmin_infimal_convolution_of_no_zero_sum_asymmetric_recession`,
  `infimal_convolution_lowerSemicontinuous_of_no_zero_sum_asymmetric_recession`, and
  `Function.IsConvex.infimal_convolution` in the Corollary 9.2.2 neighborhood;
- `indicatorFunction` from Definition 4.8.1 as the canonical `WithBotTop α` owner for the
  `0/+∞` indicator;
- `recessionCone`, object-prefix `(·).recessionCone`, and the chapter recession notation `(·)₀⁺`
  as the
  source-facing owners for recession directions of sets and functions.

Primitive data vs derived API:
- primitive inputs for the main identity: the set `C`, the function `f`, the point `x`, and the
  owner-level no-`⊥` guard `∀ y, ⊥ < f y` needed because `infimal_convolution` is computed in
  `WithBotTop α`;
- derived API: the recession-condition bridge and the attainment / lower-semicontinuity /
  convexity consequences under the closed proper convex hypotheses of the example.
- ambient-space refinement: the pointwise identity and the recession bridge use no coordinates or
  topology. The closedness/attainment consequences use the same ordered scalar-field finite-
  dimensional Hausdorff topological vector-space owner layer as Corollary 9.2.2, rather than the
  display model `EuclideanSpace ℝ (Fin n)`.
-/

section Core

section Pointwise

variable {E : Type*} [AddGroup E]
variable {α : Type*} [ConditionallyCompleteLattice α] [Add α] [Zero α]

-- Proof sketch: unfold `infimal_convolution` and split the infimum according to whether
-- `x - y ∈ -C`. This membership condition is equivalent to `y ∈ C + {x}`. The owner-level guard
-- `∀ y, ⊥ < f y` rules out the mixed `⊤ + ⊥ = ⊥` pathology in `WithBotTop α`, so the outside branch
-- simplifies to `⊤` and the remaining values are exactly the image set `f '' (C + {x})`.
/-- Example 9.2.2.2: specializing `f₁` to the `0/+∞` indicator of `-C`, the infimal convolution
`f₁ □ f` at `x` is the infimum of the values `f y` over the translate `C + {x}`. The closedness,
convexity, and nonemptiness assumptions from the prose are not needed for this pointwise identity;
the only extra hypothesis is the owner-level exclusion `∀ y, ⊥ < f y`, which prevents the
`WithBotTop α` addition pathology `⊤ + ⊥ = ⊥`. -/
theorem infimal_convolution_indicator_neg_eq_sInf_image_translate
    (C : Set E) (f : E → WithBotTop α) (hf_bot : ∀ y : E, ⊥ < f y) (x : E) :
    ((δ[α](· | -C)) □ f) x = sInf (f '' (C + {x})) := sorry

end Pointwise

section Scalar

variable {𝕜 : Type*}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]

-- Proof sketch: identify the recession function `((δ[𝕜](· | -C))₀⁺)` of the `0/+∞` indicator of
-- `-C` with the indicator of the recession cone of `-C`, rewrite that cone as `- recessionCone C`,
-- and convert the no-common-direction intersection condition into Corollary 9.2.2's primitive
-- family-kernel owner `noZeroSumAsymmetricRecession`.
/-- The example's "no common direction of recession" hypothesis implies Corollary 9.2.2's
primitive recession-kernel owner for the indicator specialization to `-C`. -/
theorem noZeroSumAsymmetricRecession_indicator_neg_of_no_common_recession_direction
    (C : Set E) (f : E → WithBotTop 𝕜)
    (hC_convex : Convex 𝕜 C)
    (hno_common :
      0⁺[𝕜]C ∩ ((f)₀⁺).recessionCone ⊆ ({0} : Set E)) :
    noZeroSumAsymmetricRecession[![(δ[𝕜](· | -C)), f]] := sorry

-- Proof sketch: `δ[𝕜](· | -C)` is convex because `-C` is convex, so the convexity clause of
-- Corollary 9.2.2 applies directly to the pair `δ[𝕜](· | -C)` and `f`.
/-- If `C` and `f` are convex, then the indicator-specialized infimal convolution from Example
9.2.2.2, equivalently the translate-infimum function `x ↦ inf {f y | y ∈ C + {x}}`, is convex. -/
theorem Function.IsConvex.indicator_neg_infimal_convolution
    {f : E → WithBotTop 𝕜} (hf_convex : f.IsConvex 𝕜)
    (C : Set E) (hC_convex : Convex 𝕜 C) :
    ((δ[𝕜](· | -C)) □ f).IsConvex 𝕜 := by
  have hindicator : (δ[𝕜](· | -C) : E → WithBotTop 𝕜).IsConvex 𝕜 :=
    (indicator_isConvex_iff (-C)).2 hC_convex.neg
  simpa using Function.IsConvex.infimal_convolution hindicator hf_convex

end Scalar

end Core

section Closed

variable {𝕜 : Type*} [Field 𝕜]
variable [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜]
variable [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type*}
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
variable [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E]
variable {C : Set E} {f : E → WithBotTop 𝕜}

-- Proof sketch: apply Corollary 9.2.2 (4) to the pair consisting of the indicator of `-C` and
-- the given closed convex function `f`, using the previous bridge theorem to supply the recession
-- kernel hypothesis and the pointwise assumption `∀ x, ⊥ < f x` for the only function-side
-- exclusion of `-∞` needed by the owner theorem. Then rewrite the minimizing point into membership
-- of the translate `C + {x}` via the identity theorem above.
/-- Under the example's recession hypothesis, the infimum of `f` over each translate `C + {x}` is
attained. -/
theorem exists_mem_translate_eq_infimal_convolution_of_no_common_recession_direction
    (hC_closed : IsClosed C)
    (hC_convex : Convex 𝕜 C)
    (hno_common :
      0⁺[𝕜]C ∩ ((f)₀⁺).recessionCone ⊆ ({0} : Set E))
    (hC_nonempty : C.Nonempty)
    (hf_convex : f.IsConvex 𝕜)
    (hf_bot : ∀ x : E, ⊥ < f x)
    (hf_closed : LowerSemicontinuous f)
    (x : E) :
    ∃ y ∈ C + {x},
      ((δ[𝕜](· | -C)) □ f) x = f y := sorry

-- Proof sketch: first obtain the corollary's recession-kernel hypothesis from the previous
-- bridge theorem. Then specialize Corollary 9.2.2 (1) to the indicator of `-C`; here the only
-- function-side side condition beyond convexity and lower semicontinuity is the pointwise
-- exclusion `∀ x, ⊥ < f x`, so the unused nonemptiness/properness binders are removed.
/-- Under the example's recession hypothesis, the function `x ↦ inf_{y ∈ C + {x}} f y` is lower
semicontinuous, expressed through the canonical infimal convolution with the indicator of `-C`. -/
theorem indicator_neg_infimal_convolution_lowerSemicontinuous_of_no_common_recession_direction
    (hC_closed : IsClosed C)
    (hC_convex : Convex 𝕜 C)
    (hno_common :
      0⁺[𝕜]C ∩ ((f)₀⁺).recessionCone ⊆ ({0} : Set E))
    (hf_convex : f.IsConvex 𝕜)
    (hf_bot : ∀ x : E, ⊥ < f x)
    (hf_closed : LowerSemicontinuous f) :
    LowerSemicontinuous ((δ[𝕜](· | -C)) □ f) := sorry

end Closed
