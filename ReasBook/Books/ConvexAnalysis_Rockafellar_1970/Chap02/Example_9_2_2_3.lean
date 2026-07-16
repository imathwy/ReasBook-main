import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_5_13
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_3_1_1
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_4_0
import ConvexAnalysis_Rockafellar_1970.Chap02.Example_9_2_2_2
import ConvexAnalysis_Rockafellar_1970.Chap02.Corollary_9_2_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

attribute [local instance] Classical.propDecidable

section OrderCore

open scoped Rockafellar

variable {X : Type*} [Preorder X]
variable {α : Type*} [CompleteSemilatticeInf α]

/-!
Source/core/bridge triage for this item.

- `source-facing`: the example studies the function `g(x) = inf {f(y) | y ≥ x}` obtained by
  taking infima over order-upper sets.
- `core/canonical`: the owner abstractions already present in the project are the positive-cone
  owner `(ConvexCone.positive 𝕜 E : Set E)`, the order-upper-closure owner `upperClosure`, and the
  generic indicator-specialized infimal-convolution API from Example 9.2.2.2.
- `bridge/view`: the orthant upper set above `x` is rendered as `{y | y ≥ x}` and identified with
  the singleton specialization of `upperClosure_eq_add_orthant`; the source function
  `g` is then
  connected to the owner-side indicator infimal convolution by a thin specialization to
  `C = (ConvexCone.positive 𝕜 E : Set E)`.

Domain-style sampling used here:
- `ConvexCone.positive`;
- `upperClosure_eq_add_orthant`;
- `indicator` / `δ[α](· | C)`;
- `infimal_convolution_indicator_neg_eq_sInf_image_translate`;
- `Monotone`.

Primitive data vs derived API:
- primitive source-facing data: only `orthantInfimumMinorant`, defined through the canonical owner
  `upperClosure ({x} : Set X)`;
- derived API: the set-builder formula `{y | y ≥ x}`, the orthant-translate bridge, the
  indicator-infimal-convolution bridge under the owner-level no-`⊥` guard `∀ y, ⊥ < f y`,
  attainment, lower semicontinuity, properness, convexity, and the greatest-minorant property.

Layer target: this item stays `source-facing`. The public object remains the textbook minorant
`g(x) = inf {f(y) | y ≥ x}`, but its support lemmas and downstream statements reuse the chapter's
orthant owners instead of parallel local wrappers.
-/

/-- The function `g(x) = inf {f(y) | y ≥ x}` obtained by taking the infimum of `f` over the
orthant upper set above `x`. -/
def orthantInfimumMinorant (f : X → α) : X → α :=
  fun x ↦ sInf (f '' upperClosure ({x} : Set X))

private theorem upperClosure_singleton_eq_orthantUpperSet (x : X) :
    (upperClosure ({x} : Set X) : Set X) = {y : X | y ≥ x} := by
  ext y
  rw [upperClosure_singleton]
  simp [ge_iff_le]

/-- The defining formula for `orthantInfimumMinorant` is the infimum of `f` over the orthant upper
set above `x`. -/
theorem orthantInfimumMinorant_eq_sInf_image (f : X → α) (x : X) :
    orthantInfimumMinorant f x = sInf (f '' {y : X | y ≥ x}) :=
  by rw [orthantInfimumMinorant, upperClosure_singleton_eq_orthantUpperSet]

-- Proof sketch: the point `x` itself satisfies `x ≥ x`, so
-- `orthantInfimumMinorant f x ≤ f x`. If `h ≤ f` is monotone for `≥` and `y ≥ x`,
-- then `h x ≤ h y ≤ f y`; taking the infimum over all such `y` gives
-- `h x ≤ orthantInfimumMinorant f x`. Monotonicity of `orthantInfimumMinorant f` is kept in the
-- canonical order-theoretic owner form `Monotone`, and follows from inclusion of orthant upper
-- sets under `≥`.
/-- Example 9.2.2.3 in its order-theoretic owner form: `orthantInfimumMinorant f` is the greatest
minorant of `f` that is nondecreasing for the ambient order, canonically expressed as
`Monotone`. -/
theorem orthantInfimumMinorant_isGreatest_orthantMonotone_minorant
    (f : X → α) :
    IsGreatest
      {h : X → α | h ≤ f ∧ Monotone h}
      (orthantInfimumMinorant f) := sorry

end OrderCore

section OrthantOrderedModulePointwise

open scoped Pointwise Rockafellar

variable {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
variable {E : Type*} [AddCommGroup E] [PartialOrder E]
  [IsOrderedAddMonoid E] [Module 𝕜 E] [PosSMulMono 𝕜 E]
variable {α : Type*} [ConditionallyCompleteLattice α] [Add α] [Zero α]

local notation "E≥0" => (ConvexCone.positive 𝕜 E : Set E)

private theorem orthantUpperSet_eq_translate_nonnegativeOrthant (x : E) :
    {y : E | y ≥ x} = E≥0 + ({x} : Set E) := by
  calc
    {y : E | y ≥ x} = (upperClosure ({x} : Set E) : Set E) := by
      rw [upperClosure_singleton_eq_orthantUpperSet x]
    _ = ({x} : Set E) + E≥0 :=
      upperClosure_eq_add_orthant ({x} : Set E)
    _ = E≥0 + ({x} : Set E) := by rw [add_comm]

-- Proof sketch: specialize Example 9.2.2.2 to `C = E≥0`, using the
-- no-`⊥` guard on `f` needed by the `WithBotTop α` owner `infimal_convolution`, and then rewrite
-- the resulting
-- translate-infimum
-- formula using the private orthant-translate identification above and the canonical
-- `WithBotTop α`-valued indicator owner `indicatorFunction`.
/-- `orthantInfimumMinorant f` is the specialization of the canonical indicator infimal
convolution from Example 9.2.2.2 to the nonnegative orthant. As in that owner bridge, the
pointwise exclusion `∀ y, ⊥ < f y` is needed to avoid the mixed `⊤ + ⊥ = ⊥` branch of
`WithBotTop α` addition. -/
theorem orthantInfimumMinorant_eq_infimal_convolution_indicator_neg
    (f : E → WithBotTop α) (hf_bot : ∀ y : E, ⊥ < f y) :
    orthantInfimumMinorant f =
      ((δ[α](· | -E≥0)) □ f) := by
  sorry

end OrthantOrderedModulePointwise

section OrthantOrderedModuleClosed

open scoped Pointwise Rockafellar

variable {𝕜 : Type*} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type*}
variable [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module 𝕜 E] [PosSMulMono 𝕜 E]

local notation "E≥0" => (ConvexCone.positive 𝕜 E : Set E)

section Ambient

variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [T2Space E] [FiniteDimensional 𝕜 E]

-- Proof sketch: specialize the attainment clause of Example 9.2.2.2 to `C = E≥0`.
-- The resulting minimizing point lies in `E≥0 + ({x} : Set E)`, which is exactly the relation
-- `y ≥ x`.
/-- The infimum defining `orthantInfimumMinorant f x` is attained whenever the recession function
`(f)₀⁺` is strictly positive on every nonzero vector of the nonnegative orthant `E≥0`. -/
theorem exists_argmin_orthantInfimumMinorant_of_positive_recession_on_nonnegative
    (f : E → WithBotTop 𝕜)
    (hf_convex : f.IsConvex 𝕜)
    (hf_bot : ∀ x : E, ⊥ < f x)
    (hf_closed : LowerSemicontinuous f)
    (hrecession :
      ∀ z : E, z ≠ 0 → z ∈ E≥0 → 0 < ((f)₀⁺) z)
    (x : E) :
    ∃ y : E, y ≥ x ∧ orthantInfimumMinorant f x = f y := sorry

-- Proof sketch: identify `orthantInfimumMinorant f` with the orthant-indicator infimal
-- convolution and specialize the lower-semicontinuity clause from Example 9.2.2.2. As in the
-- upstream owner theorem, the only function-side exclusion of `-∞` needed here is the pointwise
-- hypothesis `∀ x, ⊥ < f x`.
/-- Under the same orthant recession hypothesis, `orthantInfimumMinorant f` is closed, expressed
as lower semicontinuity. -/
theorem orthantInfimumMinorant_lowerSemicontinuous_of_positive_recession_on_nonnegative
    (f : E → WithBotTop 𝕜)
    (hf_convex : f.IsConvex 𝕜)
    (hf_bot : ∀ x : E, ⊥ < f x)
    (hf_closed : LowerSemicontinuous f)
    (hrecession :
      ∀ z : E, z ≠ 0 → z ∈ E≥0 → 0 < ((f)₀⁺) z) :
    LowerSemicontinuous (orthantInfimumMinorant f) := sorry

-- Proof sketch: apply the properness clause of Corollary 9.2.2 to the pair consisting of `f` and
-- the `0/+∞` indicator of `-E≥0`, then rewrite the resulting
-- infimal convolution
-- as `orthantInfimumMinorant f`.
/-- Under the same orthant recession hypothesis, `orthantInfimumMinorant f` is proper. -/
theorem orthantInfimumMinorant_isProper_of_positive_recession_on_nonnegative
    (f : E → WithBotTop 𝕜)
    (hf_convex : f.IsConvex 𝕜)
    (hf_proper : f.IsProper)
    (hf_closed : LowerSemicontinuous f)
    (hrecession :
      ∀ z : E, z ≠ 0 → z ∈ E≥0 → 0 < ((f)₀⁺) z) :
    (orthantInfimumMinorant f).IsProper := sorry

end Ambient

end OrthantOrderedModuleClosed

section OrthantOrderedModuleConvex

open scoped Pointwise Rockafellar

variable {𝕜 : Type*} [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜]
variable {E : Type*} [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]
  [Module 𝕜 E] [PosSMulMono 𝕜 E]

local notation "E≥0" => (ConvexCone.positive 𝕜 E : Set E)

-- Proof sketch: rewrite `orthantInfimumMinorant f` through the canonical owner bridge above, note
-- that `E≥0` is convex, and then apply the generic
-- indicator-specialized
-- convexity theorem. Unlike the closedness and properness clauses, this conclusion only uses the
-- convexity of `f`.
/-- If `f` is convex, then `orthantInfimumMinorant f` is convex. -/
theorem orthantInfimumMinorant_isConvex
    (f : E → WithBotTop 𝕜)
    (hf_convex : f.IsConvex 𝕜) :
    (orthantInfimumMinorant f).IsConvex 𝕜 := by
  sorry

end OrthantOrderedModuleConvex
