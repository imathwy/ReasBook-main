import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_2
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_7_0_4
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_8_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open scoped Rockafellar

noncomputable section

universe u

section Closedness

variable {E : Type*} [TopologicalSpace E]

/- Theorem 9.3 (1): if every summand is closed, then the finite pointwise sum is closed,
expressed by lower semicontinuity. This is the owner theorem `lowerSemicontinuous_sum`
at the canonical `Finset` layer. -/
recall lowerSemicontinuous_sum

end Closedness

section Convexity

variable {𝕜 : Type*} [Ring 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type*} [AddCommMonoid E] [SMul 𝕜 E]

/- Theorem 9.3 (2): a finite sum of proper convex functions is convex. This is the owner
finite-sum bridge `Function.isConvex_sum_of_bot_lt`; properness is used only through
`Function.IsProper.bot_lt`. -/
recall Function.isConvex_sum_of_bot_lt

end Convexity

section Properness

/- Theorem 9.3 (3): the properness clause is exactly the owner theorem
`Function.isProper_sum_of_exists_lt_top`, so no parallel local wrapper is kept here. -/
recall Function.isProper_sum_of_exists_lt_top

end Properness

section Recession

variable {ι : Type u}
variable [Fintype ι]
variable {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
variable {α : Type*}
variable [AddCommGroup α] [SMul 𝕜 α] [ConditionallyCompleteLinearOrder α] [TopologicalSpace α]
variable {E : Type*} [AddCommMonoid E] [SMul 𝕜 E] [TopologicalSpace E]

namespace Function

/- Theorem 9.3 (4) is stated at the canonical recession layer with scalar/codomain split:
the scalar for convexity is `𝕜`, while values live in `WithTopBot α`, and finite indexing is
exposed through `[Fintype ι]` rather than `Finset` membership side conditions. -/
variable (f : ι → E → WithTopBot α)

/-- Theorem 9.3 (4): for closed convex summands that are everywhere strictly above `⊥` and whose
finite sum is finite at some point, the recession
function of the finite sum is the finite sum of the recession functions. -/
-- Proof sketch: Theorem 8.5 gives the limit formula for the recession function of each closed
-- convex summand and of the total sum. The primitive pointwise `⊥`-exclusion hypothesis supplies
-- the non-`⊥` codomain side condition directly, while the finite-point hypothesis gives a common
-- base point in the effective domains. Evaluate those formulas at that base point and pass the
-- finite sum through the limit expression.
theorem recessionFunction_sum_eq_sum_recessionFunction
    (hf_bot : ∀ i, ∀ x : E, (⊥ : WithTopBot α) < f i x)
    (hf_convex : ∀ i, (f i).IsConvex 𝕜)
    (hf_closed : ∀ i, LowerSemicontinuous (f i))
    (hsum_finite : ∃ x : E, (∑ i, f i x) < (⊤ : WithTopBot α)) :
    (∑ i, f i)₀⁺ = ∑ i, (f i)₀⁺ := sorry

end Function

end Recession

section LowerSemicontinuousHull

variable {ι : Type u}
variable [Fintype ι]
variable
    {𝕜 : Type*}
    [Field 𝕜] [LinearOrder 𝕜] [TopologicalSpace 𝕜]
    [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜]
variable
    {α : Type*}
    [AddCommMonoid α] [SMul 𝕜 α] [ConditionallyCompleteLinearOrder α] [TopologicalSpace α]
variable
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E]

namespace Function

variable (f : ι → E → WithTopBot α)

/-- Theorem 9.3 (5): if the relative interiors of the effective domains of the summands have a
common point, then the closure of the finite sum is the finite sum of the closures, written with
the chapter notation `cl(·)`. The statement is at the scalar/codomain-split layer:
the scalar for convexity is `𝕜`, while values live in `WithTopBot α`, and the ambient primal space
is only a finite-dimensional Hausdorff topological `𝕜`-module (no normed-space structure is part
of the theorem surface). -/
-- Proof sketch: by Theorem 6.5 the common-point hypothesis identifies the relative interior of
-- the effective domain of the total sum with the intersection of the relative interiors
-- `riDom[𝕜](f i)` of the summand domains. A closure-comparison bridge based on relative-interior
-- domain agreement and agreement on that intrinsic domain then identifies `cl(∑ i, f i)` with
-- `∑ i, cl(f i)`.
theorem lowerSemicontinuousHull_sum_eq_sum_of_nonempty_iInter_riDom
    (hf_convex : ∀ i, (f i).IsConvex 𝕜)
    (hri : (⋂ i, riDom[𝕜](f i)).Nonempty) :
    cl(∑ i, f i) = ∑ i, cl(f i) := sorry

end Function

end LowerSemicontinuousHull
