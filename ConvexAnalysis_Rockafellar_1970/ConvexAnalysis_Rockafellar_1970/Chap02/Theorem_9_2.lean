import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_7
import ConvexAnalysis_Rockafellar_1970.Chap02.Definiton_8_5_0
import ConvexAnalysis_Rockafellar_1970.Chap02.Corollary_8_5_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Rockafellar

section

variable {𝕜 α : Type*} {E F : Type*}
variable [Semiring 𝕜]
variable [AddGroup α] [ConditionallyCompleteLattice α]
variable [AddCommGroup E] [Module 𝕜 E]
variable [AddCommMonoid F] [Module 𝕜 F]

namespace LinearMap

/-- The recession-kernel side condition in Theorem 9.2: no direction `z` with
`z ∈ Function.recessionCone ((h)₀⁺)` and `0 < ((h)₀⁺) (-z)` lies in the kernel of `A`. -/
def noAsymmetricRecessionKernel (A : E →ₗ[𝕜] F) (h : E → WithTopBot α) : Prop :=
  ∀ z : E, z ∈ Function.recessionCone ((h)₀⁺) → 0 < ((h)₀⁺) (-z) → z ∉ A.ker

end LinearMap

end

section Convexity

variable {𝕜 : Type*} {E F : Type*}
variable [Semiring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [NoBotOrder 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]
variable [AddCommMonoid F] [Module 𝕜 F]

variable (A : E →ₗ[𝕜] F) (h : E → WithTopBot 𝕜)

/- Theorem 9.2 (2): the convexity clause is already the chapter owner theorem
`Function.isConvex_linearImage`, so this file recalls that canonical result directly instead
of keeping a parallel exact-interface wrapper. -/
recall Function.isConvex_linearImage

end Convexity

section

variable
    {𝕜 : Type*} [Field 𝕜] [TopologicalSpace 𝕜]
    [ConditionallyCompleteLinearOrder 𝕜] [OrderTopology 𝕜]
    [IsStrictOrderedRing 𝕜]
    {E F : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E]
    [TopologicalSpace F] [AddCommGroup F] [Module 𝕜 F]
    [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] [T2Space F]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 9.2 studies the image function `Ah` of a closed convex function `h`
  under a linear map `A`, with an additional recession-kernel hypothesis. The file keeps the
  source clauses split by their actual hypotheses: closedness, convexity, and attainment need only
  convexity plus lower semicontinuity, while properness of `h` is added only for the properness
  and recession-function clauses.
- `core/canonical`: the chapter owner abstractions already present are `Function.linearImage A h`
  for `Ah`, `recessionFunction h` for `(h)₀⁺`, `h.IsConvex`, `h.IsProper`, and
  `LowerSemicontinuous`.
- `bridge/view`: the theorem's epigraph argument runs through `linearImageEpigraph A h`, while
  the textbook notation `A((h)₀⁺)` is rendered canonically as `Function.linearImage A
  (recessionFunction h)`.

Domain-style sampling used here:
- `Function.linearImage` and `Function.linearImage_eq_sInf_image`;
- `linearImageEpigraph` together with
  `Function.linearImage_attains_of_closed_imageEpigraph_of_ne_bot_of_mem_dom`;
- `recessionFunction`;
- `Function.isConvex_linearImage`.
- ambient-space refinement: the convexity owner `Function.linearImage` already lives on arbitrary
  scalar modules, while the closed-image, lower-semicontinuity, properness, recession, and
  attainment clauses pass through the closed-image epigraph route from Theorem 9.1 and therefore
  need the finite-dimensional Hausdorff topological-vector-space source together with a
  Hausdorff topological-vector-space target over the same ordered scalar field. Equivalently, the
  proof route needs `F × 𝕜`
  Hausdorff when identifying the closed image epigraph with `epi (A ◁ h)`. The Euclidean
  `R^n → R^m` presentation is therefore demoted to the `𝕜 = ℝ` specialization instead of remaining
  the
  public owner layer.

Primitive data vs derived API:
- primitive inputs: the linear map `A`, the function `h`, its convexity and closedness
  hypotheses, and the source-visible recession-kernel owner
  `A.noAsymmetricRecessionKernel h`;
- derived API: lower semicontinuity, convexity, the attainment statement for
  `Function.linearImage A h`, and, once properness of `h` is added, properness and the
  recession-image formula for `Ah`.

Layer target: this item stays `source-facing`, but it is written directly in terms of the chapter's
canonical owners `Function.linearImage` and `recessionFunction` rather than introducing a second
wrapper for Rockafellar's notation `Ah`.
-/

-- Proof sketch: apply Theorem 9.1 to the scalar epigraph of `h` and the linear map
-- `(x, μ) ↦ (A x, μ)`. Convexity and closedness of the epigraph come from `hh_convex` and
-- `hh_closed`, and the recession-kernel hypothesis translates the source condition into the
-- exclusion of downward vertical recession directions in the image epigraph. The resulting closed
-- image epigraph is exactly the epigraph of `Function.linearImage A h`.
variable (A : E →ₗ[𝕜] F) (h : E → WithTopBot 𝕜)

/-- Theorem 9.2 (1): under the stated recession-kernel hypothesis, the image function `Ah` is
closed, expressed here by lower semicontinuity of `Function.linearImage A h`. -/
theorem linearImage_lowerSemicontinuous_of_no_asymmetric_recession_kernel
    (hh_convex : h.IsConvex 𝕜) (hh_closed : LowerSemicontinuous h)
    (hkernel : A.noAsymmetricRecessionKernel h)
    :
    LowerSemicontinuous (A ◁ h) := sorry

-- Proof sketch: choose `x` with `h x < ⊤` using properness of `h`; then
-- `Function.linearImage A h (A x) ≤ h x < ⊤`, so `Ah` is somewhere finite. The closed-image
-- argument from part (1) rules out downward vertical lines in the image epigraph, hence every
-- value of `Ah` is strictly above `⊥`. Using the chapter characterization of properness gives the
-- conclusion.
/-- Theorem 9.2 (3): under the same hypotheses, the image function `Ah` is proper. -/
theorem linearImage_isProper_of_no_asymmetric_recession_kernel
    (hh_convex : h.IsConvex 𝕜) (hh_closed : LowerSemicontinuous h)
    (hkernel : A.noAsymmetricRecessionKernel h)
    (hh_proper : h.IsProper)
    :
    (A ◁ h).IsProper := sorry

-- Proof sketch: apply the recession-cone image formula from Theorem 9.1 to the scalar epigraph of
-- `h` under `(x, μ) ↦ (A x, μ)`. Identify the recession cone of `epi h` with the epigraph of
-- `(h)₀⁺` and the recession cone of `epi (Ah)` with the epigraph of `(Function.linearImage A h)₀⁺`.
-- Comparing the two epigraphs yields the stated
-- equality of recession functions.
/-- Theorem 9.2 (4): the recession function of `Ah` is the image under `A` of the recession
function of `h`, i.e. `(Ah)₀⁺ = A((h)₀⁺)`. -/
theorem
    recessionFunction_linearImage_eq_linearImage_recessionFunction_of_no_asymmetric_recession_kernel
    (hh_convex : h.IsConvex 𝕜) (hh_closed : LowerSemicontinuous h)
    (hkernel : A.noAsymmetricRecessionKernel h)
    (hh_proper : h.IsProper)
    :
    (A ◁ h)₀⁺ = (A ◁ ((h)₀⁺)) := sorry

-- Proof sketch: if `y ∈ dom(A ◁ h)`, then the vertical section of the image
-- epigraph above `y` is nonempty. Use `hh_convex` to make `linearImageEpigraph A h` convex,
-- combine the closedness from part (1) with the downward recession exclusion encoded by
-- `hkernel`, then apply
-- `Function.linearImage_attains_of_closed_imageEpigraph_of_ne_bot_of_mem_dom` to obtain a
-- fiber point `x` with `A x = y` and `h x = Function.linearImage A h y`.
/-- Theorem 9.2 (5): for every `y` in the effective domain of `Ah`, the infimum defining `Ah(y)`
is attained by some `x` in the fiber `A x = y`. -/
theorem exists_preimage_eq_linearImage_of_mem_dom_of_no_asymmetric_recession_kernel
    (hh_convex : h.IsConvex 𝕜) (hh_closed : LowerSemicontinuous h)
    (hkernel : A.noAsymmetricRecessionKernel h)
    (y : F) (hy : y ∈ dom(A ◁ h)) :
    ∃ x : E, A x = y ∧ h x = (A ◁ h) y := sorry

end

end
