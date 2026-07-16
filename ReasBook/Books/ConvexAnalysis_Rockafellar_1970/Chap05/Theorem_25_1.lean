import Mathlib.Analysis.Calculus.Gradient.Basic
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_8
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_25_1
import ConvexAnalysis_Rockafellar_1970.Chap05.Lemma_23_0_4
import ConvexAnalysis_Rockafellar_1970.Chap05.Theorem_23_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Gradient RealInnerProductSpace Rockafellar

universe u v

section

variable {𝕜 : Type v}
variable [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {U : Set E} {f : E → 𝕜}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 25.1 identifies the Fréchet derivative of a differentiable convex
  scalar-valued function at an interior point of a convex set with the unique subgradient of its
  canonical extension by `+∞` outside the domain, then records the supporting-hyperplane
  inequality on the domain.
- `core/canonical`: the primitive owner is
  `∂ᵣf(x | U) : Set (StrongDual 𝕜 E)` from Definition 25.1, and the
  derivative-side primitive data are `HasFDerivAt` / `fderiv`.
- `bridge/view`: gradient and inner-product formulations are Euclidean companion views obtained
  from the canonical dual owner through Fréchet-Riesz.

Domain-style sampling used here:
- `isConvex_toWithBotTopOn_iff` from `Chap01.Remark_4_4_5`;
- `∂ᵣf(x | U)` from `Chap05.Definition_25_1`;
- `_root_.mem_subdifferentialAt_iff_le_directionalDerivativeAt` from `Chap05.Theorem_23_2`;
- `Function.directionalDerivativeAt_toWithTopBot_eq_fderiv_apply_of_hasFDerivAt` from
  `Chap05.Lemma_23_0_4`.

Primitive data vs derived API:
- primitive source data: the convex set `U`, the scalar-valued branch `f`, its convexity on
  `U`, pointwise differentiability/Fréchet differentiability at `x`, and a base point
  `x ∈ ri[𝕜](U)`;
- primitive owner surface: `∂ᵣf(x | U)`;
- derived API: singleton descriptions by `fderiv 𝕜` and by the Euclidean gradient, supporting
  inequalities, and the finite-dimensional converse under uniqueness of the owner subdifferential.

Layer target:
- `subdifferentialWithinAt_eq_singleton_fderiv`: `core/canonical`;
- `fderiv_affine_le`: `core/canonical`;
- gradient forms below: `bridge/view`.

Ambient-assumption minimization:
- the canonical owner statements below avoid inner-product/completeness assumptions;
- the gradient forms are kept as Euclidean bridges in the next section.
-/

namespace Function

-- Proof sketch: rewrite `∂ᵣf(x | U)` through the canonical extension
-- `Function.toWithBotTopOn f U`, use convexity of that extension via
-- `isConvex_toWithBotTopOn_iff`, identify its directional derivative by
-- `directionalDerivativeAt_toWithTopBot_eq_fderiv_apply_of_hasFDerivAt`, and apply
-- `_root_.mem_subdifferentialAt_iff_le_directionalDerivativeAt` to obtain the singleton owner.
/-- Theorem 25.1, canonical owner form: for a convex scalar-valued function on `U`, Fréchet
differentiability at a relative-interior point forces the relative subdifferential owner to be the
singleton containing that Fréchet derivative. -/
theorem subdifferentialWithinAt_eq_singleton_fderiv
    (hf_convex : ConvexOn 𝕜 U f) {x : E} (hx : x ∈ ri[𝕜](U)) {f' : E →L[𝕜] 𝕜}
    (hfdx : HasFDerivAt f f' x) :
    ∂ᵣf(x | U) = {f'} := by
  sorry

-- Proof sketch: extract the unique owner subgradient `fderiv 𝕜 f x` from the previous theorem and
-- evaluate the defining support inequality at `z ∈ U`.
/-- Theorem 25.1, canonical affine-support companion: at a relative-interior differentiability point of a
convex scalar-valued branch, the affine functional defined by `fderiv 𝕜 f x` supports `f` on `U`. -/
theorem fderiv_affine_le
    (hf_convex : ConvexOn 𝕜 U f) {x : E} (hx : x ∈ ri[𝕜](U))
    (hfdx : DifferentiableAt 𝕜 f x) {z : E} (hz : z ∈ U) :
    f x + fderiv 𝕜 f x (z - x) ≤ f z := by
  sorry

end Function

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {U : Set E} {f : E → ℝ}

namespace Function

-- Proof sketch: specialize the canonical owner theorem
-- `subdifferentialWithinAt_eq_singleton_fderiv` to `f' = fderiv ℝ f x`, then transport across
-- the Fréchet-Riesz bridge from `StrongDual` to vectors.
/-- Theorem 25.1, canonical dual-owner Euclidean form: for a convex real-valued branch
differentiable at a relative-interior point, the relative dual-valued owner subdifferential is the
singleton containing `InnerProductSpace.toDual ℝ E (∇ f x)`. -/
theorem subdifferentialWithinAt_eq_singleton_toDual_gradient
    (hf_convex : ConvexOn ℝ U f) {x : E} (hx : x ∈ ri[ℝ](U))
    (hfdx : DifferentiableAt ℝ f x) :
    ∂ᵣf(x | U) = {InnerProductSpace.toDual ℝ E (∇ f x)} := by
  sorry

-- Proof sketch: rewrite the Euclidean bridge owner `∂ᵥᵣf(x | U)` as the preimage of
-- `∂ᵣf(x | U)` under `InnerProductSpace.toDualMap`, then use
-- `subdifferentialWithinAt_eq_singleton_toDual_gradient`.
/-- Theorem 25.1, Euclidean bridge owner form: for a convex real-valued function on `U`
differentiable at a relative-interior point `x`, the vector-valued bridge owner
`∂ᵥᵣf(x | U)` is the singleton `{∇ f x}`. -/
theorem subdifferentialWithinAt_eq_singleton_gradient
    (hf_convex : ConvexOn ℝ U f) {x : E} (hx : x ∈ ri[ℝ](U))
    (hfdx : DifferentiableAt ℝ f x) :
    ∂ᵥᵣf(x | U) = {∇ f x} := by
  sorry

-- Proof sketch: either transport `fderiv_affine_le` through Fréchet-Riesz or read off membership
-- of `∇ f x` from the singleton bridge theorem and unfold `mem_subdifferentialWithinAt`.
/-- Theorem 25.1, source-facing Euclidean companion: on a convex set, a real-valued function
differentiable at a relative-interior point `x ∈ ri[ℝ](U)` lies above the affine support determined by
its gradient at every comparison point of the domain. -/
theorem gradient_affine_le
    (hf_convex : ConvexOn ℝ U f) {x z : E} (hx : x ∈ ri[ℝ](U))
    (hfdx : DifferentiableAt ℝ f x) (hz : z ∈ U) :
    f x + ⟪∇ f x, z - x⟫ ≤ f z := by
  sorry

end Function

end

section

variable {𝕜 : Type v}
variable [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {U : Set E} {f : E → 𝕜}

namespace Function

-- Proof sketch: uniqueness of the canonical dual-valued owner
-- `∂ᵣf(x | U)` forces first-order support data to be linear in
-- direction; in finite-dimensional normed spaces this upgrades to differentiability of `f`
-- at `x`.
/-- Theorem 25.1, canonical finite-dimensional converse: if the canonical dual-valued relative
subdifferential owner of a convex scalar-valued branch is singleton at a relative-interior point, then the
branch is differentiable there. -/
theorem differentiableAt_of_existsUnique_mem_subdifferentialWithinAt
    (hf_convex : ConvexOn 𝕜 U f) {x : E} (hx : x ∈ ri[𝕜](U))
    (hsub : ∃! xStar : StrongDual 𝕜 E, xStar ∈ ∂ᵣf(x | U)) :
    DifferentiableAt 𝕜 f x := by
  sorry

end Function

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {U : Set E} {f : E → ℝ}

namespace Function

-- Proof sketch: uniqueness of `∂ᵥᵣf(x | U)` forces the Chapter 23 directional
-- derivative map of `Function.toWithBotTopOn f U` at `x` to be linear in the direction variable.
-- In finite dimensions, Rockafellar's
-- converse argument upgrades that linear first-order support data to differentiability of the
-- real-valued branch `f` at the interior point `x`.
/-- Theorem 25.1, Euclidean bridge converse: if the vector-valued bridge owner
`∂ᵥᵣf(x | U)` is singleton at a relative-interior point, then `f` is
differentiable there. -/
theorem differentiableAt_of_existsUnique_mem_subdifferentialWithinAt_vector
    (hf_convex : ConvexOn ℝ U f) {x : E} (hx : x ∈ ri[ℝ](U))
    (hsub : ∃! g : E, g ∈ ∂ᵥᵣf(x | U)) :
    DifferentiableAt ℝ f x := by
  sorry

end Function

end
