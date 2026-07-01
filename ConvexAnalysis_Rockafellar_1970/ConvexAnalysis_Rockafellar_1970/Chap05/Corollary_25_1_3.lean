import ConvexAnalysis_Rockafellar_1970.Chap05.Theorem_25_1

noncomputable section

open scoped Gradient RealInnerProductSpace Rockafellar

universe u

section

variable {𝕜 : Type*}
variable [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {U : Set E} {f : E → 𝕜}

/-!
Source/core/bridge triage for this item.

- `core/canonical`: this file is anchored at the intrinsic/relative owner surface:
  `x ∈ ri[𝕜](U)` together with pointwise differentiability at `x` yields
  `∂ᵣf(x | U) = {fderiv 𝕜 f x}`.
- `core/canonical`: the relative-global differentiability surface
  (`DifferentiableOn 𝕜 f (ri[𝕜](U))`, `x ∈ ri[𝕜](U)`) is provided as the intrinsic
  global API.
- `source-facing`: the textbook interior form (`DifferentiableOn 𝕜 f (interior U)`,
  `x ∈ interior U`) is kept as a bridge wrapper.
- `bridge/view`: Euclidean gradient and `toDual` forms are recorded in the next section.

Domain-style sampling used here:
- `∂ᵣf(x | U)` and membership in that owner from `Definition_25_1`;
- `Function.subdifferentialWithinAt_eq_singleton_fderiv` from `Theorem_25_1`.

Primitive data vs derived API:
- primitive source data: `U`, `f`, convexity of `f` on `U`, relative base-point membership
  `x ∈ ri[𝕜](U)`, and pointwise differentiability at `x`.
- primary owner statement: singleton description by `fderiv 𝕜 f x`.
- bridge views: interior wrappers and Euclidean singleton/membership/nonemptiness forms below.

Layer target:
- `subdifferentialWithinAt_eq_singleton_fderiv_of_mem_intrinsicInterior`:
  `core/canonical`;
- `mem_subdifferentialWithinAt_iff_eq_fderiv_of_mem_intrinsicInterior`: `core/canonical`;
- `subdifferentialWithinAt_nonempty_of_mem_intrinsicInterior`: `core/canonical`;
- `subdifferentialWithinAt_eq_singleton_fderiv_of_differentiableOnIntrinsicInterior`:
  `core/canonical`;
- `mem_subdifferentialWithinAt_iff_eq_fderiv_of_differentiableOnIntrinsicInterior`:
  `core/canonical`;
- `subdifferentialWithinAt_nonempty_of_differentiableOnIntrinsicInterior`:
  `core/canonical`;
- `subdifferentialWithinAt_eq_singleton_fderiv_of_differentiableOnInterior`:
  `source-facing/bridge`;
- `mem_subdifferentialWithinAt_iff_eq_fderiv_of_differentiableOnInterior`:
  `source-facing/bridge`;
- `subdifferentialWithinAt_nonempty_of_differentiableOnInterior`: `source-facing/bridge`;
- Euclidean gradient/toDual statements below: `bridge/view`.
-/

/-- Corollary 25.1.3, intrinsic canonical owner form: at a relative-interior point where `f` is
differentiable, the relative subdifferential is the singleton containing the Fréchet derivative. -/
theorem subdifferentialWithinAt_eq_singleton_fderiv_of_mem_intrinsicInterior
    (hf_convex : ConvexOn 𝕜 U f) {x : E} (hx : x ∈ ri[𝕜](U))
    (hfdx : DifferentiableAt 𝕜 f x) :
    ∂ᵣf(x | U) = {fderiv 𝕜 f x} := by
  simpa using
    (Function.subdifferentialWithinAt_eq_singleton_fderiv
      hf_convex hx hfdx.hasFDerivAt)

/-- Pointwise membership form on the intrinsic canonical owner surface. -/
theorem mem_subdifferentialWithinAt_iff_eq_fderiv_of_mem_intrinsicInterior
    (hf_convex : ConvexOn 𝕜 U f) {x : E} {xStar : StrongDual 𝕜 E}
    (hx : x ∈ ri[𝕜](U)) (hfdx : DifferentiableAt 𝕜 f x) :
    xStar ∈ ∂ᵣf(x | U) ↔ xStar = fderiv 𝕜 f x := by
  rw [subdifferentialWithinAt_eq_singleton_fderiv_of_mem_intrinsicInterior
    hf_convex hx hfdx, Set.mem_singleton_iff]

/-- Nonemptiness form on the intrinsic canonical owner surface. -/
theorem subdifferentialWithinAt_nonempty_of_mem_intrinsicInterior
    (hf_convex : ConvexOn 𝕜 U f) {x : E} (hx : x ∈ ri[𝕜](U))
    (hfdx : DifferentiableAt 𝕜 f x) :
    (∂ᵣf(x | U)).Nonempty := by
  rw [subdifferentialWithinAt_eq_singleton_fderiv_of_mem_intrinsicInterior hf_convex hx hfdx]
  exact Set.singleton_nonempty (fderiv 𝕜 f x)

/-- Corollary 25.1.3, intrinsic global owner form: differentiability of `f` on `ri[𝕜](U)` makes
the relative subdifferential at each relative-interior point a singleton containing the Fréchet
derivative. -/
theorem subdifferentialWithinAt_eq_singleton_fderiv_of_differentiableOnIntrinsicInterior
    (hf_convex : ConvexOn 𝕜 U f) (hfd : DifferentiableOn 𝕜 f (ri[𝕜](U)))
    {x : E} (hx : x ∈ ri[𝕜](U)) :
    ∂ᵣf(x | U) = {fderiv 𝕜 f x} := by
  exact subdifferentialWithinAt_eq_singleton_fderiv_of_mem_intrinsicInterior hf_convex hx (hfd x hx)

/-- Pointwise membership form on the intrinsic global owner surface. -/
theorem mem_subdifferentialWithinAt_iff_eq_fderiv_of_differentiableOnIntrinsicInterior
    (hf_convex : ConvexOn 𝕜 U f) (hfd : DifferentiableOn 𝕜 f (ri[𝕜](U)))
    {x : E} {xStar : StrongDual 𝕜 E} (hx : x ∈ ri[𝕜](U)) :
    xStar ∈ ∂ᵣf(x | U) ↔ xStar = fderiv 𝕜 f x := by
  exact mem_subdifferentialWithinAt_iff_eq_fderiv_of_mem_intrinsicInterior hf_convex hx (hfd x hx)

/-- Nonemptiness form on the intrinsic global owner surface. -/
theorem subdifferentialWithinAt_nonempty_of_differentiableOnIntrinsicInterior
    (hf_convex : ConvexOn 𝕜 U f) (hfd : DifferentiableOn 𝕜 f (ri[𝕜](U)))
    {x : E} (hx : x ∈ ri[𝕜](U)) :
    (∂ᵣf(x | U)).Nonempty := by
  exact subdifferentialWithinAt_nonempty_of_mem_intrinsicInterior hf_convex hx (hfd x hx)

/-- Corollary 25.1.3, interior bridge form: on a convex set, differentiability of `f` on
`interior U` makes the relative subdifferential at each interior point a singleton containing the
Fréchet derivative. -/
theorem subdifferentialWithinAt_eq_singleton_fderiv_of_differentiableOnInterior
    (hf_convex : ConvexOn 𝕜 U f) (hfd : DifferentiableOn 𝕜 f (interior U))
    {x : E} (hx : x ∈ interior U) :
    ∂ᵣf(x | U) = {fderiv 𝕜 f x} := by
  have hx_ri : x ∈ ri[𝕜](U) := interior_subset_intrinsicInterior hx
  exact subdifferentialWithinAt_eq_singleton_fderiv_of_mem_intrinsicInterior
    hf_convex hx_ri (hfd.differentiableAt (IsOpen.mem_nhds isOpen_interior hx))

/-- Pointwise membership form of Corollary 25.1.3 on the interior bridge surface. -/
theorem mem_subdifferentialWithinAt_iff_eq_fderiv_of_differentiableOnInterior
    (hf_convex : ConvexOn 𝕜 U f) (hfd : DifferentiableOn 𝕜 f (interior U))
    {x : E} {xStar : StrongDual 𝕜 E} (hx : x ∈ interior U) :
    xStar ∈ ∂ᵣf(x | U) ↔
      xStar = fderiv 𝕜 f x := by
  have hx_ri : x ∈ ri[𝕜](U) := interior_subset_intrinsicInterior hx
  exact mem_subdifferentialWithinAt_iff_eq_fderiv_of_mem_intrinsicInterior
    hf_convex hx_ri (hfd.differentiableAt (IsOpen.mem_nhds isOpen_interior hx))

/-- Nonemptiness form of Corollary 25.1.3 on the interior bridge surface. -/
theorem subdifferentialWithinAt_nonempty_of_differentiableOnInterior
    (hf_convex : ConvexOn 𝕜 U f) (hfd : DifferentiableOn 𝕜 f (interior U))
    {x : E} (hx : x ∈ interior U) :
    (∂ᵣf(x | U)).Nonempty := by
  have hx_ri : x ∈ ri[𝕜](U) := interior_subset_intrinsicInterior hx
  exact subdifferentialWithinAt_nonempty_of_mem_intrinsicInterior
    hf_convex hx_ri (hfd.differentiableAt (IsOpen.mem_nhds isOpen_interior hx))

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {U : Set E} {f : E → ℝ}

/-- Corollary 25.1.3, intrinsic canonical dual-owner Euclidean form. -/
theorem subdifferentialWithinAt_eq_singleton_toDual_gradient_of_mem_intrinsicInterior
    (hf_convex : ConvexOn ℝ U f) {x : E} (hx : x ∈ ri[ℝ](U))
    (hfdx : DifferentiableAt ℝ f x) :
    ∂ᵣf(x | U) = {InnerProductSpace.toDual ℝ E (∇ f x)} := by
  exact Function.subdifferentialWithinAt_eq_singleton_toDual_gradient hf_convex hx hfdx

/-- Corollary 25.1.3, intrinsic global dual-owner Euclidean form. -/
theorem subdifferentialWithinAt_eq_singleton_toDual_gradient_of_differentiableOnIntrinsicInterior
    (hf_convex : ConvexOn ℝ U f) (hfd : DifferentiableOn ℝ f (ri[ℝ](U)))
    {x : E} (hx : x ∈ ri[ℝ](U)) :
    ∂ᵣf(x | U) = {InnerProductSpace.toDual ℝ E (∇ f x)} := by
  exact subdifferentialWithinAt_eq_singleton_toDual_gradient_of_mem_intrinsicInterior
    hf_convex hx (hfd x hx)

/-- Corollary 25.1.3, interior bridge dual-owner Euclidean companion. -/
theorem subdifferentialWithinAt_eq_singleton_toDual_gradient_of_differentiableOnInterior
    (hf_convex : ConvexOn ℝ U f) (hfd : DifferentiableOn ℝ f (interior U))
    {x : E} (hx : x ∈ interior U) :
    ∂ᵣf(x | U) = {InnerProductSpace.toDual ℝ E (∇ f x)} := by
  have hx_ri : x ∈ ri[ℝ](U) := interior_subset_intrinsicInterior hx
  exact subdifferentialWithinAt_eq_singleton_toDual_gradient_of_mem_intrinsicInterior
    hf_convex hx_ri (hfd.differentiableAt (IsOpen.mem_nhds isOpen_interior hx))

/-- Pointwise membership form of the intrinsic canonical Euclidean `toDual` owner. -/
theorem mem_subdifferentialWithinAt_iff_eq_toDual_gradient_of_mem_intrinsicInterior
    (hf_convex : ConvexOn ℝ U f) {x : E} {xStar : StrongDual ℝ E}
    (hx : x ∈ ri[ℝ](U)) (hfdx : DifferentiableAt ℝ f x) :
    xStar ∈ ∂ᵣf(x | U) ↔ xStar = InnerProductSpace.toDual ℝ E (∇ f x) := by
  rw [subdifferentialWithinAt_eq_singleton_toDual_gradient_of_mem_intrinsicInterior
    hf_convex hx hfdx, Set.mem_singleton_iff]

/-- Pointwise membership form of the intrinsic global Euclidean `toDual` owner. -/
theorem mem_subdifferentialWithinAt_iff_eq_toDual_gradient_of_differentiableOnIntrinsicInterior
    (hf_convex : ConvexOn ℝ U f) (hfd : DifferentiableOn ℝ f (ri[ℝ](U)))
    {x : E} {xStar : StrongDual ℝ E} (hx : x ∈ ri[ℝ](U)) :
    xStar ∈ ∂ᵣf(x | U) ↔ xStar = InnerProductSpace.toDual ℝ E (∇ f x) := by
  exact mem_subdifferentialWithinAt_iff_eq_toDual_gradient_of_mem_intrinsicInterior
    hf_convex hx (hfd x hx)

/-- Pointwise membership form of the interior bridge Euclidean `toDual` companion. -/
theorem mem_subdifferentialWithinAt_iff_eq_toDual_gradient_of_differentiableOnInterior
    (hf_convex : ConvexOn ℝ U f) (hfd : DifferentiableOn ℝ f (interior U))
    {x : E} {xStar : StrongDual ℝ E} (hx : x ∈ interior U) :
    xStar ∈ ∂ᵣf(x | U) ↔
      xStar = InnerProductSpace.toDual ℝ E (∇ f x) := by
  have hx_ri : x ∈ ri[ℝ](U) := interior_subset_intrinsicInterior hx
  exact mem_subdifferentialWithinAt_iff_eq_toDual_gradient_of_mem_intrinsicInterior
    hf_convex hx_ri (hfd.differentiableAt (IsOpen.mem_nhds isOpen_interior hx))

namespace Function

/-- Corollary 25.1.3 on the intrinsic canonical Euclidean bridge owner surface. -/
theorem subdifferentialWithinAt_eq_singleton_gradient_of_mem_intrinsicInterior
    (hf_convex : ConvexOn ℝ U f) {x : E} (hx : x ∈ ri[ℝ](U))
    (hfdx : DifferentiableAt ℝ f x) :
    ∂ᵥᵣf(x | U) = {∇ f x} := by
  exact subdifferentialWithinAt_eq_singleton_gradient hf_convex hx hfdx

/-- Corollary 25.1.3 on the intrinsic global Euclidean bridge owner surface. -/
theorem subdifferentialWithinAt_eq_singleton_gradient_of_differentiableOnIntrinsicInterior
    (hf_convex : ConvexOn ℝ U f) (hfd : DifferentiableOn ℝ f (ri[ℝ](U)))
    {x : E} (hx : x ∈ ri[ℝ](U)) :
    ∂ᵥᵣf(x | U) = {∇ f x} := by
  exact subdifferentialWithinAt_eq_singleton_gradient_of_mem_intrinsicInterior
    hf_convex hx (hfd x hx)

/-- Corollary 25.1.3 on the interior bridge owner surface. -/
theorem subdifferentialWithinAt_eq_singleton_gradient_of_differentiableOnInterior
    (hf_convex : ConvexOn ℝ U f) (hfd : DifferentiableOn ℝ f (interior U))
    {x : E} (hx : x ∈ interior U) :
    ∂ᵥᵣf(x | U) = {∇ f x} := by
  have hx_ri : x ∈ ri[ℝ](U) := interior_subset_intrinsicInterior hx
  exact subdifferentialWithinAt_eq_singleton_gradient_of_mem_intrinsicInterior
    hf_convex hx_ri (hfd.differentiableAt (IsOpen.mem_nhds isOpen_interior hx))

/-- Pointwise membership form on the intrinsic canonical Euclidean bridge owner surface. -/
theorem mem_subdifferentialWithinAt_iff_eq_gradient_of_mem_intrinsicInterior
    (hf_convex : ConvexOn ℝ U f) {x g : E} (hx : x ∈ ri[ℝ](U))
    (hfdx : DifferentiableAt ℝ f x) :
    g ∈ ∂ᵥᵣf(x | U) ↔ g = ∇ f x := by
  rw [subdifferentialWithinAt_eq_singleton_gradient_of_mem_intrinsicInterior hf_convex hx hfdx,
    Set.mem_singleton_iff]

/-- Pointwise membership form on the intrinsic global Euclidean bridge owner surface. -/
theorem mem_subdifferentialWithinAt_iff_eq_gradient_of_differentiableOnIntrinsicInterior
    (hf_convex : ConvexOn ℝ U f) (hfd : DifferentiableOn ℝ f (ri[ℝ](U)))
    {x g : E} (hx : x ∈ ri[ℝ](U)) :
    g ∈ ∂ᵥᵣf(x | U) ↔ g = ∇ f x := by
  exact mem_subdifferentialWithinAt_iff_eq_gradient_of_mem_intrinsicInterior hf_convex hx (hfd x hx)

/-- Pointwise membership form of Corollary 25.1.3 on the interior bridge owner. -/
theorem mem_subdifferentialWithinAt_iff_eq_gradient_of_differentiableOnInterior
    (hf_convex : ConvexOn ℝ U f) (hfd : DifferentiableOn ℝ f (interior U))
    {x g : E} (hx : x ∈ interior U) :
    g ∈ ∂ᵥᵣf(x | U) ↔ g = ∇ f x := by
  have hx_ri : x ∈ ri[ℝ](U) := interior_subset_intrinsicInterior hx
  exact mem_subdifferentialWithinAt_iff_eq_gradient_of_mem_intrinsicInterior
    hf_convex hx_ri (hfd.differentiableAt (IsOpen.mem_nhds isOpen_interior hx))

/-- Nonemptiness form on the intrinsic canonical Euclidean bridge owner surface. -/
theorem subdifferentialWithinAt_nonempty_of_mem_intrinsicInterior
    (hf_convex : ConvexOn ℝ U f) {x : E} (hx : x ∈ ri[ℝ](U))
    (hfdx : DifferentiableAt ℝ f x) :
    (∂ᵥᵣf(x | U)).Nonempty := by
  rw [subdifferentialWithinAt_eq_singleton_gradient_of_mem_intrinsicInterior hf_convex hx hfdx]
  exact Set.singleton_nonempty (∇ f x)

/-- Nonemptiness form on the intrinsic global Euclidean bridge owner surface. -/
theorem subdifferentialWithinAt_nonempty_of_differentiableOnIntrinsicInterior
    (hf_convex : ConvexOn ℝ U f) (hfd : DifferentiableOn ℝ f (ri[ℝ](U)))
    {x : E} (hx : x ∈ ri[ℝ](U)) :
    (∂ᵥᵣf(x | U)).Nonempty := by
  exact subdifferentialWithinAt_nonempty_of_mem_intrinsicInterior hf_convex hx (hfd x hx)

/-- Nonemptiness form of Corollary 25.1.3 on the interior bridge owner. -/
theorem subdifferentialWithinAt_nonempty_of_differentiableOnInterior
    (hf_convex : ConvexOn ℝ U f) (hfd : DifferentiableOn ℝ f (interior U))
    {x : E} (hx : x ∈ interior U) :
    (∂ᵥᵣf(x | U)).Nonempty := by
  have hx_ri : x ∈ ri[ℝ](U) := interior_subset_intrinsicInterior hx
  exact subdifferentialWithinAt_nonempty_of_mem_intrinsicInterior
    hf_convex hx_ri (hfd.differentiableAt (IsOpen.mem_nhds isOpen_interior hx))

end Function

end
