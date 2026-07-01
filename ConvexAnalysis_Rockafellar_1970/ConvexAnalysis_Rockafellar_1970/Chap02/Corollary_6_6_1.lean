import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_6_4
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_15

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise Rockafellar

section IntrinsicInteriorUnit

variable
    {𝕜 E : Type*}
    [Ring 𝕜]
    [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E] [SMulCommClass 𝕜ˣ 𝕜 E]
    [ContinuousConstSMul 𝕜ˣ E]

namespace Set

/-- Unit-scalar dilation commutes with relative interior for any set in a topological
`𝕜`-module. This is the primitive owner theorem behind nonzero-scalar transport, obtained by
transport along the continuous affine equivalence `x ↦ u • x`. -/
@[simp] theorem intrinsicInterior_smul_unit (C : Set E) (u : 𝕜ˣ) :
    ri[𝕜]((u : 𝕜) • C) = (u : 𝕜) • ri[𝕜](C) := by
  let e : E ≃ᴬ[𝕜] E :=
    (ContinuousLinearEquiv.smulLeft (R₁ := 𝕜) (M₁ := E) u).toContinuousAffineEquiv
  simpa [e, Units.smul_def] using ContinuousAffineEquiv.image_intrinsicInterior e C

/-- Unit scalar dilation in `IsUnit` form: this keeps the owner at ring level and avoids
division-ring hypotheses when invertibility is provided directly. -/
@[simp] theorem intrinsicInterior_smul_of_isUnit (C : Set E) (a : 𝕜) (ha : IsUnit a) :
    ri[𝕜](a • C) = a • ri[𝕜](C) := by
  rcases ha with ⟨u, rfl⟩
  exact intrinsicInterior_smul_unit (C := C) (u := u)

end Set

end IntrinsicInteriorUnit

section IntrinsicInteriorZero

variable
    {𝕜 E : Type*}
    [Ring 𝕜]
    [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]

namespace Set

/-- Zero scalar dilation commutes with relative interior as soon as the relative interior is
nonempty. This is the primitive zero-scalar owner theorem used to build the all-scalar bridge. -/
theorem intrinsicInterior_zero_smul (C : Set E) (hri : (ri[𝕜](C)).Nonempty) :
    ri[𝕜]((0 : 𝕜) • C) = (0 : 𝕜) • ri[𝕜](C) := by
  have hCne : C.Nonempty := hri.mono intrinsicInterior_subset
  rw [Set.zero_smul_set hCne, Set.zero_smul_set hri]
  exact intrinsicInterior_singleton (x := (0 : E))

attribute [simp] intrinsicInterior_zero_smul

end Set

end IntrinsicInteriorZero

section IntrinsicInteriorNonzero

variable
    {𝕜 E : Type*}
    [DivisionRing 𝕜]
    [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E] [SMulCommClass 𝕜ˣ 𝕜 E]
    [ContinuousConstSMul 𝕜ˣ E]

namespace Set

/-- Nonzero scalar dilation commutes with relative interior for any set in a topological
`𝕜`-module. This is the division-ring bridge obtained from the unit-scalar owner theorem. -/
@[simp] theorem intrinsicInterior_smul_of_ne_zero (C : Set E) (a : 𝕜) (ha : a ≠ 0) :
    ri[𝕜](a • C) = a • ri[𝕜](C) := by
  exact intrinsicInterior_smul_of_isUnit C a (isUnit_iff_ne_zero.mpr ha)

end Set

end IntrinsicInteriorNonzero

section IntrinsicInteriorScalar

variable
    {𝕜 E : Type*}
    [Ring 𝕜]
    [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E] [SMulCommClass 𝕜ˣ 𝕜 E]
    [ContinuousConstSMul 𝕜ˣ E]

namespace Set

/-- Scalar dilation commutes with relative interior from primitive scalar data:
either `a = 0` or `a` is a unit, together with nonemptiness of `ri[𝕜](C)`. -/
@[simp] theorem intrinsicInterior_smul (C : Set E) (a : 𝕜)
    (ha : a = 0 ∨ IsUnit a) (hri : (ri[𝕜](C)).Nonempty) :
    ri[𝕜](a • C) = a • ri[𝕜](C) := by
  rcases ha with rfl | ha
  · simpa using intrinsicInterior_zero_smul (C := C) hri
  · simpa using intrinsicInterior_smul_of_isUnit C a ha

end Set

end IntrinsicInteriorScalar

section IntrinsicInterior

variable
    {𝕜 E : Type*}
    [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
    [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/- 
Source/core/bridge triage:
- `source-facing`: Corollary 6.6.1 states that dilating a convex subset of a finite-dimensional
  normed space over `𝕜` by a scalar dilates its relative interior by the same scalar.
- `core/canonical`: the owner theorem is `Set.intrinsicInterior_smul`, whose primitive input is
  the set `C`, the scalar `a`, the witness `a = 0 ∨ IsUnit a`, and nonemptiness of `ri[𝕜](C)`.
- `bridge/view`: the source all-scalar convex corollary recovers that primitive nonemptiness in
  finite-dimensional spaces via `Convex.intrinsicInterior_nonempty`.
- Primitive data vs derived API: transport needs only `a = 0 ∨ IsUnit a` and
  `Nonempty (ri[𝕜](C))`; convexity and finite-dimensional ambient structure are source-facing
  bridge data used to produce these owner inputs.
- Domain-style sampling: the relevant declarations are `ContinuousLinearEquiv.smulLeft`,
  `ContinuousAffineEquiv.image_intrinsicInterior`,
  `Convex.intrinsicInterior_nonempty`, and `Set.zero_smul_set`.
- Layer target: this item exposes both layers explicitly: the canonical all-scalar owner theorem on
  `Set`, and the source-facing convex bridge in `namespace Convex`.
-/

namespace Convex

/-- Corollary 6.6.1: for a convex subset `C` of a finite-dimensional normed space over `𝕜` and any
scalar `λ : 𝕜`, the relative interior of the dilate `λ • C` is the dilate of the relative
interior of `C`. This is the source-facing all-scalar bridge over the nonzero owner theorem and
the zero-scalar singleton/nonempty-relative-interior bridge at `λ = 0`. -/
@[simp] theorem intrinsicInterior_smul {C : Set E} (hC : Convex 𝕜 C) (a : 𝕜) :
    ri[𝕜](a • C) = a • ri[𝕜](C) := by
  rcases Set.eq_empty_or_nonempty C with rfl | hCne
  · simp
  · have ha : a = 0 ∨ IsUnit a := by
      rcases eq_or_ne a 0 with ha0 | ha0
      · exact Or.inl ha0
      · exact Or.inr (isUnit_iff_ne_zero.mpr ha0)
    simpa using Set.intrinsicInterior_smul C a ha (hC.intrinsicInterior_nonempty hCne)

end Convex

end IntrinsicInterior
