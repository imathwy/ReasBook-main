import ConvexAnalysis_Rockafellar_1970.Chap01.Remark_4_4_5
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_23_0_6

noncomputable section

open scoped Rockafellar
open Function

universe u v

section

variable {𝕜 : Type v} [Add 𝕜] [LE 𝕜]
variable {E : Type u} [Sub E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Definition 25.1 repeatedly uses the subdifferential of a scalar-valued branch
  `f` on a domain `U`, understood through its canonical extension by `+∞` off `U`.
- `core/canonical`: the primitive owner is the pairing-parametric Chapter 23 owner
  `_root_.subdifferentialAt` applied to the canonical extension `Function.toWithTopBotOn f U`.
- `bridge/view`: a Euclidean vector-valued owner is kept separately in the next section as a thin
  Fréchet-Riesz transport bridge.

Domain-style sampling used here:
- `Function.toWithTopBotOn` from `Chap01.Remark_4_4_5`;
- `_root_.subdifferentialAt` and `_root_.mem_subdifferentialAt_pairing` from
  `Chap05.Definition_23_0_6`.

Primitive data vs derived API:
- primitive source data: `f`, `U`, and `x`;
- primitive owner surface: `_root_.subdifferentialWithinAt f U x Y`;
- derived API: pointwise membership in that owner.

Layer target: `core/canonical` owner surface for Chapter 25 statements, with no
inner-product/completeness assumptions in the main owner.
-/

/-- Definition 25.1, canonical owner form: the relative subdifferential of a scalar-valued branch
`f` on `U` at `x` is the Chapter 23 subdifferential of the canonical extension
`Function.toWithTopBotOn f U` at `x`. The codomain is pairing-parametric. -/
abbrev subdifferentialWithinAt (f : E → 𝕜) (U : Set E) (x : E)
    {Y : Type (max u v)} [HasPairing E Y 𝕜] : Set Y :=
  _root_.subdifferentialAt (Y := Y) (toWithTopBotOn f U) x

scoped[Rockafellar] notation "∂ᵣ[" Y "]" f "(" x " | " U ")" =>
  subdifferentialWithinAt f U x Y

@[simp] theorem mem_subdifferentialWithinAt_pairing
    {f : E → 𝕜} {U : Set E} {x : E} {Y : Type (max u v)} [HasPairing E Y 𝕜] {xStar : Y} :
    xStar ∈ ∂ᵣ[Y]f(x | U) ↔
      ∀ z, toWithTopBotOn f U z ≥
        toWithTopBotOn f U x + ((⟪z - x, xStar⟫ₚ : 𝕜) : WithTopBot 𝕜) :=
  Iff.rfl

end

section

variable {𝕜 : Type v} [Semiring 𝕜] [TopologicalSpace 𝕜] [LE 𝕜]
variable {E : Type u} [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
variable [HasPairing E (StrongDual 𝕜 E) 𝕜]

/-- Canonical default-dual bridge for Definition 25.1. -/
abbrev subdifferentialWithinAtDual (f : E → 𝕜) (U : Set E) (x : E) : Set (StrongDual 𝕜 E) :=
  _root_.subdifferentialWithinAt (Y := StrongDual 𝕜 E) f U x

scoped[Rockafellar] notation "∂ᵣ" f "(" x " | " U ")" =>
  subdifferentialWithinAtDual f U x

/-- Pairing-level membership form on the default dual codomain `StrongDual 𝕜 E`. -/
theorem mem_subdifferentialWithinAt_default_pairing
    {f : E → 𝕜} {U : Set E} {x : E} {xStar : StrongDual 𝕜 E} :
    xStar ∈ ∂ᵣf(x | U) ↔
      ∀ z, toWithTopBotOn f U z ≥
        toWithTopBotOn f U x + ((⟪z - x, xStar⟫ₚ : 𝕜) : WithTopBot 𝕜) :=
  Iff.rfl

end

section

variable {𝕜 : Type v} [NormedField 𝕜] [LE 𝕜]
variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Pointwise membership in `subdifferentialWithinAt` specialized to the canonical dual model
`StrongDual 𝕜 E`. -/
@[simp] theorem mem_subdifferentialWithinAt
    {f : E → 𝕜} {U : Set E} {x : E} {xStar : StrongDual 𝕜 E} :
    xStar ∈ ∂ᵣf(x | U) ↔
      ∀ z, toWithTopBotOn f U z ≥
        toWithTopBotOn f U x + ((xStar (z - x) : 𝕜) : WithTopBot 𝕜) := by
  rw [mem_subdifferentialWithinAt_default_pairing (f := f) (U := U) (x := x) (xStar := xStar)]
  change
      (∀ z, toWithTopBotOn f U z ≥ toWithTopBotOn f U x +
        (((HasLinearPairing.pairingLinear (z - x)) xStar : 𝕜) : WithTopBot 𝕜)) ↔
      ∀ z, toWithTopBotOn f U z ≥
        toWithTopBotOn f U x + ((xStar (z - x) : 𝕜) : WithTopBot 𝕜)
  rfl

end

section

variable {𝕜 : Type v} [RCLike 𝕜] [LE 𝕜]
variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace Function

/-- Euclidean bridge owner for Definition 25.1: transport the canonical dual-valued owner
`_root_.subdifferentialWithinAt` through the Fréchet-Riesz map
`InnerProductSpace.toDualMap 𝕜 E`. -/
abbrev subdifferentialWithinAt (f : E → 𝕜) (U : Set E) (x : E) : Set E :=
  (InnerProductSpace.toDualMap 𝕜 E) ⁻¹' (∂ᵣf(x | U))

scoped[Rockafellar] notation "∂ᵥᵣ" f "(" x " | " U ")" =>
  Function.subdifferentialWithinAt f U x

/-- Membership in the Euclidean bridge owner is equivalent to the source inequality form from
Definition 25.1. -/
@[simp] theorem mem_subdifferentialWithinAt
    {f : E → 𝕜} {U : Set E} {x g : E} :
    g ∈ ∂ᵥᵣf(x | U) ↔
      ∀ z, toWithTopBotOn f U z ≥
        toWithTopBotOn f U x + ((inner 𝕜 g (z - x) : 𝕜) : WithTopBot 𝕜) := by
  change InnerProductSpace.toDualMap 𝕜 E g ∈ ∂ᵣf(x | U) ↔
      ∀ z, toWithTopBotOn f U z ≥
        toWithTopBotOn f U x + ((inner 𝕜 g (z - x) : 𝕜) : WithTopBot 𝕜)
  rw [_root_.mem_subdifferentialWithinAt (f := f) (U := U) (x := x)
    (xStar := InnerProductSpace.toDualMap 𝕜 E g)]
  simp

end Function

end
