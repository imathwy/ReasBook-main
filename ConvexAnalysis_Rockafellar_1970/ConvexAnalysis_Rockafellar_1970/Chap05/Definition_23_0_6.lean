import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.HasPairing

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Rockafellar

universe u v

section

variable {𝕜 : Type v} [Add 𝕜] [LE 𝕜]
variable {E : Type u} [Sub E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Definition 23.0.6 introduces the subdifferential of an extended-valued
  function at a point: the set of continuous linear functionals whose affine support inequality
  holds everywhere.
- `core/canonical`: there is no upstream project or mathlib owner for this exact notion in the
  current chapter graph, so this file owns the declaration `subdifferentialAt`. The primitive
  mathematical data are only the function `f`, the base point `x`, and the supporting inequality
  for a dual-side element of a pairing.
- `bridge/view`: the membership theorem below is the derived pointwise characterization of being a
  subgradient at `x`.

Domain-style sampling used here:
- the chapter owner `convexConjugate` from `Chap03.Defn_12_2`,
  which also lives on the canonical extended codomain `WithTopBot 𝕜` and uses Rockafellar scoped
  notation;
- the chapter owner `indicatorFunction` with notation `δ(· | C)` from
  `Chap01.Defintion_4_8_1`,
  showing the project convention of a direct owner plus thin notation/specification API;
- the chapter effective-domain owner `dom(·)` from `Chap01.Definition_4_4`,
  which downstream Chapter 23 theorems use alongside subdifferentials;
- the project pairing owner `HasPairing`, which keeps the source-facing definition intrinsic and
  lets the strong-dual model `StrongDual 𝕜 E` remain a canonical default specialization.

Primitive data vs derived API:
- primitive owner: `subdifferentialAt f x`;
- derived API: the membership characterization `xStar ∈ subdifferentialAt f x`.

Layer target: `source-facing`. The definition itself only uses the affine support inequality
through a pairing, so the owner is pairing-intrinsic with the continuous-dual model kept as the
default specialization.
-/

/-- Definition 23.0.6: the subdifferential of an extended-valued function at `x` is the set
of dual-side elements that support `f` at `x`. -/
def subdifferentialAt (f : E → WithTopBot 𝕜) (x : E)
    {Y : Type*} [HasPairing E Y 𝕜] : Set Y :=
  {xStar | ∀ z, f z ≥ f x + ((⟪z - x, xStar⟫ₚ : 𝕜) : WithTopBot 𝕜)}

scoped[Rockafellar] notation "∂[" Y "]" f "(" x ")" => subdifferentialAt (Y := Y) f x

/-- Pairing-level membership form of `subdifferentialAt`. -/
@[simp] theorem mem_subdifferentialAt_pairing
    {f : E → WithTopBot 𝕜} {x : E} {Y : Type*} [HasPairing E Y 𝕜]
    {xStar : Y} :
    xStar ∈ (∂[Y]f(x)) ↔
      ∀ z, f z ≥ f x + ((⟪z - x, xStar⟫ₚ : 𝕜) : WithTopBot 𝕜) :=
  Iff.rfl

/-- Pairing transport API for `subdifferentialAt`: if two pairing instances on `(E, Y, 𝕜)` are
pointwise equal, they define the same subdifferential set at every base point. -/
theorem subdifferentialAt_eq_of_pairing_eq
    {f : E → WithTopBot 𝕜} {x : E} {Y : Type*}
    {pairing₁ pairing₂ : HasPairing E Y 𝕜}
    (hpair : ∀ z : E, ∀ xStar : Y,
      @HasPairing.pairing E Y 𝕜 pairing₁ z xStar =
        @HasPairing.pairing E Y 𝕜 pairing₂ z xStar) :
    (letI : HasPairing E Y 𝕜 := pairing₁; _root_.subdifferentialAt (Y := Y) f x) =
      (letI : HasPairing E Y 𝕜 := pairing₂; _root_.subdifferentialAt (Y := Y) f x) := by
  ext xStar
  constructor <;> intro hx
  · rw [@_root_.mem_subdifferentialAt_pairing 𝕜 _ _ E _ f x Y pairing₂ xStar]
    rw [@_root_.mem_subdifferentialAt_pairing 𝕜 _ _ E _ f x Y pairing₁ xStar] at hx
    intro z
    simpa [hpair (z - x) xStar] using hx z
  · rw [@_root_.mem_subdifferentialAt_pairing 𝕜 _ _ E _ f x Y pairing₁ xStar]
    rw [@_root_.mem_subdifferentialAt_pairing 𝕜 _ _ E _ f x Y pairing₂ xStar] at hx
    intro z
    simpa [hpair (z - x) xStar] using hx z

end

section

variable {𝕜 : Type v} [Semiring 𝕜] [TopologicalSpace 𝕜] [LE 𝕜]
variable {E : Type u} [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
variable [HasPairing E (StrongDual 𝕜 E) 𝕜]

scoped[Rockafellar] notation "∂ " f " at " x =>
  (_root_.subdifferentialAt (Y := StrongDual _ _) f x)

/-- Pairing-level membership form on the default dual codomain `StrongDual 𝕜 E`. This keeps the
default subdifferential surface `∂ f at x` on the intrinsic pairing owner layer; the concrete
evaluation form is provided below as a bridge specialization. -/
theorem mem_subdifferentialAt_default_pairing
    {f : E → WithTopBot 𝕜} {x : E}
    {xStar : StrongDual 𝕜 E} :
    xStar ∈ (∂ f at x) ↔
      ∀ z, f z ≥ f x + ((⟪z - x, xStar⟫ₚ : 𝕜) : WithTopBot 𝕜) :=
  Iff.rfl

end

section

variable {𝕜 : Type v} [NormedField 𝕜] [LE 𝕜]
variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A functional belongs to the subdifferential at `x` exactly when it satisfies the global
supporting-affine inequality. -/
@[simp] theorem mem_subdifferentialAt
    {f : E → WithTopBot 𝕜} {x : E} {xStar : StrongDual 𝕜 E} :
    xStar ∈ (∂ f at x) ↔ ∀ z, f z ≥ f x + ((xStar (z - x) : 𝕜) : WithTopBot 𝕜) := by
  rw [mem_subdifferentialAt_default_pairing (f := f) (x := x) (xStar := xStar)]
  change
      (∀ z, f z ≥ f x + (((HasLinearPairing.pairingLinear (z - x)) xStar : 𝕜) :
        WithTopBot 𝕜)) ↔
      ∀ z, f z ≥ f x + ((xStar (z - x) : 𝕜) : WithTopBot 𝕜)
  rfl

end

section

variable {𝕜 : Type v} [RCLike 𝕜] [LE 𝕜]
variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Definition 23.0.6 introduces the subdifferential `∂f(x)` through the
  supporting-affine inequality.
- `core/canonical`: the primitive owner remains the dual-valued declaration
  `_root_.subdifferentialAt`.
- `bridge/view`: later Chapter 23 statements pair subdifferentials with directions using the
  chapter support-function owner on `Set E`. The canonical dual-pairing map
  `InnerProductSpace.toDualMap 𝕜 E` sends vectors to continuous dual vectors, so
  `Function.subdifferentialAt` below is a thin vector-valued bridge, not a second root
  definition.

Domain-style sampling used here:
- `Function.IsConvex` from `Chap01.Theorem_4_2`;
- `Function.IsProper` and `dom(·)` from `Chap01.Definition_4_6`;
- `supportFunction` from `Chap01.Defintion_4_8_2`;
- mathlib's canonical dual-pairing bridge `InnerProductSpace.toDualMap`, which gives the chapter's
  standard vector-to-dual map in ordered inner-product spaces.

Primitive data vs derived API:
- primitive owner: `_root_.subdifferentialAt f x`;
- derived API: the vector-valued bridge `Function.subdifferentialAt f x`,
  obtained by pulling back the owner along `InnerProductSpace.toDualMap 𝕜 E`,
  and its pointwise membership simplification.

Layer target: `bridge/view`.

Notation evaluation:
- the pointwise source notation is exposed as `∂ f at x`, with `∂[Y]f(x)` available when the
  dual codomain must be explicit. This keeps the textbook symbol while avoiding a parser collision
  with the established image notation `∂f(S)`.
-/

namespace Function

/-- In an ordered inner-product space, the vector-valued subdifferential used later in this
chapter is the pullback of the dual-valued owner `_root_.subdifferentialAt` along
`InnerProductSpace.toDualMap`. -/
abbrev subdifferentialAt (f : E → WithTopBot 𝕜) (x : E) : Set E :=
  (InnerProductSpace.toDualMap 𝕜 E) ⁻¹' (_root_.subdifferentialAt f x)

scoped[Rockafellar] notation "∂ᵥ" f "(" x ")" => Function.subdifferentialAt f x

@[simp] theorem mem_subdifferentialAt {f : E → WithTopBot 𝕜} {x g : E} :
    g ∈ (∂ᵥf(x)) ↔ ∀ z, f z ≥ f x + ((inner 𝕜 g (z - x) : 𝕜) : WithTopBot 𝕜) :=
  Iff.rfl

end Function

end
