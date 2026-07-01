import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.ERealSMul
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped RealInnerProductSpace
open scoped Rockafellar

universe u v

section

variable {E : Type u} [SeminormedAddGroup E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 12.3.5 characterizes the functions on a real Euclidean space invariant
  under all orthogonal transformations as exactly the functions factoring through the Euclidean
  norm, and then characterizes which such radial functions are closed proper convex.
- `core/canonical`: the owner abstractions are `LinearIsometryEquiv` for orthogonal
  transformations, the norm `‖x‖`, the canonical nonnegative-ray type `NNReal`,
  ray, `ConvexOn ℝ (Set.Ici (0 : ℝ))` for convexity of the radial profile, `Monotone`,
  `LowerSemicontinuous`, and `Function.IsClosedProperConvex`.
- `bridge/view`: the textbook profile `g : [0, +∞) → ...` is encoded directly as a function on the
  type `NNReal`, and its ambient-line convexity is expressed by the canonical bridge
  `Function.extendByTop`.

Domain-style sampling used here:
- `LinearIsometryEquiv.norm_map`;
- `reflection_sub`, which gives an orthogonal map sending one vector to another of the same norm;
- `ConvexOn` on `Set.Ici (0 : ℝ)`;
- `Monotone` and `LowerSemicontinuous` on `NNReal`;
- the chapter predicate `Function.IsClosedProperConvex`.

Primitive data vs derived API:
- primitive bridge data: `radialExtension`;
- source-facing ray-side owner:
  `Function.IsMonotoneClosedConvexOnNonnegativeRay`, bundling lower semicontinuity and
  monotonicity on `NNReal`, finiteness at the origin, and convexity of the canonical ambient-line
  extension on `Set.Ici (0 : ℝ)`;
- derived API: the orthogonal-invariance characterization and the closed-proper-convex
  characterization for radial extensions.

Layer target: `source-facing`; the item is stated directly in terms of orthogonal invariance, the
norm, and one-variable radial profiles. The radial-extension owner itself lives on the
minimal seminormed-space layer, the orthogonal-invariance theorem refines the ambient `R^n` source
semantics to the intrinsic real inner-product-space level, and the closed-proper-convex theorem
lives on the weaker real normed-space layer already used by `ConvexOn`, `LowerSemicontinuous`, and
`Function.IsClosedProperConvex`.
-/

/-- The radial extension of a function on `[0, +∞)` to a seminormed additive group, obtained by
composing with the norm. -/
def radialExtension (E : Type u) [SeminormedAddGroup E] {α : Type v}
    (g : NNReal → α) : E → α :=
  fun x ↦ g ‖x‖₊

-- Proof sketch: unfold `radialExtension`; the value at `x` is, by definition, the profile `g`
-- evaluated at the nonnegative radius `‖x‖`.
/-- Evaluating the radial extension at `x` means evaluating the profile at the radius `‖x‖`. -/
@[simp] theorem radialExtension_apply {α : Type v} (g : NNReal → α) (x : E) :
    radialExtension E g x = g ‖x‖₊ :=
  rfl

end

section

namespace Function

/-- A `WithTopBot α`-valued profile on `[0, +∞)` is lower semicontinuous and nondecreasing on the
ray subtype, its canonical ambient-line extension `Function.extendByTop g` is convex on the ray,
and its value at the origin is finite. -/
class IsMonotoneClosedConvexOnNonnegativeRay
    {α : Type v} [TopologicalSpace (WithTopBot α)] [AddCommMonoid α] [SMul ℝ α]
    [PartialOrder (WithTopBot α)]
    (g : NNReal → WithTopBot α) : Prop where
  lowerSemicontinuous : LowerSemicontinuous g
  convexOn : ConvexOn ℝ (Set.Ici (0 : ℝ)) (Function.extendByTop g)
  finite_zero : ⊥ < g 0 ∧ g 0 < ⊤
  monotone : Monotone g

end Function

-- Proof sketch: the zero profile on `[0, +∞)` is constant, hence monotone, convex, and lower
-- semicontinuous; its value at the origin is the finite extended value `0`.
/-- The zero profile is a canonical monotone closed convex profile on `[0, +∞)`. -/
instance instIsMonotoneClosedConvexOnNonnegativeRayZero :
    Function.IsMonotoneClosedConvexOnNonnegativeRay
      (fun _ : NNReal ↦ (0 : WithTopBot ℝ)) := sorry

end

section

variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

-- Proof sketch: for `→`, evaluate the invariance condition along orthogonal maps sending a fixed
-- vector to another vector with the same norm, so `f` depends only on `‖x‖`. For `←`, a radial
-- extension is unchanged by every orthogonal transformation because such maps preserve norms.
/-- Text 12.3.5: a function on a real inner-product space is invariant under every orthogonal
transformation if and only if it is the radial extension of a profile on `[0, +∞)`. -/
theorem orthogonallyInvariant_iff_exists_radialExtension
    {α : Type v} (f : E → α) :
    (∀ U : E ≃ₗᵢ[ℝ] E, f ∘ U = f) ↔
      ∃ g : NNReal → α, f = radialExtension E g := sorry

end

section

variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
local notation "IsClosedProperConvex[ℝ]" => Function.IsClosedProperConvex (𝕜 := ℝ)

-- Proof sketch: when the ambient space is nontrivial, restrict the radial extension to the ray
-- `t ↦ t • e` for a unit vector `e`, obtaining the scalar profile, then use convexity,
-- lower semicontinuity, and
-- properness of `f` together with radial symmetry to derive the four listed ray conditions. For
-- `←`, compose a monotone closed convex ray profile with the norm; the norm is convex
-- and continuous, and monotonicity of the profile upgrades convexity along radii to convexity on
-- all of the ambient space. The nontriviality hypothesis excludes the degenerate zero space, where
-- `radialExtension g` depends only on `g 0`.
/-- In a nontrivial real normed space, a radial extension `x ↦ g(‖x‖)` is closed proper
convex exactly when
the profile `g` is convex on `[0, +∞)`, nondecreasing, lower semicontinuous, and finite at `0`. -/
theorem radialExtension_isClosedProperConvex_iff
    {α : Type v} [TopologicalSpace (WithTopBot α)] [AddCommMonoid α] [SMul ℝ α]
    [PartialOrder (WithTopBot α)]
    [Nontrivial E] (g : NNReal → WithTopBot α) :
    IsClosedProperConvex[ℝ] (radialExtension E g) ↔
      g.IsMonotoneClosedConvexOnNonnegativeRay := sorry

end
