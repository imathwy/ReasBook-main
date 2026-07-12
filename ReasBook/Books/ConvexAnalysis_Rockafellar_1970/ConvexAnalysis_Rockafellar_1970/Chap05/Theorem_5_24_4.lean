import Mathlib.Topology.Order.LeftRightLim
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_6
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_5_24_3
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_5_24_4
import ConvexAnalysis_Rockafellar_1970.Chap05.Theorem_5_24_2
import ConvexAnalysis_Rockafellar_1970.Chap05.Theorem_5_24_3

noncomputable section

open scoped SetRel Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 5.24.4 gives the one-dimensional
  existence/identification/uniqueness package relating complete nondecreasing curves and
  subdifferential graphs of closed proper convex functions.
- `core/canonical`: the reused owners are `Function.leftDerivative`,
  `Function.rightDerivative`, `_root_.subdifferentialAt`, `_root_.subdifferentialGraph`, and
  `SetRel.IsCompleteNondecreasingCurve`.
- `bridge/view`: this file composes Theorem 5.24.2 and Theorem 5.24.3 into source-facing graph
  and uniqueness statements; it does not introduce a new primitive owner.

Scalar/codomain canonicalization checkpoint:
- this file now follows the scalar-line abstraction layer already exposed by
  Theorem 5.24.1/5.24.2/5.24.3:
  `𝕜` with `[Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]`;
- the codomain remains the canonical extended layer `WithBotTop 𝕜` used by the derivative and
  subdifferential owners;
- graph statements use the intrinsic pairing owner `_root_.subdifferentialGraph` with
  the scalar-line multiplication pairing, rather than the inner-product bridge owner
  `Function.subdifferentialGraph`.

Topology-layer checkpoint:
- this file introduces no new ambient `closure`/`interior` API surface;
- the topology-facing content used here is intrinsic to `leftLim`/`rightLim` and to the relation
  owner `IsCompleteNondecreasingCurve`.
-/

namespace Function

section

variable {𝕜 : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]

variable {φ : 𝕜 → WithBotTop 𝕜}

local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)
local notation "subgradGraph" => (_root_.subdifferentialGraph (Y := 𝕜))

/-- Canonical scalar-line pairing for subdifferential statements on the one-dimensional line. -/
local instance instHasPairingScalarLine : HasPairing 𝕜 𝕜 𝕜 where
  pairing x y := x * y

-- Proof sketch: use the source primitive with a chosen finite base point `a`.
-- Monotonicity of `φ` gives convexity of the primitive, the interval description of its
-- subdifferential graph is exactly `φ.completeNondecreasingCurve`, and the normalization
-- `f a = 0` is built into that primitive normalization at `a`.
/-- Theorem 5.24.4: if `φ` is nondecreasing and finite at a chosen base point `a`, then there
exists a closed proper convex function whose subdifferential graph is the complete
nondecreasing curve of `φ` and whose value at `a` is `0`. -/
theorem exists_isClosedProperConvex_subdifferentialGraph_eq_completeNondecreasingCurve_normalized
    (hφ_mono : Monotone φ) {a : 𝕜}
    (ha_finite : φ a ∈ Set.Ioo (⊥ : WithBotTop 𝕜) ⊤) :
    ∃ f : 𝕜 → WithBotTop 𝕜,
      IsClosedProperConvex[𝕜] f ∧
        subgradGraph f = φ.completeNondecreasingCurve ∧
          f a = 0 := sorry

-- Proof sketch: choose a finite base point from `hφ_finite`, apply the normalized existence
-- theorem above, and then forget the normalization equation.
/-- A nondecreasing extended-codomain profile that is finite somewhere is the
subdifferential graph of a closed proper convex function. -/
theorem exists_isClosedProperConvex_subdifferentialGraph_eq_completeNondecreasingCurve
    (hφ_mono : Monotone φ)
    (hφ_finite : ∃ x, φ x ∈ Set.Ioo (⊥ : WithBotTop 𝕜) ⊤) :
    ∃ f : 𝕜 → WithBotTop 𝕜,
      IsClosedProperConvex[𝕜] f ∧
        subgradGraph f = φ.completeNondecreasingCurve := sorry

-- Proof sketch: combine Theorem 5.24.2, which writes `∂[𝕜]f(x)` as the interval between the
-- one-sided derivatives of `f`, with Theorem 5.24.3, which rewrites the same interval in terms
-- of the left and right limits of `φ`.
/-- If the subdifferential graph of `f` is the complete nondecreasing curve of `φ`, then each
fiber `∂[𝕜]f(x)` is the interval cut out by `φ.leftLim x` and `φ.rightLim x`. -/
theorem subdifferentialAt_eq_of_subdifferentialGraph_eq_completeNondecreasingCurve
    {f : 𝕜 → WithBotTop 𝕜}
    (hf : IsClosedProperConvex[𝕜] f)
    (hgraph : subgradGraph f = φ.completeNondecreasingCurve) (x : 𝕜) :
    ∂[𝕜]f(x) =
      {xStar : 𝕜 | (xStar : WithBotTop 𝕜) ∈ Set.Icc (φ.leftLim x) (φ.rightLim x)} := sorry

-- Proof sketch: rewrite `∂[𝕜]f(x)` both by the previous fiber theorem and by Theorem 5.24.2; the
-- left endpoints of the two interval descriptions must agree.
/-- Under the graph identity `_root_.subdifferentialGraph f = φ.completeNondecreasingCurve`, the
left derivative of `f` is the left limit `φ_-`. -/
theorem leftDerivative_eq_leftLim_of_subdifferentialGraph_eq_completeNondecreasingCurve
    {f : 𝕜 → WithBotTop 𝕜} (hf : IsClosedProperConvex[𝕜] f)
    (hgraph : subgradGraph f = φ.completeNondecreasingCurve) (x : 𝕜) :
    leftDerivative f x = φ.leftLim x := sorry

-- Proof sketch: rewrite `∂[𝕜]f(x)` both by the previous fiber theorem and by Theorem 5.24.2; the
-- right endpoints of the two interval descriptions must agree.
/-- Under the graph identity `_root_.subdifferentialGraph f = φ.completeNondecreasingCurve`, the
right derivative of `f` is the right limit `φ_+`. -/
theorem rightDerivative_eq_rightLim_of_subdifferentialGraph_eq_completeNondecreasingCurve
    {f : 𝕜 → WithBotTop 𝕜} (hf : IsClosedProperConvex[𝕜] f)
    (hgraph : subgradGraph f = φ.completeNondecreasingCurve) (x : 𝕜) :
    rightDerivative f x = φ.rightLim x := sorry

-- Proof sketch: monotonicity gives the standard inequalities
-- `φ.leftLim x ≤ φ x ≤ φ.rightLim x`; combine these with the two derivative-identification
-- theorems above.
/-- If `_root_.subdifferentialGraph f = φ.completeNondecreasingCurve`, then `φ` lies pointwise
between the left and right derivatives of `f`. -/
theorem derivative_sandwich_of_subdifferentialGraph_eq_completeNondecreasingCurve
    {f : 𝕜 → WithBotTop 𝕜} (hf : IsClosedProperConvex[𝕜] f) (hφ_mono : Monotone φ)
    (hgraph : subgradGraph f = φ.completeNondecreasingCurve) (x : 𝕜) :
    leftDerivative f x ≤ φ x ∧ φ x ≤ rightDerivative f x := sorry

-- Proof sketch: apply Theorem 5.24.3 to the derivative sandwich assumption on `g` to identify
-- `g`'s left and right derivatives with `φ.leftLim` and `φ.rightLim`, then invoke Theorem 5.24.2
-- to recover the complete nondecreasing-curve graph.
/-- A closed proper convex function whose one-sided derivatives sandwich `φ` has subdifferential
graph equal to `φ.completeNondecreasingCurve`. -/
theorem subdifferentialGraph_eq_completeNondecreasingCurve_of_derivative_sandwich
    {g : 𝕜 → WithBotTop 𝕜} (hg : IsClosedProperConvex[𝕜] g)
    (hφ : ∀ x, leftDerivative g x ≤ φ x ∧ φ x ≤ rightDerivative g x) :
    subgradGraph g = φ.completeNondecreasingCurve := sorry

-- Proof sketch: equal subdifferential graphs force equal one-dimensional subdifferential fibers.
-- Theorem 5.24.2 then gives equality of left and right derivatives, and the one-variable
-- uniqueness argument yields equality up to an additive constant.
/-- Any two closed proper convex functions with the same subdifferential graph differ by an
additive constant. -/
theorem eq_add_const_of_subdifferentialGraph_eq
    {f g : 𝕜 → WithBotTop 𝕜}
    (hf : IsClosedProperConvex[𝕜] f) (hg : IsClosedProperConvex[𝕜] g)
    (hgraph : subgradGraph f = subgradGraph g) :
    ∃ α : 𝕜, g = fun x ↦ f x + α := sorry

-- Proof sketch: first convert the derivative sandwich on `g` into the graph identity
-- `_root_.subdifferentialGraph g = φ.completeNondecreasingCurve`. Then compare with the fixed
-- graph identity for `f` and apply the generic graph-equality uniqueness theorem.
/-- If `f` realizes the complete nondecreasing curve of `φ` and `g` is another closed proper
convex function whose one-sided derivatives sandwich `φ`, then `g` differs from `f` by an
additive constant. -/
theorem eq_add_const_of_derivative_sandwich_of_subdifferentialGraph_eq_completeNondecreasingCurve
    {f g : 𝕜 → WithBotTop 𝕜}
    (hf : IsClosedProperConvex[𝕜] f) (hg : IsClosedProperConvex[𝕜] g)
    (hfgraph : subgradGraph f = φ.completeNondecreasingCurve)
    (hgφ : ∀ x, leftDerivative g x ≤ φ x ∧ φ x ≤ rightDerivative g x) :
    ∃ α : 𝕜, g = fun x ↦ f x + α := sorry

end

end Function

namespace SetRel

section

variable {𝕜 : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]

local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)
local notation "subgradGraph" => (_root_.subdifferentialGraph (Y := 𝕜))

/-- Canonical scalar-line pairing for relation-level one-dimensional subdifferential graphs. -/
local instance instHasPairingScalarLine : HasPairing 𝕜 𝕜 𝕜 where
  pairing x y := x * y

-- Proof sketch: unpack the witness profile `φ` from `hΓ`, choose a finite base point from the
-- witness data in `Γ.IsCompleteNondecreasingCurve`, and then apply the witness-side existence
-- theorem in the `Function` namespace.
/-- Every complete nondecreasing curve in `𝕜 × 𝕜` is the subdifferential graph of a closed proper
convex function. -/
theorem exists_isClosedProperConvex_subdifferentialGraph_eq_of_isCompleteNondecreasingCurve
    {Γ : SetRel 𝕜 𝕜} (hΓ : Γ.IsCompleteNondecreasingCurve) :
    ∃ f : 𝕜 → WithBotTop 𝕜,
      IsClosedProperConvex[𝕜] f ∧
        subgradGraph f = Γ := sorry

end

end SetRel
