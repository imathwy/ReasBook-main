import Mathlib
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.Recall
import Mathlib.Topology.Order.LeftRightLim

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_5_24_4 (from Chap05) -/
noncomputable section

open scoped SetRel

universe u v

/-!
Source/core/bridge triage for this item.

- `source-facing`: Definition 5.24.4 uses one-sided limits to describe complete non-decreasing
  curves via witness profiles.
- `core/canonical`: the chapter owner for the curve notion itself is the intrinsic order-theoretic
  owner `IsMaxChain (· ≤ ·)` on `ι × α`.
- `bridge/view`: `Function.completeNondecreasingCurve` is retained as the witness-side
  interval-fiber realization built from `leftLim` and `rightLim`.

Domain-style sampling used here:
- `Function.leftLim` and `Function.rightLim` from
  `.lake/packages/mathlib/Mathlib/Topology/Order/LeftRightLim.lean`, which are the canonical
  owners for strict one-sided limits;
- the intrinsic interval owner `Set.Icc` in the chapter's canonical extended codomain
  `WithTopBot α`, expressing membership in the source interval fiber `[φ_-(x), φ_+(x)]`;
- `subdifferentialGraph` from
  `ConvexAnalysis_Rockafellar_1970/Chap05/Definition_5_24_3.lean`, which fixes the chapter's
  owner level for multivalued graphs as `SetRel`.

Primitive data vs derived API:
- primitive source-facing owner: mathlib's canonical `IsMaxChain (· ≤ ·) Γ` on relations;
- derived bridge/view API: the witness-side relation `φ.completeNondecreasingCurve` and its
  membership simplification.
-/

namespace Function

section

variable {ι : Type u} [LinearOrder ι]
variable {α : Type v} [Preorder α] [TopologicalSpace (WithTopBot α)]

/- Definition 5.24.4, witness-side bridge: the non-decreasing function `φ` determines the graph
relation whose fiber over `x` is the interval cut out by `φ_-(x)` and `φ_+(x)` in the ambient
extended codomain. In the source specialization `ι = ℝ`, `α = ℝ`, this is exactly
`[φ_-(x), φ_+(x)] ∩ ℝ`. -/
abbrev completeNondecreasingCurve (φ : ι → WithTopBot α) : SetRel ι α :=
  {p | (p.2 : WithTopBot α) ∈ Set.Icc (φ.leftLim p.1) (φ.rightLim p.1)}

/-- Pointwise membership in `φ.completeNondecreasingCurve` is exactly interval membership in
`[φ_-(x), φ_+(x)]` inside the ambient codomain. -/
@[simp] theorem mem_completeNondecreasingCurve_iff_mem_Icc
    {φ : ι → WithTopBot α} {x : ι} {xStar : α} :
    x ~[φ.completeNondecreasingCurve] xStar ↔
      (xStar : WithTopBot α) ∈ Set.Icc (φ.leftLim x) (φ.rightLim x) :=
  Iff.rfl

/-- Pointwise membership in `φ.completeNondecreasingCurve` is exactly
`φ_-(x) ≤ x⋆ ≤ φ_+(x)` in the ambient codomain order. -/
@[simp] theorem mem_completeNondecreasingCurve
    {φ : ι → WithTopBot α} {x : ι} {xStar : α} :
    x ~[φ.completeNondecreasingCurve] xStar ↔
      φ.leftLim x ≤ (xStar : WithTopBot α) ∧
        (xStar : WithTopBot α) ≤ φ.rightLim x := by
  simp [Set.mem_Icc]

end

end Function

namespace SetRel

section

variable {ι : Type u} [LE ι]
variable {α : Type v} [LE α]

/- Layer target: `source-facing`. The owner itself is the canonical order owner
`IsMaxChain (· ≤ ·)` on relations; the function-side graph construction above is a bridge/view. -/

/-- Canonical owner for complete non-decreasing curves: maximal chains for the coordinatewise
order on `ι × α`. -/
abbrev IsCompleteNondecreasingCurve (Γ : SetRel ι α) : Prop :=
  IsMaxChain (· ≤ ·) Γ

/-- Definitional bridge to the canonical order owner. -/
@[simp] theorem isCompleteNondecreasingCurve_iff_isMaxChain (Γ : SetRel ι α) :
    Γ.IsCompleteNondecreasingCurve ↔ IsMaxChain (· ≤ ·) Γ :=
  Iff.rfl

end

end SetRel

/-! ### Proposition_5_24_4 (from Chap05) -/
open scoped Rockafellar SetRel

universe u v w

section

variable {X : Type u} {Y : Type v} {𝕜 : Type w}
variable [Sub X] [Sub Y] [HasPairing X Y 𝕜]
variable [AddCommGroup 𝕜] [LE 𝕜] [AddRightMono 𝕜]
variable [HasPairingSubLeft X Y 𝕜] [HasPairingSubRight X Y 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Proposition 5.24.4 says that cyclic monotonicity implies ordinary
  monotonicity for a multivalued mapping.
- `core/canonical`: this chapter already owns cyclic monotonicity and monotonicity as the relation
  predicates `SetRel.CyclicallyMonotone` and `SetRel.Monotone` on `ρ : SetRel X Y`, with the
  pairing codomain explicit in the owner parameter and surfaced via the chapter notation
  `CMon[𝕜](ρ)` and `Mon[𝕜](ρ)`.
- `bridge/view`: Proposition 5.24.4 is the owner-level implication from the stronger cyclic
  relation predicate to the weaker monotone one; strong-dual relation views are just later
  specialization of this canonical statement.

Domain-style sampling used here:
- `SetRel.CyclicallyMonotone` from
  `ConvexAnalysis_Rockafellar_1970/Chap05/Definition_5_24_5.lean`;
- `SetRel.Monotone` from
  `ConvexAnalysis_Rockafellar_1970/Chap05/Definition_5_24_7.lean`;
- subtraction-compatible pairing owners `HasPairingSubLeft` and `HasPairingSubRight` from
  `ConvexAnalysis_Rockafellar_1970/Chap01/HasPairing.lean`, the primitive algebraic layer
  for the source cycle-to-monotonicity rewrite.

Primitive data vs derived API:
- primitive hypothesis: `CMon[𝕜](ρ)`;
- primitive ambient owner data used by the core theorem: subtraction-compatible pairing owners in
  the left and right arguments;
- derived conclusion: `Mon[𝕜](ρ)`.

Layer target: `core/canonical`. This item is the direct canonical implication between the chapter's
two owner predicates on relations.
-/

namespace SetRel.CyclicallyMonotone

-- Proof sketch: specialize cyclic monotonicity to a cycle of length `2`, obtaining
-- `⟪x₁ - x₀, y₀⟫ₚ + ⟪x₀ - x₁, y₁⟫ₚ ≤ 0`. Rewriting with subtraction-compatible pairing identities
-- gives `-(⟪x₁ - x₀, y₁ - y₀⟫ₚ) ≤ 0`, hence monotonicity.
/-- Proposition 5.24.4 at the canonical owner layer: cyclic monotonicity implies monotonicity
whenever the pairing is subtraction-compatible in each argument. -/
theorem monotone {ρ : SetRel X Y} (hρ : CMon[𝕜](ρ)) :
    Mon[𝕜](ρ) := by
  refine ⟨?_⟩
  intro x₀ x₁ y₀ y₁ hx₀ hx₁
  have hsum : (⟪x₁ - x₀, y₀⟫ₚ + ⟪x₀ - x₁, y₁⟫ₚ : 𝕜) ≤ 0 := by
    simpa [Fin.sum_univ_two] using
      hρ.sum_nonpos 1 ![x₀, x₁] ![y₀, y₁] (by
        intro i
        fin_cases i
        · simpa using hx₀
        · simpa using hx₁)
  have hrewrite :
      (⟪x₁ - x₀, y₀⟫ₚ + ⟪x₀ - x₁, y₁⟫ₚ : 𝕜) =
        -(⟪x₁ - x₀, y₁ - y₀⟫ₚ : 𝕜) := by
    calc
      (⟪x₁ - x₀, y₀⟫ₚ + ⟪x₀ - x₁, y₁⟫ₚ : 𝕜)
          = (⟪x₁, y₀⟫ₚ - ⟪x₀, y₀⟫ₚ) + (⟪x₀, y₁⟫ₚ - ⟪x₁, y₁⟫ₚ) := by
              rw [HasPairingSubLeft.pairing_sub_left x₁ x₀ y₀,
                HasPairingSubLeft.pairing_sub_left x₀ x₁ y₁]
      _ = -((⟪x₁, y₁⟫ₚ - ⟪x₀, y₁⟫ₚ) - (⟪x₁, y₀⟫ₚ - ⟪x₀, y₀⟫ₚ)) := by
            abel
      _ = -((⟪x₁ - x₀, y₁⟫ₚ : 𝕜) - ⟪x₁ - x₀, y₀⟫ₚ) := by
            rw [HasPairingSubLeft.pairing_sub_left x₁ x₀ y₁,
              HasPairingSubLeft.pairing_sub_left x₁ x₀ y₀]
      _ = -(⟪x₁ - x₀, y₁ - y₀⟫ₚ : 𝕜) := by
            rw [← HasPairingSubRight.pairing_sub_right (x₁ - x₀) y₁ y₀]
  have hsub : (0 : 𝕜) - (⟪x₁ - x₀, y₁ - y₀⟫ₚ : 𝕜) ≤ 0 := by
    simpa [hrewrite] using hsum
  exact sub_nonpos.mp hsub

/-- Canonical owner bridge: cyclic monotonicity implies monotonicity. This instance lets
downstream declarations use `Mon[𝕜](ρ)` via typeclass inference whenever
`[CMon[𝕜](ρ)]` is available. -/
instance toMonotone (ρ : SetRel X Y) [hρ : CMon[𝕜](ρ)] : Mon[𝕜](ρ) :=
  monotone hρ

end SetRel.CyclicallyMonotone

end

/-! ### Remark_5_24_4 (from Chap05) -/
namespace SetRel

section

/-- The canonical one-dimensional pairing on `ℝ` is ordinary multiplication. -/
local instance instHasPairingRealLine : HasPairing ℝ ℝ ℝ where
  pairing x y := x * y

/-!
Source/core/bridge triage for this item.

- `source-facing`: Remark 5.24.4 records three one-dimensional identifications: monotone
  relations are exactly the coordinatewise chains in `ℝ × ℝ`, maximal monotone relations are
  exactly the complete non-decreasing curves, and monotone and cyclically monotone relations
  coincide on the real line.
- `core/canonical`: the owner abstractions already exist as `SetRel.Monotone`,
  `SetRel.CyclicallyMonotone`, `SetRel.IsCompleteNondecreasingCurve`, and mathlib's order-theoretic
  owners `IsChain`, `IsMaxChain`, and `Maximal`.
- `bridge/view`: the source phrase "totally ordered in `ℝ²` with respect to the coordinatewise
  partial ordering" is exactly `IsChain (· ≤ ·) ρ`, viewing a relation `ρ : SetRel ℝ ℝ` as its
  graph subset of `ℝ × ℝ`.

Domain-style sampling used here:
- `SetRel.Monotone` from `Definition_5_24_7`;
- `SetRel.CyclicallyMonotone` from `Definition_5_24_5`;
- `SetRel.IsCompleteNondecreasingCurve` and
  `SetRel.isCompleteNondecreasingCurve_iff_isMaxChain` from `Definition_5_24_4`;
- `Maximal`, `IsChain`, and `IsMaxChain` from mathlib's order-theoretic API.

Primitive data vs derived API:
- primitive owner input: a relation `ρ : SetRel ℝ ℝ`;
- primitive source-facing predicates: `ρ.Monotone ℝ`, `ρ.CyclicallyMonotone ℝ`,
  `ρ.IsCompleteNondecreasingCurve`;
- derived bridge/view API: the coordinatewise-chain formulation `IsChain (· ≤ ·) ρ` and the
  maximality translation `Maximal (·.Monotone ℝ) ρ`.
-/

-- Proof sketch: unfold `SetRel.Monotone` with the real-line pairing
-- `⟪x, y⟫ₚ = x * y`. For two graph points `(x₀, x₀⋆)` and `(x₁, x₁⋆)`, the inequality
-- `(x₁ - x₀) * (x₁⋆ - x₀⋆) ≥ 0` is equivalent to coordinatewise comparability in `ℝ × ℝ`,
-- yielding exactly the chain condition for the graph.
/-- Remark 5.24.4: on the real line, a multivalued mapping is monotone exactly when its graph is
totally ordered in `ℝ × ℝ` for the coordinatewise partial order. -/
theorem monotone_iff_graph_isChain (ρ : SetRel ℝ ℝ) :
    ρ.Monotone ℝ ↔ IsChain (· ≤ ·) ρ := sorry

-- Proof sketch: combine `monotone_iff_graph_isChain` with
-- `isCompleteNondecreasingCurve_iff_isMaxChain`. Maximal monotonicity means maximality among
-- coordinatewise chains in `ℝ × ℝ`, and Remark 5.24.3 identifies those maximal chains with
-- complete non-decreasing curves.
/-- A relation on the real line is maximal monotone exactly when its graph is a complete
non-decreasing curve. -/
theorem maximal_monotone_iff_isCompleteNondecreasingCurve (ρ : SetRel ℝ ℝ) :
    Maximal (·.Monotone ℝ) ρ ↔ ρ.IsCompleteNondecreasingCurve := sorry

-- Proof sketch: the forward implication is Proposition 5.24.4. For the converse, extend a
-- monotone graph on `ℝ` to a maximal monotone one, use the previous theorem to identify that
-- extension with a complete non-decreasing curve, then combine Theorems 5.24.5 and 5.24.12 to
-- obtain cyclic monotonicity and restrict the cyclic inequality back to the original graph.
/-- On the real line, monotone and cyclically monotone relations coincide. -/
theorem monotone_iff_cyclicallyMonotone (ρ : SetRel ℝ ℝ) :
    ρ.Monotone ℝ ↔ ρ.CyclicallyMonotone ℝ := sorry

end

end SetRel

/-! ### Theorem_5_24_4 (from Chap05) -/
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

/-! ### Definition_5_24_5 (from Chap05) -/
open scoped BigOperators Rockafellar SetRel

universe u v w

section

variable {X : Type u} {Y : Type v} [Sub X]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Definition 5.24.5 introduces cyclic monotonicity for a multivalued mapping.
- `core/canonical`: cyclic inequalities in this project are pairing-first owners, so the primitive
  layer should use `SetRel X Y` with the chapter pairing notation `⟪·, ·⟫ₚ`, not an
  `InnerProductSpace`-specific self-relation owner.
- `bridge/view`: the source wording “`xᵢ⋆ ∈ ρ(xᵢ)`” is relation membership `xᵢ ~[ρ] xᵢ⋆`.

Domain-style sampling used here:
- `SetRel` together with its relation notation from mathlib's `Data/Rel`, the canonical owner
  layer for multivalued mappings;
- the codomain-parametric pairing layer `HasPairing X Y L` together with an ordered additive
  codomain structure `[LE L] [AddCommMonoid L]`, and the project notation `⟪·, ·⟫ₚ` from
  `Items/Chap01/HasPairing.lean`, the canonical dual-evaluation abstraction layer;
- `Function.subdifferentialGraph` from `Items/Chap05/Definition_5_24_3.lean`, which already
  places the subdifferential mapping in the same `SetRel` owner language;
- `Function.subdifferentialAt` from `Items/Chap05/Definition_23_0_6.lean`, whose graph is later
  compared with arbitrary cyclically monotone relations.

Primitive data vs derived API:
- primitive owner: a relation `ρ : SetRel X Y`;
- primitive source data inside the definition: finite cyclic families
  `x : Fin (m + 1) → X` and `xStar : Fin (m + 1) → Y` with graph-membership hypotheses
  `x i ~[ρ] xStar i`;
- derived API: the specification theorem `cyclicallyMonotone_iff` and the named owner accessor
  `SetRel.CyclicallyMonotone.sum_nonpos`.

Ambient-assumption minimization:
- cyclic monotonicity uses only additive differences in the primal variable and scalar pairing
  evaluations against graph points;
- no normed or inner-product structure is primitive data for this owner.

Layer target: `source-facing`. This file owns the notion itself at the canonical relation-plus-
pairing layer rather than through a separate “multivalued mapping” structure.
-/

namespace SetRel

/-- Definition 5.24.5: a multivalued mapping is cyclically monotone when every finite cycle in
its graph satisfies the source cyclic pairing inequality. The canonical owner is the relation
itself, so the source condition is stated directly on `ρ : SetRel X Y`; the pairing codomain
parameter `L` is explicit in the owner because it is mathematically essential and not recoverable
from `ρ` alone. -/
@[mk_iff cyclicallyMonotone_iff]
class CyclicallyMonotone (ρ : SetRel X Y) (L : Type w)
    [LE L] [AddCommMonoid L] [pairing : HasPairing X Y L] : Prop where
  sum_nonpos (m : ℕ) (x : Fin (m + 1) → X) (xStar : Fin (m + 1) → Y)
      (hp : ∀ i, x i ~[ρ] xStar i) :
    ∑ i : Fin (m + 1), ⟪x (i + 1) - x i, xStar i⟫ₚ ≤ (0 : L)

/-- Source-facing notation for cyclic monotonicity with the ambient pairing instance. -/
scoped[SetRel] notation "CMon[" L "](" ρ ")" =>
  SetRel.CyclicallyMonotone ρ L

/-- Canonical explicit-pairing notation for cyclic monotonicity. The codomain is determined by the
pairing instance, so this surface avoids redundant `L` noise. -/
scoped[SetRel] notation "CMonPair[" pairing "](" ρ ")" =>
  (@SetRel.CyclicallyMonotone _ _ _ ρ _ _ _ pairing)

namespace CyclicallyMonotone

/-!
Owner-level pairing transport API.

`SetRel.CyclicallyMonotone` is intentionally pairing-parametric. When two pairing instances on the
same ambient types are pointwise equal, cyclic monotonicity transports directly between them.
This keeps downstream theorem surfaces at the owner layer instead of forcing explicit
instance-expanded `@...` proofs.
-/

/-- If two pairing instances on the same `(X, Y, L)` are pointwise equal, cyclic monotonicity of
`ρ` transfers from the first pairing to the second. -/
theorem of_pairing_eq {ρ : SetRel X Y} {L : Type w}
    [LE L] [AddCommMonoid L]
    {pairing₁ pairing₂ : HasPairing X Y L}
    (hρ : CMonPair[pairing₁](ρ))
    (hpair : ∀ x : X, ∀ y : Y, pairing₁.pairing x y = pairing₂.pairing x y) :
    CMonPair[pairing₂](ρ) := by
  refine ⟨?_⟩
  intro m x xStar hp
  have hineq :
      ∑ i : Fin (m + 1), pairing₁.pairing (x (i + 1) - x i) (xStar i) ≤ (0 : L) := by
    exact hρ.sum_nonpos m x xStar hp
  have hsum :
      (∑ i : Fin (m + 1), pairing₂.pairing (x (i + 1) - x i) (xStar i)) =
        (∑ i : Fin (m + 1), pairing₁.pairing (x (i + 1) - x i) (xStar i)) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact (hpair (x (i + 1) - x i) (xStar i)).symm
  rw [hsum]
  exact hineq

/-- Cyclic monotonicity is invariant under replacement of the pairing by a pointwise equal one. -/
theorem iff_pairing_eq {ρ : SetRel X Y} {L : Type w}
    [LE L] [AddCommMonoid L]
    {pairing₁ pairing₂ : HasPairing X Y L}
    (hpair : ∀ x : X, ∀ y : Y, pairing₁.pairing x y = pairing₂.pairing x y) :
    CMonPair[pairing₁](ρ) ↔
      CMonPair[pairing₂](ρ) := by
  constructor
  · intro hρ
    exact of_pairing_eq (pairing₁ := pairing₁) (pairing₂ := pairing₂) hρ hpair
  · intro hρ
    exact of_pairing_eq (pairing₁ := pairing₂) (pairing₂ := pairing₁) hρ
      (fun x y ↦ (hpair x y).symm)

end CyclicallyMonotone

end SetRel

end

/-! ### Remark_5_24_5 (from Chap05) -/
noncomputable section

open scoped RealInnerProductSpace

/-!
Source/core/bridge triage for this item.

- `source-facing`: Remark 5.24.5 records that in dimensions `n > 1` monotonicity is strictly
  weaker than cyclic monotonicity, and it says that a linear example already shows the
  distinction.
- `core/canonical`: the chapter already owns these notions as `SetRel.Monotone` and
  `SetRel.CyclicallyMonotone` on graph relations, while single-valued mappings are canonically
  viewed as relations through `Function.graph`.
- `bridge/view`: the source's "linear mapping" is therefore most naturally a linear self-map
  `Q : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)` together with the relation
  `(Q : _ → _).graph`.

Domain-style sampling used here:
- `SetRel.CyclicallyMonotone` from `Definition_5_24_5`;
- `SetRel.Monotone` from `Definition_5_24_7`;
- `Function.graph` from mathlib's relation API, the canonical bridge from a single-valued map to
  a graph relation;
- `SetRel.maximal_cyclicallyMonotone_iff_exists_isClosedProperConvex_subdifferentialGraph_eq` from
  `Theorem_5_24_12`, which confirms that the chapter's owner level for these notions is the graph
  relation itself.

Primitive data vs derived API:
- primitive source-facing data: the dimension parameter `n` with `1 < n`;
- primitive witness data promised by the remark: a linear map `Q`;
- derived owner-level properties: monotonicity and failure of cyclic monotonicity of the graph
  relation of `Q`.

Layer target: `source-facing`. The remark is an existence statement about linear mappings on
`ℝⁿ`, expressed directly through the canonical graph-relation owners already fixed by the chapter.
-/

section

local instance (n : ℕ) :
    HasPairing (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) ℝ :=
  instHasPairingOfHasLinearPairing

-- Proof sketch: use the standard quarter-turn on a two-dimensional coordinate plane, whose
-- symmetric part is zero and hence whose graph is monotone, while the map is not symmetric and so
-- fails the linear cyclic-monotonicity criterion. For `n > 1`, extend this `2 × 2` skew block by
-- zero on the remaining coordinates.
/-- Remark 5.24.5: when `n > 1`, there exists a linear self-map of `ℝⁿ` whose graph is monotone
but not cyclically monotone. This gives the source's linear example showing that cyclic
monotonicity is strictly stronger than monotonicity in dimensions greater than one. -/
theorem exists_linearMap_graph_monotone_not_cyclicallyMonotone
    {n : ℕ} (hn : 1 < n) :
    ∃ Q : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n),
      ((Q : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)).graph).Monotone ℝ ∧
        ¬ ((Q : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)).graph).CyclicallyMonotone ℝ :=
  sorry

end

/-! ### Theorem_5_24_5 (from Chap05) -/
noncomputable section

open scoped SetRel

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 5.24.5 characterizes exactly which relations `Γ ⊆ ℝ × ℝ` occur as
  graphs of one-dimensional subdifferential mappings of closed proper convex functions, and it
  adds the uniqueness-up-to-constant clause for the realizing function.
- `core/canonical`: the project already owns the relevant notions as the relation predicate
  `SetRel.IsCompleteNondecreasingCurve Γ`, the graph owner
  `_root_.subdifferentialGraph (Y := ℝ) f`, and the admissibility owner
  `Function.IsClosedProperConvex`.
- `bridge/view`: Theorem 5.24.4 already provides the two source halves separately: the existence
  direction for complete nondecreasing curves and the uniqueness theorem for equal
  subdifferential graphs. The current item packages those canonical pieces into the source-facing
  characterization theorem.

Domain-style sampling used here:
- `SetRel.IsCompleteNondecreasingCurve` from
  `ConvexAnalysis_Rockafellar_1970/Chap05/Definition_5_24_4.lean`;
- `Function.subdifferentialGraph` from
  `ConvexAnalysis_Rockafellar_1970/Chap05/Definition_5_24_3.lean`;
- `SetRel.exists_isClosedProperConvex_subdifferentialGraph_eq_of_isCompleteNondecreasingCurve`
  from `ConvexAnalysis_Rockafellar_1970/Chap05/Theorem_5_24_4.lean`;
- `Function.eq_add_const_of_subdifferentialGraph_eq` from
  `ConvexAnalysis_Rockafellar_1970/Chap05/Theorem_5_24_4.lean`.

Primitive data vs derived API:
- primitive source-facing owner input: a relation `Γ : SetRel ℝ ℝ`;
- primitive witness in the existence clause: a function `f : ℝ → WithBotTop ℝ` with
  `f.IsClosedProperConvex`;
- derived clause: if two such functions have graph `Γ`, then they differ by an additive real
  constant.

Layer target: `source-facing`. The main labeled entry is the characterization of the admissible
graphs; the uniqueness statement is kept as a companion theorem rather than being folded into a
large conjunction.

Scalar/codomain canonicalization checkpoint:
- this item remains at the one-dimensional real scalar layer because its primitive reused owners
  (`_root_.subdifferentialGraph`, `SetRel.IsCompleteNondecreasingCurve`, and the Chapter 24
  maximality bridges) are all the `ℝ`-line theorem surfaces for this chapter, not a deferred
  specialization from a scalar-parametric upstream owner in this file;
- the codomain remains `WithBotTop ℝ` because the realizing-function owner
  `Function.IsClosedProperConvex` and the one-dimensional subdifferential graph owner already live
  there upstream; this file only repackages that owner layer.

Topology-language checkpoint:
- no new ambient `closure`/`interior` statement is introduced in this packaging theorem;
- the theorem surface is purely relation/graph classification, so there is no intrinsic-vs-ambient
  topology reformulation to perform in this file.
-/

namespace SetRel

local notation "IsClosedProperConvex[ℝ]" => Function.IsClosedProperConvex (𝕜 := ℝ)
local notation "subgradGraph" =>
  (fun f : ℝ → WithBotTop ℝ ↦
    @_root_.subdifferentialGraph ℝ _ _ _ ℝ _ _ _ f ℝ SetRel.instHasPairingRealLine)
local notation "subgradGraphScalarLine" =>
  (fun f : ℝ → WithBotTop ℝ ↦
    @_root_.subdifferentialGraph ℝ _ _ _ ℝ _ _ _ f ℝ Function.instHasPairingScalarLine)

/-- The scalar-line pairing owner used in Theorem 5.24.4 and the real-line pairing owner used in
Remark 5.24.4 induce the same intrinsic graph relation on `ℝ`. -/
private theorem subgradGraph_scalarLine_eq_subgradGraph (f : ℝ → WithBotTop ℝ) :
    subgradGraphScalarLine f = subgradGraph f := by
  exact _root_.subdifferentialGraph_eq_of_pairing_eq
    (f := f) (Y := ℝ)
    (pairing₁ := Function.instHasPairingScalarLine)
    (pairing₂ := SetRel.instHasPairingRealLine)
    (fun _ _ ↦ rfl)

/-- Bridge on the real line: the Euclidean graph owner `Function.subdifferentialGraph` agrees with
the intrinsic scalar-line subdifferential graph owner. -/
private theorem function_subdifferentialGraph_eq_subgradGraph (f : ℝ → WithBotTop ℝ) :
    Function.subdifferentialGraph f = subgradGraph f := by
  ext p
  rcases p with ⟨x, xStar⟩
  constructor
  · intro hx
    rw [@_root_.mem_subdifferentialGraph ℝ _ _ _ ℝ _ _ _ f ℝ SetRel.instHasPairingRealLine x
      xStar]
    rw [@_root_.mem_subdifferentialAt_pairing ℝ _ _ _ ℝ _ _ _ f x ℝ SetRel.instHasPairingRealLine
      xStar]
    rw [Function.mem_subdifferentialGraph, Function.mem_subdifferentialAt] at hx
    intro z
    have hinner : (inner ℝ xStar (z - x) : ℝ) = (z - x) * xStar := by
      calc
        inner ℝ xStar (z - x) = (starRingEnd ℝ) xStar * (z - x) := by
          simpa using (RCLike.inner_apply' (x := xStar) (y := (z - x)))
        _ = (z - x) * xStar := by simp [mul_comm]
    have hxz := hx z
    rw [hinner] at hxz
    exact hxz
  · intro hx
    rw [Function.mem_subdifferentialGraph, Function.mem_subdifferentialAt]
    rw [@_root_.mem_subdifferentialGraph ℝ _ _ _ ℝ _ _ _ f ℝ SetRel.instHasPairingRealLine x
      xStar] at hx
    rw [@_root_.mem_subdifferentialAt_pairing ℝ _ _ _ ℝ _ _ _ f x ℝ SetRel.instHasPairingRealLine
      xStar] at hx
    intro z
    have hinner : (inner ℝ xStar (z - x) : ℝ) = (z - x) * xStar := by
      calc
        inner ℝ xStar (z - x) = (starRingEnd ℝ) xStar * (z - x) := by
          simpa using (RCLike.inner_apply' (x := xStar) (y := (z - x)))
        _ = (z - x) * xStar := by simp [mul_comm]
    have hxz := hx z
    rw [hinner]
    exact hxz

-- Proof sketch: combine the forward direction from the one-dimensional intrinsic
-- `_root_.subdifferentialGraph` owner with the converse maximal-cyclic bridge.
/-- Theorem 5.24.5: a relation `Γ ⊆ ℝ × ℝ` is a complete non-decreasing curve exactly when it is
the graph of the subdifferential mapping of some closed proper convex function on `ℝ`. -/
theorem isCompleteNondecreasingCurve_iff_exists_isClosedProperConvex_subdifferentialGraph_eq
    (Γ : SetRel ℝ ℝ) :
    Γ.IsCompleteNondecreasingCurve ↔
      ∃ f : ℝ → WithBotTop ℝ,
        IsClosedProperConvex[ℝ] f ∧ subgradGraph f = Γ := by
  -- Theorem 5.24.12 now runs directly at the intrinsic pairing owner layer, so we instantiate it
  -- with the real-line multiplication pairing used by `subgradGraph`.
  let CycRealLine : SetRel ℝ ℝ → Prop := fun ρ =>
    CMonPair[SetRel.instHasPairingRealLine](ρ)
  let MonRealLine : SetRel ℝ ℝ → Prop := fun ρ =>
    Mon[SetRel.instHasPairingRealLine, ℝ](ρ)
  constructor
  · intro hΓ
    rcases
        exists_isClosedProperConvex_subdifferentialGraph_eq_of_isCompleteNondecreasingCurve hΓ
      with
      ⟨f, hf, hgraph⟩
    refine ⟨f, hf, ?_⟩
    calc
      subgradGraph f = subgradGraphScalarLine f := (subgradGraph_scalarLine_eq_subgradGraph f).symm
      _ = Γ := hgraph
  · rintro ⟨f, hf, hgraph⟩
    have hmaxCyclicRealLine :
        Maximal CycRealLine Γ := by
      letI : HasPairing ℝ ℝ ℝ := SetRel.instHasPairingRealLine
      have hmax : Maximal (fun σ : SetRel ℝ ℝ ↦ σ.CyclicallyMonotone ℝ) Γ := by
        simpa using
          (maximal_cyclicallyMonotone_iff_exists_isClosedProperConvex_subdifferentialGraph_eq
            (𝕜 := ℝ) (E := ℝ) (Y := ℝ) Γ).2 ⟨f, hf, hgraph⟩
      simpa [CycRealLine] using hmax
    have hmaxMonotoneRealLine :
        Maximal MonRealLine Γ := by
      rcases hmaxCyclicRealLine with ⟨hΓCyc, hmaxCyc⟩
      refine ⟨(by
        simpa [CycRealLine, MonRealLine] using (monotone_iff_cyclicallyMonotone Γ).2 hΓCyc), ?_⟩
      intro ρ hρMono hΓρ
      have hρCyc : CycRealLine ρ := by
        simpa [CycRealLine, MonRealLine] using (monotone_iff_cyclicallyMonotone ρ).1 hρMono
      exact hmaxCyc hρCyc hΓρ
    exact (maximal_monotone_iff_isCompleteNondecreasingCurve Γ).1
      (by simpa [MonRealLine] using hmaxMonotoneRealLine)

-- Owner-projection form of the existence direction in Theorem 5.24.5.
theorem IsCompleteNondecreasingCurve.exists_isClosedProperConvex_subdifferentialGraph_eq
    {Γ : SetRel ℝ ℝ} (hΓ : Γ.IsCompleteNondecreasingCurve) :
    ∃ f : ℝ → WithBotTop ℝ,
      IsClosedProperConvex[ℝ] f ∧ subgradGraph f = Γ :=
  (isCompleteNondecreasingCurve_iff_exists_isClosedProperConvex_subdifferentialGraph_eq Γ).1 hΓ

-- Owner-projection form of the converse direction in Theorem 5.24.5.
theorem isCompleteNondecreasingCurve_of_exists_isClosedProperConvex_subdifferentialGraph_eq
    {Γ : SetRel ℝ ℝ}
    (hΓ : ∃ f : ℝ → WithBotTop ℝ,
      IsClosedProperConvex[ℝ] f ∧ subgradGraph f = Γ) :
    Γ.IsCompleteNondecreasingCurve :=
  (isCompleteNondecreasingCurve_iff_exists_isClosedProperConvex_subdifferentialGraph_eq Γ).2 hΓ

-- Canonical uniqueness surface: equal subdifferential-graph owners imply equality up to a
-- real additive constant.
/-- Two closed proper convex functions on `ℝ` with equal subdifferential graph owners differ by an
additive real constant. -/
theorem eq_add_const_of_subdifferentialGraph_eq
    {f g : ℝ → WithBotTop ℝ}
    (hf : IsClosedProperConvex[ℝ] f) (hg : IsClosedProperConvex[ℝ] g)
    (hfg : subgradGraph f = subgradGraph g) :
    ∃ α : ℝ, g = fun x ↦ f x + α :=
  by
    have hfg_scalar : subgradGraphScalarLine f = subgradGraphScalarLine g := by
      calc
        subgradGraphScalarLine f = subgradGraph f :=
          subgradGraph_scalarLine_eq_subgradGraph f
        _ = subgradGraph g := hfg
        _ = subgradGraphScalarLine g :=
          (subgradGraph_scalarLine_eq_subgradGraph g).symm
    exact
      Function.eq_add_const_of_subdifferentialGraph_eq hf hg hfg_scalar

-- Proof sketch: convert the source-facing same-curve hypotheses to the canonical graph-equality
-- hypothesis and apply `eq_add_const_of_subdifferentialGraph_eq`.
/-- Two closed proper convex functions on `ℝ` with the same subdifferential graph `Γ` differ by
an additive real constant. -/
theorem eq_add_const_of_subdifferentialGraph_eq_same_curve
    {Γ : SetRel ℝ ℝ} {f g : ℝ → WithBotTop ℝ}
    (hf : IsClosedProperConvex[ℝ] f) (hg : IsClosedProperConvex[ℝ] g)
    (hfΓ : subgradGraph f = Γ)
    (hgΓ : subgradGraph g = Γ) :
    ∃ α : ℝ, g = fun x ↦ f x + α :=
  eq_add_const_of_subdifferentialGraph_eq hf hg (hfΓ.trans hgΓ.symm)

end SetRel

/-! ### Definition_5_24_6 (from Chap05) -/
universe u v w

namespace SetRel

section

variable {X : Type u} {Y : Type v}
variable [Sub X]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Definition 5.24.6 names those cyclically monotone multivalued mappings whose
  graphs are maximal under inclusion among cyclically monotone graphs.
- `core/canonical`: the owner abstraction is exactly the generic order-theoretic predicate
  `Maximal`, applied to the Chapter 5 owner `SetRel.CyclicallyMonotone`; no extra synonym owner is
  introduced in this file.
- `bridge/view`: the source phrase "graph is not properly contained" is exactly the order relation
  on `SetRel X Y`, so no extra wrapper or graph package belongs in the API.

Domain-style sampling used here:
- `SetRel.CyclicallyMonotone` from `Definition_5_24_5`;
- `Maximal` from mathlib's order-theoretic API;
- direct uses of `Maximal` elsewhere in the project, such as Theorem 18.2 and Corollary 37.5.2.

Primitive data vs derived API:
- primitive owner data already exist upstream: a relation `ρ : SetRel X Y`;
- primitive source-facing property reused here: `CMon[L](ρ)`;
- derived API in this file: source-facing notation for maximal cyclic monotonicity in default and
  canonical explicit-pairing forms (`MaxCMon[L](ρ)` and `MaxCMonPair[p](ρ)`), together with
  pairing-transport and strict-extension unpacking theorems.

Layer target: `core/canonical` reuse of `Maximal` on the existing cyclically monotone owner.
-/

/- Definition 5.24.6 reuses the canonical order owner `Maximal` on
`SetRel.CyclicallyMonotone`. -/
recall Maximal

/-- Source-facing notation for Definition 5.24.6: `MaxCMon[L](ρ)` means that `ρ` is maximal among
relations that are cyclically monotone with pairing codomain `L`. -/
scoped[SetRel] notation "MaxCMon[" L "](" ρ ")" =>
  Maximal (fun σ ↦ CMon[L](σ)) ρ

/-- Canonical explicit-pairing notation for maximal cyclic monotonicity. The codomain is
determined by the pairing instance, so this surface avoids redundant `L` noise. -/
scoped[SetRel] notation "MaxCMonPair[" pairing "](" ρ ")" =>
  Maximal (fun σ ↦ CMonPair[pairing](σ)) ρ

namespace MaxCMon

/-- If two pairing instances on the same `(X, Y, L)` are pointwise equal, maximal cyclic
monotonicity of `ρ` transfers from the first pairing to the second. -/
theorem of_pairing_eq {L : Type w}
    [LE L] [AddCommMonoid L]
    {pairing₁ pairing₂ : HasPairing X Y L}
    {ρ : SetRel X Y}
    (hρ : MaxCMonPair[pairing₁](ρ))
    (hpair : ∀ x : X, ∀ y : Y, pairing₁.pairing x y = pairing₂.pairing x y) :
    MaxCMonPair[pairing₂](ρ) := by
  rcases hρ with ⟨hρcyc, hmaxρ⟩
  refine ⟨?_, ?_⟩
  · exact SetRel.CyclicallyMonotone.of_pairing_eq
      (pairing₁ := pairing₁) (pairing₂ := pairing₂) hρcyc hpair
  · intro σ hσcyc hρσ
    exact hmaxρ
      (SetRel.CyclicallyMonotone.of_pairing_eq
        (pairing₁ := pairing₂) (pairing₂ := pairing₁) hσcyc (fun x y ↦ (hpair x y).symm))
      hρσ

/-- Maximal cyclic monotonicity is invariant under replacement of the pairing by a pointwise equal
one. -/
theorem iff_pairing_eq {L : Type w}
    [LE L] [AddCommMonoid L]
    {pairing₁ pairing₂ : HasPairing X Y L}
    {ρ : SetRel X Y}
    (hpair : ∀ x : X, ∀ y : Y, pairing₁.pairing x y = pairing₂.pairing x y) :
    MaxCMonPair[pairing₁](ρ) ↔
      MaxCMonPair[pairing₂](ρ) := by
  constructor
  · intro hρ
    exact of_pairing_eq (pairing₁ := pairing₁) (pairing₂ := pairing₂) hρ hpair
  · intro hρ
    exact of_pairing_eq (pairing₁ := pairing₂) (pairing₂ := pairing₁) hρ
      (fun x y ↦ (hpair x y).symm)

/-- Explicit-pairing strict-extension form of Definition 5.24.6. This owner-prefixed surface keeps
the API aligned with the `MaxCMon` notation family. -/
theorem pair_iff_forall_gt
    {L : Type w} [LE L] [AddCommMonoid L] {pairing : HasPairing X Y L} {ρ : SetRel X Y} :
    MaxCMonPair[pairing](ρ) ↔
      CMonPair[pairing](ρ) ∧
        ∀ ⦃σ : SetRel X Y⦄, ρ < σ → ¬CMonPair[pairing](σ) := by
  simpa using
    (maximal_iff_forall_gt (P := fun σ : SetRel X Y ↦ CMonPair[pairing](σ)) (x := ρ))

/-- Canonical relation-owner strict-extension form of Definition 5.24.6. -/
theorem iff_forall_gt
    {L : Type w} [LE L] [AddCommMonoid L] [HasPairing X Y L] {ρ : SetRel X Y} :
    MaxCMon[L](ρ) ↔
      CMon[L](ρ) ∧
        ∀ ⦃σ : SetRel X Y⦄, ρ < σ → ¬CMon[L](σ) := by
  simpa using
    (maximal_iff_forall_gt (P := fun σ : SetRel X Y ↦ CMon[L](σ)) (x := ρ))

end MaxCMon

/-- Explicit-pairing strict-extension form of Definition 5.24.6. -/
theorem maximalCyclicallyMonotone_iff_explicitPairing
    {L : Type w} [LE L] [AddCommMonoid L] {pairing : HasPairing X Y L} {ρ : SetRel X Y} :
    MaxCMonPair[pairing](ρ) ↔
      CMonPair[pairing](ρ) ∧
        ∀ ⦃σ : SetRel X Y⦄, ρ < σ → ¬CMonPair[pairing](σ) := by
  simpa using (MaxCMon.pair_iff_forall_gt (pairing := pairing) (ρ := ρ))

/-- Definition 5.24.6 at the canonical relation owner layer: `ρ` is maximal cyclically monotone
iff `ρ` is cyclically monotone and has no proper cyclically monotone extension. Here `<` on
`SetRel X Y` is strict graph inclusion. -/
theorem maximalCyclicallyMonotone_iff
    {L : Type w} [LE L] [AddCommMonoid L] [HasPairing X Y L] {ρ : SetRel X Y} :
    MaxCMon[L](ρ) ↔
      CMon[L](ρ) ∧
        ∀ ⦃σ : SetRel X Y⦄, ρ < σ → ¬CMon[L](σ) := by
  simpa using (MaxCMon.iff_forall_gt (L := L) (ρ := ρ))

end

end SetRel

/-! ### Theorem_5_24_6 (from Chap05) -/
noncomputable section

namespace SetRel

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 5.24.6 says that if a subset `Γ ⊆ ℝ × ℝ` is a complete
  non-decreasing curve, then the coordinate-swapped subset
  `Γ* = {(x⋆, x) | (x, x⋆) ∈ Γ}` is again a complete non-decreasing curve.
- `core/canonical`: the chapter owner `SetRel.IsCompleteNondecreasingCurve` is already intrinsic
  on relations `Γ : SetRel ι α`, so this item should live at that owner level rather than being
  fixed to `ℝ × ℝ`.
- `bridge/view`: the coordinate swap is exactly mathlib's canonical relation inverse `Γ.inv`;
  no second transpose owner or set-builder wrapper is needed.

Domain-style sampling used here:
- `SetRel.IsCompleteNondecreasingCurve` from
  `ConvexAnalysis_Rockafellar_1970/Chap05/Definition_5_24_4.lean`;
- `SetRel.inv` from `.lake/packages/mathlib/Mathlib/Data/Rel.lean`, the canonical owner for
  swapping the two coordinates of a relation;
- `IsMaxChain` and `IsMaxChain.image` from
  `Mathlib/Order/Preorder/Chain.lean`, transporting maximal-chain structure along a relation
  isomorphism.

Primitive data vs derived API:
- primitive owner input: a relation `Γ : SetRel ι α`;
- primitive source-facing hypothesis: `Γ.IsCompleteNondecreasingCurve`;
- derived bridge operation: `Γ.inv`, representing the source transpose `Γ*`.

Layer target: `bridge/view`.
-/

section

variable {ι : Type*} [LE ι]
variable {α : Type*} [LE α]

private def prodSwapRelIso : ((· ≤ ·) : (ι × α) → (ι × α) → Prop) ≃r
    ((· ≤ ·) : (α × ι) → (α × ι) → Prop) where
  toEquiv := Equiv.prodComm ι α
  map_rel_iff' := by
    intro a b
    constructor
    · intro h
      exact ⟨h.2, h.1⟩
    · intro h
      exact ⟨h.2, h.1⟩

private theorem image_prodSwapRelIso_eq_inv (Γ : SetRel ι α) :
    prodSwapRelIso (ι := ι) (α := α) '' Γ = Γ.inv := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    change q.swap.swap ∈ Γ
    simpa using hq
  · intro hp
    refine ⟨p.swap, ?_, ?_⟩
    · change p.swap ∈ Γ at hp
      exact hp
    · cases p
      rfl

-- Proof sketch: identify complete non-decreasing curves with maximal chains in the coordinatewise
-- order; the coordinate-swap map on `ι × α` is a relation isomorphism to `α × ι`, so maximal
-- chains are preserved under image. Rewriting that image as `Γ.inv` yields the theorem.
/-- Theorem 5.24.6 at the canonical owner layer: if `Γ` is a complete non-decreasing curve, then
its coordinate-swapped relation `Γ.inv = {(x⋆, x) | (x, x⋆) ∈ Γ}` is also a complete
non-decreasing curve. Specializing `ι = α = ℝ` recovers the source statement. -/
theorem IsCompleteNondecreasingCurve.inv {Γ : SetRel ι α}
    (hΓ : Γ.IsCompleteNondecreasingCurve) :
    Γ.inv.IsCompleteNondecreasingCurve := by
  have hmax : IsMaxChain (· ≤ ·) Γ := hΓ
  have hmaxSwap : IsMaxChain (· ≤ ·) (prodSwapRelIso (ι := ι) (α := α) '' Γ) :=
    hmax.image (prodSwapRelIso (ι := ι) (α := α))
  simpa [image_prodSwapRelIso_eq_inv (ι := ι) (α := α) Γ] using hmaxSwap

end

end SetRel

/-! ### Definition_5_24_7 (from Chap05) -/
open scoped Rockafellar SetRel

universe u v w

section

variable {X : Type u} {Y : Type v}
variable [Sub X] [Sub Y]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Definition 5.24.7 introduces monotonicity for a multivalued mapping.
- `core/canonical`: this chapter already organizes multivalued mappings as relations `SetRel`,
  while pairing-based convex-analytic owners live on `HasPairing`. The monotonicity owner should
  therefore be the relation-plus-pairing layer `SetRel X Y` with values in an ordered codomain
  `L`, not a special wrapper around the continuous dual.
- `bridge/view`: vector-valued Euclidean operators and dual-valued operators both become ordinary
  instances of the same owner via the existing pairing instances from `HasPairing`.

Domain-style sampling used here:
- `SetRel` together with graph-membership notation from mathlib's `Data/Rel`, the canonical owner
  layer for multivalued mappings;
- `HasPairing` from `Items/Chap01/HasPairing.lean`, the project owner layer for convex-analytic
  pairings;
- `SetRel.CyclicallyMonotone` from `Items/Chap05/Definition_5_24_5.lean`, the neighboring owner
  for the stronger cyclic inequality on the same relation-plus-pairing abstraction.

Primitive data vs derived API:
- primitive owner: a relation `ρ : SetRel X Y`;
- primitive source data inside the definition: two graph points of `ρ`;
- derived API: the specification theorem `monotone_iff` and the named owner accessor
  `SetRel.Monotone.pairing_nonneg`.

Ambient-assumption minimization:
- the definition uses only additive differences in the source and target, a pairing value in a
  codomain with `LE` and `Zero` structure, and relation membership;
- no additive, linear, or topological structure on the codomain is primitive for this owner;
- no normed, dual-space, or inner-product structure is primitive data for this owner.

Layer target: `source-facing`. This file owns monotonicity itself, and it belongs at the same
relation-plus-pairing abstraction layer as the surrounding chapter owners.
-/

namespace SetRel

/-- Definition 5.24.7: a multivalued mapping is monotone when every two points of its graph
satisfy the pairing inequality between the primal and dual differences. The canonical owner is the
relation itself, with the pairing codomain `L` explicit because it is not determined by `ρ`
alone. -/
@[mk_iff monotone_iff]
class Monotone (ρ : SetRel X Y) (L : Type w) [LE L] [Zero L] [HasPairing X Y L] : Prop where
  pairing_nonneg {x₀ x₁ : X} {y₀ y₁ : Y}
      (hx₀ : x₀ ~[ρ] y₀) (hx₁ : x₁ ~[ρ] y₁) :
    (0 : L) ≤ ⟪x₁ - x₀, y₁ - y₀⟫ₚ

/-- Source-facing notation for monotonicity with the ambient pairing instance. -/
scoped[SetRel] notation "Mon[" L "](" ρ ")" =>
  SetRel.Monotone ρ L

/-- Explicit-pairing notation for monotonicity, used when two pairing instances on the same
ambient types must be compared in one theorem statement. -/
scoped[SetRel] notation "Mon[" pairing ", " L "](" ρ ")" =>
  (@SetRel.Monotone _ _ _ _ ρ L _ _ pairing)

/-- Graph-membership form of Definition 5.24.7: monotonicity is equivalently a two-point
inequality over arbitrary members of the graph set `ρ ⊆ X × Y`. This keeps theorem surfaces in
the canonical relation-as-set language when that is more convenient. -/
theorem monotone_iff_forall_mem {ρ : SetRel X Y} {L : Type w}
    [LE L] [Zero L] [HasPairing X Y L] :
    Mon[L](ρ) ↔
      ∀ ⦃p q : X × Y⦄, p ∈ ρ → q ∈ ρ →
        (0 : L) ≤ ⟪p.1 - q.1, p.2 - q.2⟫ₚ := by
  constructor
  · intro hρ p q hp hq
    exact hρ.pairing_nonneg hq hp
  · intro hρ
    refine ⟨?_⟩
    intro x₀ x₁ y₀ y₁ hx₀ hx₁
    exact hρ hx₁ hx₀

namespace Monotone

/-!
Owner-level pairing transport API.

`SetRel.Monotone` is pairing-parametric. If two pairing instances on the same ambient types are
pointwise equal, monotonicity transports directly between them.
-/

/-- If two pairing instances on the same `(X, Y, L)` are pointwise equal, monotonicity of `ρ`
transfers from the first pairing to the second. -/
theorem of_pairing_eq {ρ : SetRel X Y} {L : Type w} [LE L] [Zero L]
    {pairing₁ pairing₂ : HasPairing X Y L}
    (hρ : Mon[pairing₁, L](ρ))
    (hpair : ∀ x : X, ∀ y : Y, pairing₁.pairing x y = pairing₂.pairing x y) :
    Mon[pairing₂, L](ρ) := by
  refine ⟨?_⟩
  intro x₀ x₁ y₀ y₁ hx₀ hx₁
  have hineq :
      (0 : L) ≤ pairing₁.pairing (x₁ - x₀) (y₁ - y₀) := by
    exact hρ.pairing_nonneg hx₀ hx₁
  simpa [hpair (x₁ - x₀) (y₁ - y₀)] using hineq

/-- Monotonicity is invariant under replacement of the pairing by a pointwise equal one. -/
theorem iff_pairing_eq {ρ : SetRel X Y} {L : Type w} [LE L] [Zero L]
    {pairing₁ pairing₂ : HasPairing X Y L}
    (hpair : ∀ x : X, ∀ y : Y, pairing₁.pairing x y = pairing₂.pairing x y) :
    Mon[pairing₁, L](ρ) ↔
      Mon[pairing₂, L](ρ) := by
  constructor
  · intro hρ
    exact of_pairing_eq (pairing₁ := pairing₁) (pairing₂ := pairing₂) hρ hpair
  · intro hρ
    exact of_pairing_eq (pairing₁ := pairing₂) (pairing₂ := pairing₁) hρ
      (fun x y ↦ (hpair x y).symm)

end Monotone

end SetRel

end

/-! ### Theorem_5_24_7 (from Chap05) -/
noncomputable section

universe u v

open Filter
open scoped Topology Rockafellar

section

variable {𝕜 : Type v} [Semiring 𝕜] [TopologicalSpace 𝕜] [LE 𝕜]
variable {E : Type u} [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]

namespace Function

/-- Sequential closedness consequence for the pairing-parametric graph owner: if the graph of
the subdifferential is closed, then limits of convergent graph sequences remain in the graph. -/
theorem mem_subdifferentialAt_of_tendsto_of_isClosed_subdifferentialGraph
    {Y : Type (max u v)} [TopologicalSpace Y] [HasPairing E Y 𝕜]
    {f : E → WithBotTop 𝕜} (hclosed : IsClosed (gph∂[Y](f)))
    {xSeq : ℕ → E} {x : E}
    {xStarSeq : ℕ → Y} {xStar : Y}
    (hx : Tendsto xSeq atTop (𝓝 x))
    (hxStar : Tendsto xStarSeq atTop (𝓝 xStar))
    (hsub : ∀ n, xStarSeq n ∈ (∂[Y]f(xSeq n))) :
    xStar ∈ (∂[Y]f(x)) := by
  have hgraph : Tendsto (fun n ↦ (xSeq n, xStarSeq n)) atTop (𝓝 (x, xStar)) := by
    simpa [nhds_prod_eq] using hx.prodMk hxStar
  have hmem : ∀ n, (xSeq n, xStarSeq n) ∈ gph∂[Y](f) := by
    intro n
    simpa using hsub n
  have hlimit : (x, xStar) ∈ gph∂[Y](f) := by
    exact hclosed.mem_of_tendsto hgraph (Filter.Eventually.of_forall hmem)
  simpa using hlimit

end Function

end

section

variable {𝕜 : Type v} [Semiring 𝕜] [TopologicalSpace 𝕜] [PartialOrder 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)]
variable {E : Type u} [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]

local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)

namespace Function

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 5.24.7 says that if `xᵢ → x` and `xᵢ⋆ → x⋆` with
  `xᵢ⋆ ∈ ∂f(xᵢ)` for all `i`, then `x⋆ ∈ ∂f(x)`. The source then immediately restates this as the
  closedness of the graph of `∂f`.
- `core/canonical`: the owner abstractions already present in the project are the dual-valued
  graph owner `_root_.subdifferentialGraph` from Definition 5.24.3, the dual-valued
  `_root_.subdifferentialAt` from Definition 23.0.6, the closed-proper-convex owner
  `Function.IsClosedProperConvex`, and the topological owner `IsClosed`.
- `bridge/view`: once graph closedness is available, the pairing-parametric sequential
  closedness consequence is packaged as
  `mem_subdifferentialAt_of_tendsto_of_isClosed_subdifferentialGraph`.

Domain-style sampling used here:
- `_root_.subdifferentialGraph` from
  [Definition_5_24_3](Items/Chap05/Definition_5_24_3.lean);
- `_root_.subdifferentialAt` from
  [Definition_23_0_6](Items/Chap05/Definition_23_0_6.lean);
- `Function.IsClosedProperConvex` from
  [Text_12_3_6](Items/Chap03/Text_12_3_6.lean);
- mathlib's canonical closed-set owner `IsClosed`, together with
  `IsClosed.mem_of_tendsto` and `IsClosed.isSeqClosed`.

Primitive data vs derived API:
- primitive data: the closed proper convex function `f` and its canonical dual-valued owner graph
  `subdifferentialGraph f`;
- primitive topological compatibility data: continuity of
  `(x, x⋆) ↦ ⟪z - x, x⋆⟫ₚ` for each fixed `z`;
- derived API: the pairing-parametric sequence-limit corollary obtained from closedness of the
  canonical graph owner.

Layer target: `core/canonical` for the main labeled entry
`Function.IsClosedProperConvex.isClosed_subdifferentialGraph`, because the source itself
identifies the theorem with graph closedness; the sequential statement is kept only as a
consequence on that owner.

Codomain-layer normalization:
- this file's pairing-parametric theorem surfaces are kept at the chapter owner codomain
  `WithBotTop 𝕜` (not a concrete `EReal` alias), while the strong-dual bridge below is the
  `𝕜 = ℝ` specialization.

Ambient-assumption minimization:
- no finite-dimensionality hypothesis is needed at the canonical dual-valued closed-graph layer;
- no inner-product or completeness assumption is exposed on the pairing-parametric theorem;
- the strong-dual specialization is a thin bridge theorem.
-/

-- Proof sketch: write the graph as an intersection over `z` of closed sets
-- `{(x, x⋆) | f x + ⟪z - x, x⋆⟫ ≤ f z}`. Each set is closed because
-- `x ↦ f x` is lower semicontinuous (from `hf`) and
-- `(x, x⋆) ↦ (⟪z - x, x⋆⟫ : WithBotTop 𝕜)` is continuous.
/-- Theorem 5.24.7 at the pairing-parametric owner layer: if `f` is closed proper convex and the
pairing evaluation map `(x, x⋆) ↦ ⟪z - x, x⋆⟫ₚ` is continuous for each `z`, then the canonical
subdifferential graph is closed. -/
theorem IsClosedProperConvex.isClosed_subdifferentialGraph
    {Y : Type (max u v)} [TopologicalSpace Y] [HasPairing E Y 𝕜]
    {f : E → WithBotTop 𝕜} (hf : IsClosedProperConvex[𝕜] f)
    (hpair_cont : ∀ z : E,
      Continuous (fun p : E × Y ↦ ((⟪z - p.1, p.2⟫ₚ : 𝕜) : WithBotTop 𝕜)))
    :
    IsClosed (gph∂[Y](f)) := by
  have hgraph_eq :
      gph∂[Y](f) =
        ⋂ z : E,
          {p : E × Y |
            f p.1 + ((⟪z - p.1, p.2⟫ₚ : 𝕜) : WithBotTop 𝕜) ≤ f z} := by
    ext p
    constructor
    · intro hp
      refine Set.mem_iInter.mpr ?_
      intro z
      have hp' : p.2 ∈ subdifferentialAt f p.1 Y := hp
      exact (_root_.mem_subdifferentialAt_pairing.mp hp') z
    · intro hp
      change p.2 ∈ subdifferentialAt f p.1 Y
      rw [_root_.mem_subdifferentialAt_pairing]
      intro z
      have hz :
          f p.1 + ((⟪z - p.1, p.2⟫ₚ : 𝕜) : WithBotTop 𝕜) ≤ f z :=
        (Set.mem_iInter.mp hp) z
      simpa [ge_iff_le] using hz
  rw [hgraph_eq]
  refine isClosed_iInter ?_
  intro z
  have hcont_pairing :
      Continuous (fun p : E × Y ↦
        ((⟪z - p.1, p.2⟫ₚ : 𝕜) : WithBotTop 𝕜)) := hpair_cont z
  have hlsc_fst :
      LowerSemicontinuous (fun p : E × Y ↦ f p.1) :=
    hf.closed.comp continuous_fst
  have hlsc_pairing :
      LowerSemicontinuous (fun p : E × Y ↦
        ((⟪z - p.1, p.2⟫ₚ : 𝕜) : WithBotTop 𝕜)) :=
    hcont_pairing.lowerSemicontinuous
  have hlsc_sum :
      LowerSemicontinuous (fun p : E × Y ↦
        f p.1 + ((⟪z - p.1, p.2⟫ₚ : 𝕜) : WithBotTop 𝕜)) := by
    refine hlsc_fst.add' hlsc_pairing ?_
    intro p
    have h1 :
        f p.1 ≠ (⊤ : WithBotTop 𝕜) ∨
          ((⟪z - p.1, p.2⟫ₚ : 𝕜) : WithBotTop 𝕜) ≠ ⊥ := by
      exact Or.inr (WithBotTop.coe_ne_bot (⟪z - p.1, p.2⟫ₚ : 𝕜))
    have h2 :
        f p.1 ≠ (⊥ : WithBotTop 𝕜) ∨
          ((⟪z - p.1, p.2⟫ₚ : 𝕜) : WithBotTop 𝕜) ≠ ⊤ := by
      exact Or.inr (WithBotTop.coe_ne_top (⟪z - p.1, p.2⟫ₚ : 𝕜))
    exact WithBotTop.continuousAt_add
      (p := (f p.1, ((⟪z - p.1, p.2⟫ₚ : 𝕜) : WithBotTop 𝕜))) h1 h2
  simpa [Set.preimage] using hlsc_sum.isClosed_preimage (f z)

-- Proof sketch: this is the canonical dual-valued sequential consequence of graph closedness,
-- instantiated by the pairing-parametric closed-graph theorem above.
/-- Pairing-parametric sequential form of Theorem 5.24.7: under the same hypotheses as
`Function.IsClosedProperConvex.isClosed_subdifferentialGraph`, limits of convergent subgradient
sequences remain subgradients. -/
theorem IsClosedProperConvex.mem_subdifferentialAt_of_tendsto_pairing
    {Y : Type (max u v)} [TopologicalSpace Y] [HasPairing E Y 𝕜]
    {f : E → WithBotTop 𝕜} (hf : IsClosedProperConvex[𝕜] f)
    (hpair_cont : ∀ z : E,
      Continuous (fun p : E × Y ↦ ((⟪z - p.1, p.2⟫ₚ : 𝕜) : WithBotTop 𝕜)))
    {xSeq : ℕ → E} {x : E}
    {xStarSeq : ℕ → Y} {xStar : Y}
    (hx : Tendsto xSeq atTop (𝓝 x))
    (hxStar : Tendsto xStarSeq atTop (𝓝 xStar))
    (hsub : ∀ n, xStarSeq n ∈ (∂[Y]f(xSeq n))) :
    xStar ∈ (∂[Y]f(x)) := by
  exact Function.mem_subdifferentialAt_of_tendsto_of_isClosed_subdifferentialGraph
    (hf.isClosed_subdifferentialGraph hpair_cont) hx hxStar hsub

end Function

end

section

variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

local notation "IsClosedProperConvex[ℝ]" => Function.IsClosedProperConvex (𝕜 := ℝ)

namespace Function

/-- Strong-dual specialization of
`Function.IsClosedProperConvex.isClosed_subdifferentialGraph`; this is the chapter's canonical
concrete dual model bridge. -/
theorem IsClosedProperConvex.isClosed_subdifferentialGraph_strongDual
    {f : E → WithBotTop ℝ} (hf : IsClosedProperConvex[ℝ] f) :
    IsClosed (gph∂(f)) := by
  refine hf.isClosed_subdifferentialGraph (Y := StrongDual ℝ E) ?_
  intro z
  have hcont_real : Continuous (fun p : E × StrongDual ℝ E ↦ (p.2) (z - p.1)) :=
    continuous_snd.clm_apply (continuous_const.sub continuous_fst)
  simpa using WithBotTop.continuous_coe.comp hcont_real

/-- Theorem 5.24.7, strong-dual sequential bridge: in a real seminormed space, limits of
convergent dual subgradient sequences of a closed proper convex function remain subgradients. -/
theorem IsClosedProperConvex.mem_subdifferentialAt_of_tendsto
    {f : E → WithBotTop ℝ} (hf : IsClosedProperConvex[ℝ] f)
    {xSeq : ℕ → E} {x : E}
    {xStarSeq : ℕ → StrongDual ℝ E} {xStar : StrongDual ℝ E}
    (hx : Tendsto xSeq atTop (𝓝 x))
    (hxStar : Tendsto xStarSeq atTop (𝓝 xStar))
    (hsub : ∀ n, xStarSeq n ∈ (∂ f at xSeq n)) :
    xStar ∈ (∂ f at x) := by
  exact hf.mem_subdifferentialAt_of_tendsto_pairing (Y := StrongDual ℝ E)
    (hpair_cont := by
      intro z
      have hcont_real : Continuous (fun p : E × StrongDual ℝ E ↦ (p.2) (z - p.1)) :=
        continuous_snd.clm_apply (continuous_const.sub continuous_fst)
      simpa using WithBotTop.continuous_coe.comp hcont_real)
    hx hxStar hsub

end Function

end
