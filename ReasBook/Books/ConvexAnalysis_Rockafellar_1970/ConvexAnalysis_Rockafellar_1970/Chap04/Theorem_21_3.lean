import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Definition_8_0_1
import ConvexAnalysis_Rockafellar_1970.Chap02.Corollary_8_5_1
import ConvexAnalysis_Rockafellar_1970.Chap02.Definiton_8_5_0
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_6
import ConvexAnalysis_Rockafellar_1970.Chap04.Text_21_0_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Rockafellar
open Set

noncomputable section

universe u v

section

variable {E : Type u}
variable {I : Type v}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 21.3 is Rockafellar's infinite-family alternative for closed proper
  convex inequalities on a closed convex set `C`: either there is a point of `C` where
  every constraint is nonpositive, or there is a finitely supported nonnegative multiplier
  certificate uniformly separating `C` from the feasible region.
- `core/canonical`: the existing project owners already matching the mathematics are
  `Function.IsClosedProperConvex`, `weakConvexInequalitySolutionSet`,
  `Set.RecedesInDirection`, `Function.recessionCone`, the no-common-recession owner
  `Set.NoCommonRecessionDirectionOn`, the finitely-supported multiplier owner predicate
  `Finsupp.IsNonnegativeMultiplierCertificateOn`, and the logical exclusive-or `Xor'`.
- `bridge/view`: the textbook phrase "no common direction of recession" is carried by the owner
  `C.NoCommonRecessionDirectionOn f`, whose definitional expansion is exactly the existence-negated
  conjunction of a source-facing recession direction of `C` and membership in every
  function recession cone `Function.recessionCone ((f i)₀⁺)`. The finitely many nonzero
  multipliers are expressed by a single `Finsupp`, and the weak feasible region is the Chapter 21
  owner `weakConvexInequalitySolutionSet f`.

Domain-style sampling used here:
- `Function.IsClosedProperConvex` from `Text_12_3_6`;
- `weakConvexInequalitySolutionSet` and `mem_weakConvexInequalitySolutionSet` from `Text_21_0_1`;
- `Set.RecedesInDirection` from `Definition_8_0_1`;
- `Function.recessionCone` from `Definiton_8_5_0`;
- `Xor'` and `Finsupp` from the canonical logical and finitely supported APIs.

Primitive data vs derived API:
- primitive inputs: an arbitrary index family `f : I → E → WithTopBot ℝ` with
  `∀ i, (f i).IsClosedProperConvex` and a closed convex set `C`;
- primitive hypothesis layer: the no-common-recession condition is the owner
  `C.NoCommonRecessionDirectionOn f`;
- owner feasible-set data: `C ∩ weakConvexInequalitySolutionSet f`;
- derived API: the pointwise restatement `∃ x ∈ C, ∀ i, f i x ≤ 0` of owner feasible-set
  nonemptiness, the exclusive alternative between that owner feasible set and a finitely
  supported nonnegative multiplier certificate, recorded as a predicate on the actual
  `Finsupp` of weights, and the Caratheodory-type support bound
  `Module.finrank ℝ E + 1` for the certificate under the full Theorem 21.3 hypotheses when the
  multiplier alternative occurs.

Layer target: `source-facing`, with the feasible-point side routed through the Chapter 21 weak
inequality owner and the textbook pointwise phrasing retained only as a thin companion bridge.
-/

namespace Finsupp

/-- A nonnegative multiplier family with a positive uniform lower bound for its weighted sum on
`C`. The finite-support data is carried canonically by `weights : I →₀ 𝕜`. -/
def IsNonnegativeMultiplierCertificateOn
    {𝕜 : Type*} [Semiring 𝕜] [LinearOrder 𝕜]
    (weights : I →₀ 𝕜) (C : Set E) (f : I → E → WithTopBot 𝕜) (epsilon : 𝕜) : Prop :=
  (∀ i : I, 0 ≤ weights i) ∧
    0 < epsilon ∧
    ∀ x : E, x ∈ C →
      (epsilon : WithTopBot 𝕜) ≤
        weights.sum (fun i a ↦ (a : WithTopBot 𝕜) * f i x)

end Finsupp

-- Proof sketch: add the indicator of `C` to the family to reduce to the unconstrained case
-- `C = R^n`. If the pointwise nonpositive alternative fails, form the convex hull of the
-- conjugates `fᵢ*`, pass to its positively homogeneous envelope, and use the empty-feasible-set
-- hypothesis to force the value at `0` to be negative after closure. The recession-direction
-- hypothesis rules out the boundary case in which that value could drop only after closure, so one
-- obtains a genuine negative value at `0`; Caratheodory then yields finitely many nonnegative
-- multipliers producing a uniform lower bound `ε > 0` on `C`. Mutual exclusivity is immediate by
-- evaluating a certificate at a feasible point.
/-- The owner weak-feasible set for the family `f` on `C` is exactly the textbook set of points
`x ∈ C` with `f i x ≤ 0` for every constraint `i`. -/
theorem nonpositive_convexInequalitySolutionSet_nonempty_iff
    {ι : Sort v} {β : Type*} [LE β] [Zero β]
    {C : Set E} (f : ι → E → β) :
    (C ∩ weakConvexInequalitySolutionSet f).Nonempty ↔
      ∃ x : E, x ∈ C ∧ ∀ i : ι, f i x ≤ 0 := by
  constructor
  · rintro ⟨x, hxC, hxfeasible⟩
    exact ⟨x, hxC, mem_weakConvexInequalitySolutionSet.mp hxfeasible⟩
  · rintro ⟨x, hxC, hxfeasible⟩
    exact ⟨x, hxC, mem_weakConvexInequalitySolutionSet.mpr hxfeasible⟩

section

variable {𝕜 α : Type*}
variable [Zero 𝕜] [LE 𝕜]
variable [Add E] [Zero E] [SMul 𝕜 E]
variable [AddCommGroup α] [ConditionallyCompleteLattice α]

namespace Set

/-- Owner hypothesis for Chapter 21 alternatives: there is no nonzero recession direction of `C`
that belongs to every recession cone `Function.recessionCone ((f i)₀⁺)`.

This owner keeps the ambient scalar (`𝕜`) and function codomain base (`α`) independent: recession
directions of `C` live in the scalar geometry, while recession cones of `(f i)₀⁺` live in the
`WithTopBot α` codomain layer. -/
def NoCommonRecessionDirectionOn {ι : Sort v}
    (C : Set E) (f : ι → E → WithTopBot α) : Prop :=
  ¬ ∃ y : E, C.RecedesInDirection 𝕜 y ∧
    ∀ i : ι, y ∈ Function.recessionCone ((f i)₀⁺)

@[simp] theorem noCommonRecessionDirectionOn_iff {ι : Sort v}
    (C : Set E) (f : ι → E → WithTopBot α) :
    C.NoCommonRecessionDirectionOn f ↔
      ¬ ∃ y : E, C.RecedesInDirection 𝕜 y ∧
        ∀ i : ι, y ∈ Function.recessionCone ((f i)₀⁺) :=
  Iff.rfl

end Set

end

section

variable [TopologicalSpace E] [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
variable {C : Set E} {f : I → E → WithTopBot ℝ}
local notation "IsClosedProperConvex[ℝ]" => Function.IsClosedProperConvex (𝕜 := ℝ)

/-- Theorem 21.3: let `fᵢ`, `i ∈ I`, be closed proper convex functions on `R^n`, and let `C` be a
closed convex set. If there is no nonzero recession direction of `C` along which every
`fᵢ` has nonpositive recession value, then exactly one of the following holds: either the weak
feasible set `C ∩ weakConvexInequalitySolutionSet f` is nonempty, or there is
a finitely supported nonnegative multiplier family `λ` and some `ε > 0` such that
`ε ≤ ∑ i, λᵢ fᵢ x` for every `x ∈ C`. The source ambient `R^n` is represented here by the
chapter's canonical finite-dimensional real topological vector-space layer. -/
theorem
    xor_nonpositive_convexInequalitySolutionSet_nonempty_or_finitely_supported_nonnegative_multiplier_certificate
    (f : I → E → WithTopBot ℝ)
    (hf : ∀ i : I, IsClosedProperConvex[ℝ] (f i))
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (hno_common : C.NoCommonRecessionDirectionOn f)
    :
    Xor'
      (C ∩ weakConvexInequalitySolutionSet f).Nonempty
      (∃ weights : I →₀ ℝ, ∃ epsilon : ℝ,
        weights.IsNonnegativeMultiplierCertificateOn C f epsilon) := sorry

/-- Source-facing pointwise restatement of Theorem 21.3: the owner weak-feasible-set alternative
is equivalent to existence of `x ∈ C` with `f i x ≤ 0` for every `i`. -/
theorem xor_exists_nonpositive_point_or_finitely_supported_nonnegative_multiplier_certificate
    (f : I → E → WithTopBot ℝ)
    (hf : ∀ i : I, IsClosedProperConvex[ℝ] (f i))
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (hno_common : C.NoCommonRecessionDirectionOn f)
    :
    Xor'
      (∃ x : E, x ∈ C ∧ ∀ i : I, f i x ≤ 0)
      (∃ weights : I →₀ ℝ, ∃ epsilon : ℝ,
        weights.IsNonnegativeMultiplierCertificateOn C f epsilon) := by
  have hiff :
      (C ∩ weakConvexInequalitySolutionSet f).Nonempty ↔
        (∃ x : E, x ∈ C ∧ ∀ i : I, f i x ≤ 0) :=
    nonpositive_convexInequalitySolutionSet_nonempty_iff (C := C) f
  rcases
      xor_nonpositive_convexInequalitySolutionSet_nonempty_or_finitely_supported_nonnegative_multiplier_certificate
        f hf hC_closed hC_convex hno_common with
    hxor | hxor
  · exact Or.inl ⟨hiff.mp hxor.1, hxor.2⟩
  · exact Or.inr ⟨hxor.1, fun hpoint ↦ hxor.2 (hiff.mpr hpoint)⟩

-- Proof sketch: under the full hypotheses of Theorem 21.3, if the multiplier alternative holds,
-- rerun the same convex-hull/separation construction behind that alternative and apply
-- Caratheodory's theorem in ambient dimension `Module.finrank ℝ E`. This directly produces a
-- multiplier certificate with support cardinality at most `Module.finrank ℝ E + 1`; it is not a
-- free-standing reduction theorem for an arbitrary pre-existing certificate on an arbitrary family.
/-- Under the hypotheses of Theorem 21.3, whenever the multiplier alternative occurs, it can be
chosen with at most `Module.finrank ℝ E + 1` nonzero multipliers. -/
theorem exists_finitely_supported_nonnegative_multiplier_certificate_with_support_card_le
    (f : I → E → WithTopBot ℝ)
    (hf : ∀ i : I, IsClosedProperConvex[ℝ] (f i))
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (hno_common : C.NoCommonRecessionDirectionOn f)
    (hcert : ∃ weights : I →₀ ℝ, ∃ epsilon : ℝ,
      weights.IsNonnegativeMultiplierCertificateOn C f epsilon) :
    ∃ weights : I →₀ ℝ, ∃ epsilon : ℝ,
      weights.support.card ≤ Module.finrank ℝ E + 1 ∧
        weights.IsNonnegativeMultiplierCertificateOn C f epsilon := sorry

end

end
