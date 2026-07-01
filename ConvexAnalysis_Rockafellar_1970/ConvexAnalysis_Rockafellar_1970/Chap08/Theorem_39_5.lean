import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.HasPairing
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_3_6
import ConvexAnalysis_Rockafellar_1970.Chap08.Definition_39_0_1
import ConvexAnalysis_Rockafellar_1970.Chap08.Definition_39_0_14
import ConvexAnalysis_Rockafellar_1970.Chap08.Definition_39_0_5

noncomputable section

open scoped Rockafellar SetRel

universe u v w z

namespace SetRel

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 39.5 is the process-level sum rule for adjoints, together with the
  closedness and closure clauses under the dual relative-interior qualification.
- `core/canonical`: Chapter 39 already owns convex processes on `SetRel U X` via
  `A.IsConvexProcess 𝕜`, graph closure via `closure` and `IsClosed`, and the process adjoint via
  the notation surface `A∗[𝕜]` (with dual carrier types inferred from context).
- `bridge/view`: the theorem is a direct process-side specialization of the Chapter 38 sum rule,
  so no new wrapper around relations, graphs, or adjoints is introduced here.

Primary mathematical domain:
- convex processes on finite-dimensional pairing spaces.

Domain-style sampling used here:
- `SetRel.IsConvexProcess` from `Chap08.Definition_39_0_1`;
- `SetRel.closure` and `SetRel.IsClosed` from `Chap08.Definition_39_0_5`;
- the Chapter 39 process-adjoint notation `A∗[𝕜]` from `Chap08.Definition_39_0_14`;
- `Set.fiberwiseSum` and notation `+ᶠ` from `Chap01.Theorem_3_6`.

Primitive data vs derived API:
- primitive source data: convex processes `A₁`, `A₂ : SetRel U X`;
- primitive reused owners: `A.dom`, `A∗[𝕜]`, `cl(A)`, `IsClosed A`, and
  `(A₁ +ᶠ A₂ : SetRel U X)`;
- derived API: the adjoint-of-sum identity, closedness of the sum under the dual qualification,
  and the closure formula for the adjoint of the sum.

Layer target: `source-facing`, stated directly on the canonical Chapter 39 owners.
-/

section

variable {𝕜 : Type*}
variable [Field 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {U : Type u}
variable [AddCommGroup U] [Module 𝕜 U] [TopologicalSpace U] [_root_.FiniteDimensional 𝕜 U]
variable {X : Type v}
variable [AddCommGroup X] [Module 𝕜 X] [TopologicalSpace X] [_root_.FiniteDimensional 𝕜 X]
variable {UStar : Type w}
variable [AddCommGroup UStar] [Module 𝕜 UStar] [TopologicalSpace UStar]
  [_root_.FiniteDimensional 𝕜 UStar]
variable {XStar : Type z}
variable [AddCommGroup XStar] [Module 𝕜 XStar] [TopologicalSpace XStar]
  [_root_.FiniteDimensional 𝕜 XStar]
variable [HasLinearPairing U UStar 𝕜]
variable [HasLinearPairing X XStar 𝕜]

local notation "ri(" C ")" => intrinsicInterior 𝕜 C
local notation:100 A "∗ᵣ" => (A∗[XStar, UStar; 𝕜])

-- Proof sketch: specialize the Chapter 38 sum rule to the indicator bifunctions of `A₁` and
-- `A₂`, then identify the resulting bifunction adjoints with the process adjoints `A₁∗ᵣ` and
-- `A₂∗ᵣ`.
/-- Theorem 39.5 (1): if convex processes `A₁` and `A₂` have a common point in
`intrinsicInterior 𝕜 (dom A₁) ∩ intrinsicInterior 𝕜 (dom A₂)`, then the adjoint of their
fiberwise sum is the fiberwise sum of
their adjoints. This is the Chapter 39 process form of the Chapter 38 adjoint sum rule. -/
theorem adjoint_fiberwiseSum_eq_fiberwiseSum_adjoint_of_common_ri_dom
    {A₁ A₂ : SetRel U X} (hA₁ : A₁.IsConvexProcess 𝕜) (hA₂ : A₂.IsConvexProcess 𝕜)
    (hri : (ri(A₁.dom) ∩ ri(A₂.dom)).Nonempty) :
    (A₁ +ᶠ A₂)∗ᵣ = A₁∗ᵣ +ᶠ A₂∗ᵣ := sorry

-- Proof sketch: apply the Chapter 38 closed-sum theorem to the same indicator bifunctions, using
-- the dual qualification on `ri ((A₁∗ᵣ).dom) ∩ ri ((A₂∗ᵣ).dom)`, then translate bifunction
-- closedness back
-- to graph closedness of the process sum.
/-- Theorem 39.5 (2): if `A₁` and `A₂` are closed convex processes and
`ri (dom A₁*) ∩ ri (dom A₂*)` is nonempty, then their fiberwise sum is closed. -/
theorem isClosed_fiberwiseSum_of_isClosed_of_common_ri_dom_adjoint
    {A₁ A₂ : SetRel U X} (hA₁ : A₁.IsConvexProcess 𝕜) (hA₂ : A₂.IsConvexProcess 𝕜)
    (hA₁_closed : A₁.IsClosed) (hA₂_closed : A₂.IsClosed)
    (hri :
      (ri((A₁∗ᵣ).dom) ∩ ri((A₂∗ᵣ).dom)).Nonempty) :
    IsClosed (A₁ +ᶠ A₂) := sorry

-- Proof sketch: the same Chapter 38 specialization gives the adjoint-side formula
-- `(A₁ + A₂)^* = cl (A₁^* + A₂^*)` once the process-side adjoint and closure owners are
-- substituted for the corresponding indicator-bifunction owners.
/-- Theorem 39.5 (3): if `A₁` and `A₂` are closed convex processes and
`ri (dom A₁*) ∩ ri (dom A₂*)` is nonempty, then the adjoint of their fiberwise sum is the graph
closure of the fiberwise sum of their adjoints. -/
theorem adjoint_fiberwiseSum_eq_closure_fiberwiseSum_adjoint_of_isClosed_of_common_ri_dom_adjoint
    {A₁ A₂ : SetRel U X} (hA₁ : A₁.IsConvexProcess 𝕜) (hA₂ : A₂.IsConvexProcess 𝕜)
    (hA₁_closed : A₁.IsClosed) (hA₂_closed : A₂.IsClosed)
    (hri :
      (ri((A₁∗ᵣ).dom) ∩ ri((A₂∗ᵣ).dom)).Nonempty) :
    (A₁ +ᶠ A₂)∗ᵣ = cl(A₁∗ᵣ +ᶠ A₂∗ᵣ) := sorry

end

end SetRel
