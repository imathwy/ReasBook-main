import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.HasPairing

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
