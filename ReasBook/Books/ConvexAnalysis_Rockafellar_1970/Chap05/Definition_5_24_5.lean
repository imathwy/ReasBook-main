import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.HasPairing

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
