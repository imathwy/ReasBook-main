import ConvexAnalysis_Rockafellar_1970.Chap01.HasPairing
import Mathlib

noncomputable section

universe u v w z ℓ

open scoped Rockafellar SetRel

namespace SetRel

/-!
Source/core/bridge triage:

- `source-facing`: Definition 39.0.14 introduces the adjoint `A*` of an oriented convex process by
  the fiberwise pairing inequality `⟪u, u⋆⟫ ≥ ⟪x, x⋆⟫` for every graph point `(u, x)` of `A`.
- `core/canonical`: the chapter already owns convex processes on the relation owner
  `A : SetRel U X`, and the present item uses the canonical pairing owner
  `HasPairing U UStar L` and `HasPairing X XStar L` from `Chap01.HasPairing`.
- `bridge/view`: the parenthetical infimum-oriented clause is not a second owner here; it is the
  same relation-level owner read in the order-dual codomain `Lᵒᵈ`, where the displayed inequality
  is automatically reversed.

Primary mathematical domain:
- convex processes and pairing-based adjoint relations.

Domain-style sampling used here:
- `SetRel` from `Mathlib.Data.Rel` as the canonical graph owner;
- the canonical pairing owner `HasPairing` and its order-dual lift;
- `SetRel.IsConvexProcess` from `Chap08.Definition_39_0_1`, which shows that Chapter 39 already
  treats convex processes directly as relations rather than through a wrapper structure.

Primitive data vs derived API:
- primitive source data: a relation `A : SetRel U X`;
- primitive owner introduced here:
  `SetRel.adjoint (XStar := XStar) (UStar := UStar) (L := L) A : SetRel XStar UStar`;
- derived API: the pointwise membership criterion `mem_adjoint_iff`.

Owner and notation decision:
- the raw owner is `SetRel.adjoint`, not a new packaged “adjoint process” structure;
- the source-facing operator notation is the lightweight `Rockafellar`-scoped notation
  `A∗[XStar, UStar; L]` (explicit dual carriers) together with the low-noise notation `A∗[L]`
  when the surrounding context already fixes the dual carriers; both expand directly to the same
  canonical raw owner
  `SetRel.adjoint (XStar := XStar) (UStar := UStar) (L := L) A`
  (no wrapper owner and no macro parser layer);
- the dual carrier types `XStar`, `UStar` and the pairing codomain `L` are core owner
  parameters and are therefore explicit on the owner surface (typically via named arguments),
  since they are not recoverable from `A : SetRel U X` alone.

Layer target: `source-facing`, stated directly on the canonical relation owner with explicit dual
space parameters, since those parameters are not recoverable from `A : SetRel U X` alone.
-/

section Adjoint

variable {U : Type u} {X : Type v} {XStar : Type w} {UStar : Type z} {L : Type ℓ}
variable [LE L]
variable [HasPairing U UStar L] [HasPairing X XStar L]

/-- Definition 39.0.14: for a supremum-oriented convex process `A`, its adjoint `A*` is the
relation on dual points `(x⋆, u⋆)` cut out by the inequalities `⟪u, u⋆⟫ ≥ ⟪x, x⋆⟫` for every
graph point `(u, x)` of `A`. The parenthetical infimum-oriented clause is recovered by reading
the same owner in the order-dual codomain `Lᵒᵈ`, which reverses the inequality. -/
def adjoint (A : SetRel U X) : SetRel XStar UStar :=
  { p : XStar × UStar | ∀ ⦃u : U⦄ ⦃x : X⦄, u ~[A] x → (⟪u, p.2⟫ₚ : L) ≥ ⟪x, p.1⟫ₚ }

/-- Canonical theorem-surface notation for Definition 39.0.14:
`A∗[L]` denotes the process adjoint relation in pairing codomain `L`.
When typeclass inference needs help fixing dual carriers, use the explicit disambiguation form
`A∗[XStar, UStar; L]`. -/
scoped[Rockafellar] notation:100 A "∗[" K "]" =>
  SetRel.adjoint (L := K) A
scoped[Rockafellar] notation:100 A "∗[" Xs ", " Us "; " K "]" =>
  SetRel.adjoint (XStar := Xs) (UStar := Us) (L := K) A

/-- Evaluating the adjoint relation at `(x⋆, u⋆)` is exactly the defining universal pairing
inequality against every graph point of `A`. -/
@[simp] theorem mem_adjoint_iff (A : SetRel U X) {xStar : XStar} {uStar : UStar} :
    xStar ~[A∗[L]] uStar ↔
      ∀ ⦃u : U⦄ ⦃x : X⦄, u ~[A] x → (⟪u, uStar⟫ₚ : L) ≥ ⟪x, xStar⟫ₚ := Iff.rfl

/-- Reading `SetRel.adjoint` in the order-dual codomain `Lᵒᵈ` gives the infimum-oriented branch
of Definition 39.0.14, where the defining inequality is reversed. -/
-- Proof sketch: apply `mem_adjoint_iff` in the order-dual codomain; the order dual turns `≥`
-- in `Lᵒᵈ` into `≤` in `L`.
@[simp] theorem mem_adjoint_orderDual_iff (A : SetRel U X) {xStar : XStar} {uStar : UStar} :
    xStar ~[A∗[Lᵒᵈ]] uStar ↔
      ∀ ⦃u : U⦄ ⦃x : X⦄, u ~[A] x → (⟪u, uStar⟫ₚ : L) ≤ ⟪x, xStar⟫ₚ := Iff.rfl

end Adjoint

end SetRel
