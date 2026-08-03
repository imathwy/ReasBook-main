import Mathlib
import BauschkeLean.Chap01.Text_1_0_8

open scoped InnerProductSpace

universe u

namespace ERealFunction

section Pairing

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The canonical `EReal`-valued pairing on the Hilbert product `H × H`. -/
def pairing : H × H → EReal :=
  fun p ↦ ((⟪p.1, p.2⟫_ℝ : ℝ) : EReal)

/-- Evaluating `pairing` at `(x, u)` recovers the coerced inner product `⟪x, u⟫`. -/
@[simp] theorem pairing_apply (x u : H) :
    pairing (x, u) = ((⟪x, u⟫_ℝ : ℝ) : EReal) :=
  rfl

end Pairing

end ERealFunction

namespace SetValuedOperator

section BivariateFenchelEquality

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/- Source/core/bridge triage:
- `source-facing`: the pairing-contact operator attached to a bivariate function `F`.
- `core/canonical`: the set-valued operator `pairingEqualityOperator F`.
- `bridge/view`: pointwise and graph membership are the atomic derived characterizations.

Primitive data: the bivariate function `F`.
Derived API: pointwise membership, graph-membership simplification lemmas, and the graph-equality
description of the contact set. -/

/-- The set-valued operator whose graph is the pairing-contact set
`{(x, u) | F (x, u) = ⟪x, u⟫}`. -/
def pairingEqualityOperator {α : Type*} [CoeTC α EReal] (F : H × H → α) :
    SetValuedOperator H H :=
  fun x ↦ {u | (F (x, u) : EReal) = ERealFunction.pairing (x, u)}

/-- Membership in `pairingEqualityOperator F x` is exactly the defining pairing equality
`F (x, u) = ⟪x, u⟫`. -/
@[simp] theorem mem_pairingEqualityOperator_iff
    {α : Type*} [CoeTC α EReal] (F : H × H → α) (x u : H) :
    u ∈ pairingEqualityOperator F x ↔
      (F (x, u) : EReal) = ERealFunction.pairing (x, u) :=
  Iff.rfl

/-- A pair `(x, u)` lies in the graph of `pairingEqualityOperator F` exactly when it satisfies the
pairing equality `F (x, u) = ⟪x, u⟫`. -/
@[simp] theorem mem_graph_pairingEqualityOperator_iff
    {α : Type*} [CoeTC α EReal] (F : H × H → α) (x u : H) :
    (x, u) ∈ (pairingEqualityOperator F).graph ↔
      (F (x, u) : EReal) = ERealFunction.pairing (x, u) :=
  Iff.rfl

/-- The graph of `pairingEqualityOperator F` is exactly the pairing-contact set
`{(x, u) | F (x, u) = ⟪x, u⟫}`. -/
theorem graph_pairingEqualityOperator_eq
    {α : Type*} [CoeTC α EReal] (F : H × H → α) :
    (pairingEqualityOperator F).graph =
      {p | (F p : EReal) = ERealFunction.pairing p} :=
  rfl

end BivariateFenchelEquality

end SetValuedOperator
