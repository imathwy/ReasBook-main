import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

open scoped Rockafellar

section

variable {X : Type u} {Y : Type v} {L : Type w}
variable [InfSet L] [Sub L] [HasPairing X Y L]

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.30.4 introduces the conjugate `g*` of a concave function `g` by
  the infimum formula `inf_x (pairing x y - g x)`.
- `core/canonical`: the actual owner abstraction is already Chapter 12's `convexConjugate`,
  applied on the order-dual codomain `OrderDual L`, since `InfSet L` is exactly `SupSet (OrderDual
  L)` and the source formula is the same conjugation operator viewed in the reversed order.
- `bridge/view`: this file keeps the source-facing Chapter 6 name `concaveConjugate` and notation
  `g∗`, but only as the thin order-dual view of that existing owner.

Domain-style sampling used here:
- the Chapter 12 pairing owner `convexConjugate`;
- an ambient codomain `L` carrying the primitive operations used by the source formula;
- indexed infima `⨅ x, ...` as the primitive source formula.

Primitive data vs derived API:
- primitive input: a function `g : X → L`;
- canonical owner upstream: `convexConjugate` on `OrderDual L`;
- source-facing bridge owner in this file: `concaveConjugate g : Y → L`;
- derived API in this file: only the immediate pointwise `⨅` restatement.

Layer target: `bridge/view`. The source genuinely introduces a concave-side conjugation formula,
but its canonical owner is already the Chapter 12 conjugate on the order-dual codomain, so this
file should expose only the source-facing view rather than a second primitive wheel.
-/

/-- Definition 6.30.4: the Chapter 6 concave-side conjugate owner, implemented as
the order-dual view of the Chapter 12 owner `convexConjugate`. -/
def concaveConjugate : (X → L) → (Y → L) :=
  (convexConjugate : (X → OrderDual L) → Y → OrderDual L)

-- Source-facing notation `g∗` is directly the Chapter 6 bridge owner.
-- Keeping the notation on the owner directly avoids fragile elaboration through local lambdas.
scoped[Rockafellar] postfix:max "∗" => concaveConjugate

/-- Owner-level bridge: the Chapter 6 concave conjugate is exactly the Chapter 12 Fenchel
conjugate on the order-dual codomain. -/
@[simp] theorem concaveConjugate_eq_convexConjugate (g : X → L) :
    g∗ = (g⋆ : Y → OrderDual L) :=
  rfl

/-- Evaluating the concave conjugate `g∗` at `y` gives the source infimum formula
`inf_x (pairing x y - g x)`. -/
theorem concaveConjugate_eq_iInf_pairing_sub
    (g : X → L) (y : Y) :
    g∗ y =
      ⨅ x : X, ⟪x, y⟫ₚ - g x :=
  rfl

end
