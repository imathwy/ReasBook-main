import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_4

noncomputable section

open scoped Rockafellar

universe u v u' v' w

namespace Bifunction

section

variable {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'} {L : Type w}
variable [SupSet L] [InfSet L] [Sub L]
variable [HasPairing U UStar L] [HasPairing X XStar L]

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.30.15 introduces the adjoint of a concave bifunction on the dual
  variables `(x⋆, u⋆)`.
- `core/canonical`: for fixed `x⋆`, the project already owns this mathematics through the
  conjugacy layer `concaveConjugate` followed by `convexConjugate`: first conjugate the slice
  `G u` in `x`, then conjugate the resulting `u`-slice in `u`.
- `bridge/view`: the textbook double-`⨆` formula, plus under stronger right-negation
  compatibility on the `X`-pairing the graph-function bridge to
  `convexConjugate (- Function.uncurry G)`.

Domain-style sampling used here:
- the pairing owners `HasPairing U UStar L` and `HasPairing X XStar L`, with notation `⟪·, ·⟫ₚ`;
- `convexConjugate` from `Chap03.Defn_12_2`, which owns the outer `u`-supremum;
- `concaveConjugate` from `Definition_6_30_4`, which owns the inner `x`-slice conjugation;
- `Bifunction.adjoint` from `Definition_6_30_14`, whose sign-twisted convex owner is
  related but mathematically distinct.

Primitive data vs derived API:
- primitive data: a bifunction `G : U → X → L`;
- primitive ambient data: canonical pairings from `HasPairing`;
- source-facing owner: `concaveAdjoint XStar UStar G : XStar → UStar → L`;
- core owner reused upstream:
  `fun xStar ↦ convexConjugate (fun u ↦ (G u)∗ xStar)`;
- derived API: the outer-conjugate evaluation formula on the generic pairing-codomain layer, then
  in the stronger `WithBotTop` specialization below the textbook double-`⨆` formula and the
  graph-function bridge theorem.

Layer target: `source-facing`, but as a thin bridge to the existing conjugacy layer rather than a
new primitive wheel.
-/

/-- Definition 6.30.15: the adjoint of a concave bifunction `G`, written in the source order
`x⋆ ↦ G*_{x⋆}` on the dual variables. Canonically, for each fixed `x⋆`, this is the Fenchel
conjugate in `u` of the slice `u ↦ (G u)∗ x⋆`. -/
abbrev concaveAdjoint
    (XStar : Type v') (UStar : Type u')
    [HasPairing U UStar L] [HasPairing X XStar L]
    (G : U → X → L) : XStar → UStar → L :=
  fun xStar ↦ (fun u ↦ (G u)∗ xStar)⋆

/- Evaluating `concaveAdjoint G` recalls the canonical outer-conjugate owner. -/
@[simp] theorem concaveAdjoint_apply
    (G : U → X → L)
    (xStar : XStar) (uStar : UStar) :
    concaveAdjoint XStar UStar G xStar uStar =
      (fun u ↦ (G u)∗ xStar)⋆ uStar :=
  rfl

/- Evaluating the outer conjugate gives the canonical one-variable supremum formula. -/
theorem concaveAdjoint_eq_iSup_pairing_sub_concaveConjugate
    (G : U → X → L)
    (xStar : XStar) (uStar : UStar) :
    concaveAdjoint XStar UStar G xStar uStar =
      ⨆ u : U, ⟪u, uStar⟫ₚ - (G u)∗ xStar := by
  simpa [concaveAdjoint] using
    convexConjugate_eq_iSup_pairing_sub (fun u ↦ (G u)∗ xStar) uStar

section ConvexConjugateBridge

variable [Add L] [Neg L] [Neg XStar] [HasPairingNegRight X XStar L]

-- Proof sketch: rewrite `concaveAdjoint` by the derived double-`⨆` source formula, then
-- expand `convexConjugate (- Function.uncurry G)` at `(u⋆, -x⋆)` and use `pairing_neg_right` on
-- the `X`-pairing inside the canonical product pairing.
/-- Under the canonical right-negation compatibility on the `X`-pairing, and with the canonical
product pairing between `(U × X)` and `(UStar × XStar)`, the source concave adjoint is exactly
the Fenchel conjugate of the negated graph function `- Function.uncurry G` evaluated at
`(u⋆, -x⋆)`. This
keeps the source-facing owner while exposing the stronger Chapter 12 bridge when the extra sign
structure is available. -/
theorem concaveAdjoint_eq_convexConjugate_neg_uncurry
    (G : U → X → L) :
    concaveAdjoint XStar UStar G =
      fun (xStar : XStar) (uStar : UStar) ↦
        convexConjugate (- Function.uncurry G) (uStar, -xStar) := sorry

@[simp] theorem concaveAdjoint_eq_convexConjugate_neg_uncurry_apply
    (G : U → X → L) (xStar : XStar) (uStar : UStar) :
    concaveAdjoint XStar UStar G xStar uStar =
      convexConjugate (- Function.uncurry G) (uStar, -xStar) := by
  simpa using
    congrFun
      (congrFun
        (concaveAdjoint_eq_convexConjugate_neg_uncurry (G := G)) xStar)
      uStar

end ConvexConjugateBridge

end

section WithBotTop

variable {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'} {α : Type w}
variable [ConditionallyCompleteLinearOrder α]
variable [HasPairing U UStar α] [HasPairing X XStar α]

section TextbookFormula

variable [AddCommGroup α]

/-- Evaluating `concaveAdjoint G` gives the textbook formula
`sup_u sup_x (G(u, x) - pairing x x⋆ + pairing u u⋆)`. -/
theorem concaveAdjoint_eq_iSup_iSup
    (G : U → X → WithBotTop α)
    (xStar : XStar) (uStar : UStar) :
    concaveAdjoint XStar UStar G xStar uStar =
      ⨆ u : U, ⨆ x : X,
        G u x - ⟪x, xStar⟫ₚ + ⟪u, uStar⟫ₚ := sorry
end TextbookFormula

end WithBotTop

end Bifunction
