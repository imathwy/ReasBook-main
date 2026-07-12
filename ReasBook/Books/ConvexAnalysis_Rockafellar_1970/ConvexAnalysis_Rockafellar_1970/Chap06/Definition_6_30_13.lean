import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2

noncomputable section

universe u v w z

namespace Bifunction

section

variable {U : Type u} {X : Type v} {UStar : Type w} {L : Type z}
variable [SupSet L] [Sub L] [Neg L] [HasPairing U UStar L]

open scoped Rockafellar

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.30.13 introduces the Lagrangian of the concave program attached
  to a bifunction `G`, with source formula `L(u⋆, x) = sup_u (⟪u, u⋆⟫ₚ + G u x)`.
- `core/canonical`: the owner abstraction for this supremum formula is the existing
  pairing-based Fenchel conjugate owner `convexConjugate`, applied to the negated `u`-slice
  `u ↦ -G u x`. This is the same mathematical object as the older product-kernel
  `partialSupremum` presentation, but it removes a duplicate local wheel and aligns the public
  API with the chapter's pairing/conjugation vocabulary.
- `bridge/view`: the source display formula is recovered by the immediate pointwise
  `iSup`-formula for `convexConjugate`.

Domain-style sampling used here:
- `HasPairing` and the notation `⟪·, ·⟫ₚ` from `Chap01.HasPairing` as the project owner for dual
  evaluation data;
- `convexConjugate` from `Chap03.Defn_12_2` as the canonical owner of
  `sup_u (⟪u, u⋆⟫ₚ - f u)`;
- `convexConjugate_eq_iSup_pairing_sub` from the same file as the canonical evaluation formula;
- `Function.partialSupremum` from `Chap01.Text_5_7_2` as the lower-level product-kernel owner
  that this file now avoids duplicating;
- `Bifunction.upperPerturbationFunction` from `Definition_6_30_11` as the neighboring
  slice-supremum owner pattern in Chapter 6.

Primitive data vs derived API:
- primitive ambient pairing data: `[HasPairing U UStar L]`;
- primitive bifunction data: `G : U → X → L`;
- source-facing owner introduced here: `Bifunction.lagrangian G`;
- core owner reused upstream: `convexConjugate (fun u ↦ -G u x)` on each `x`-slice;
- derived API: the source `iSup` formula `⨆ u, ⟪u, u⋆⟫ₚ + G u x` under additive
  assumptions, together with the weaker bridge formula `⨆ u, ⟪u, u⋆⟫ₚ - (-G u x)` used when
  only subtraction/negation is available.

Layer target: `source-facing`. The source genuinely names a Lagrangian attached to `G`, but the
definition is now expressed as a thin bridge to the canonical conjugate owner rather than as a
parallel local `partialSupremum` construction.
-/

/-- Definition 6.30.13: the Lagrangian of the concave program associated with a bifunction `G`,
implemented canonically as the Fenchel conjugate of the negated `u`-slice `u ↦ -G u x`. Its
source formula is `sup_u (⟪u, u⋆⟫ₚ + G u x)`. -/
abbrev lagrangian (G : U → X → L) : UStar → X → L :=
  fun uStar x ↦ (fun u ↦ -G u x)⋆ uStar

/-- Pointwise owner form of Definition 6.30.13: at each fixed `x`, `lagrangian G` is the Fenchel
conjugate of the negated slice `u ↦ -G u x`. -/
@[simp] theorem lagrangian_apply
    (G : U → X → L) (uStar : UStar) (x : X) :
    lagrangian G uStar x = (fun u ↦ -G u x)⋆ uStar :=
  rfl

end

section SourceFormula

variable {U : Type u} {X : Type v} {UStar : Type w} {L : Type z}
variable [SupSet L] [SubtractionMonoid L] [HasPairing U UStar L]

open scoped Rockafellar

/-- Evaluating `lagrangian G` at `(u⋆, x)` gives Rockafellar's source formula
`sup_u (⟪u, u⋆⟫ₚ + G u x)`. -/
theorem lagrangian_eq_iSup_pairing_add
    (G : U → X → L) (uStar : UStar) (x : X) :
    lagrangian G uStar x =
      ⨆ u : U, ⟪u, uStar⟫ₚ + G u x := by
  simpa [sub_neg_eq_add] using
    convexConjugate_eq_iSup_pairing_sub (fun u ↦ -G u x) uStar

end SourceFormula

section Bridge

variable {U : Type u} {X : Type v} {UStar : Type w} {L : Type z}
variable [SupSet L] [Sub L] [Neg L] [HasPairing U UStar L]

open scoped Rockafellar

/-- Bridge form of the Lagrangian evaluation formula, keeping only the primitive codomain
operations needed by the conjugate owner:
`sup_u (⟪u, u⋆⟫ₚ - (-G u x))`. This is the form used for order-dual downstream bridges such as
Chapter 7's infimum formulas. -/
theorem lagrangian_eq_iSup_pairing_sub
    (G : U → X → L) (uStar : UStar) (x : X) :
    lagrangian G uStar x =
      ⨆ u : U, ⟪u, uStar⟫ₚ - (-G u x) := by
  simpa using convexConjugate_eq_iSup_pairing_sub (fun u ↦ -G u x) uStar

end Bridge

end Bifunction
