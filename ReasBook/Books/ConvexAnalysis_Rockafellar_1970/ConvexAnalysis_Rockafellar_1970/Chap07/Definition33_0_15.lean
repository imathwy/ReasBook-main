import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_8

noncomputable section

universe u v u' w

open scoped Rockafellar
open Function

namespace Bifunction

section

variable {U : Type u} {X : Type v} {Y : Type u'} {L : Type w}
variable [SupSet L] [Sub L]
variable [HasPairing (U × X) Y L]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Definition33.0.15 introduces the ordinary conjugate of a bifunction
  `F : U → X → L`, viewed in the book as a map on dual variables `(u⋆, x⋆)`.
- `core/canonical`: this is Fenchel conjugation of the uncurried graph function
  `uncurry F` under a pairing on the product source `U × X`.
- `bridge/view`: the source item is the pointwise reading of that canonical owner at a dual
  variable `y`; on theorem surfaces this is the chapter pairing notation `⟪·, ·⟫ᶠ` from
  Definition33.0.8.

Domain-style sampling used here:
- `convexConjugate`;
- `Function.convexPairing_eq_iSup_pairing_sub`;
- convex pairing notation `⟪f, y⟫ᶠ`;
- the product-space owner input `uncurry F`.

Primitive data vs derived API:
- primitive owner: `convexConjugate` on functions into `L`;
- primitive input here: `uncurry F : U × X → L`;
- derived view in this file: Definition33.0.15 is that owner read at `y : Y`.

Layer target: `bridge/view`.
-/

/-
Definition33.0.15: the ordinary conjugate of a bifunction is already the canonical Fenchel
conjugate `convexConjugate` applied to the uncurried graph function `uncurry F`.
-/
recall convexConjugate
recall Function.convexPairing_eq_iSup_pairing_sub

variable (F : U → X → L) (y : Y)

/- The displayed source formula is the direct specialization of
`Function.convexPairing_eq_iSup_pairing_sub` to the uncurried graph function `uncurry F`,
written on the existing chapter pairing-notation surface. -/
#check
  (Function.convexPairing_eq_iSup_pairing_sub (uncurry F) y :
    ⟪uncurry F, y⟫ᶠ =
      ⨆ ux : U × X, ⟪ux, y⟫ₚ - uncurry F ux)

end

end Bifunction
