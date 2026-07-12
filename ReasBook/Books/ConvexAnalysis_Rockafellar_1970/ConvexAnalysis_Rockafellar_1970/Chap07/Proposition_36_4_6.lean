import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Basic
import ConvexAnalysis_Rockafellar_1970.Chap01.HasPairing
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_2
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_1
import ConvexAnalysis_Rockafellar_1970.Chap07.Theorem_36_5

noncomputable section

universe u u' v

open scoped Rockafellar

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 36.4.6 studies the bifunction on `UStar × X` given by the
  explicit infimum formula `(uStar, x) ↦ inf_u (⟪u, uStar⟫ₚ + F u x)`.
- `core/canonical`: the theorem owner is the Chapter 34 representative
  `upperConcavePairing (F _*)`, with conclusion in `SaddleFunction.IsConcaveConvex`.
- `bridge/view`: the Chapter 6 owner `lagrangian (toOrderDual F)` and the explicit `iInf` formula
  are downstream companion views, via `lagrangian_toOrderDual_eq_upperConcavePairing_inverse` and
  `lagrangian_eq_iInf_pairing_add`.

Domain-style sampling used here:
- `HasLinearPairing` and the derived pairing notation `⟪·, ·⟫ₚ` from `Chap01.HasPairing`;
- `Bifunction.toOrderDual` from `Chap01.EOrder.Basic`;
- `(Function.uncurry F).IsConvex 𝕜` from `Chap01.Theorem_4_2`;
- `Bifunction.lagrangian` from `Chap06.Definition_6_30_13`;
- `lagrangian_toOrderDual_eq_upperConcavePairing_inverse` and
  `lagrangian_eq_iInf_pairing_add` from `Chap07.Theorem_36_5`;
- `SaddleFunction.IsConcaveConvex` from `Chap07.Definition33_0_1`;

Primitive data vs derived API:
- primitive input: `F : U → X → WithBotTop 𝕜` with the convex-bifunction owner
  `(Function.uncurry F).IsConvex 𝕜`;
- primitive pairing owner: `HasLinearPairing U UStar 𝕜`, whose canonical raw and extended-codomain
  pairing views are derived upstream;
- primitive chapter owner: `upperConcavePairing (F _*)`;
- derived companion views: `lagrangian (toOrderDual F)` and the explicit infimum formula.

Layer target: `core/canonical`. The dual-variable concavity side is kept on the chapter's
linear-pairing owner layer rather than on a raw `HasPairing`, because the pairing term must stay
affine in `uStar`.
-/

section Shape

variable {𝕜 : Type*} {U : Type u} {UStar : Type u'} {X : Type v}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [AddCommMonoid U] [Module 𝕜 U]
variable [AddCommMonoid UStar] [Module 𝕜 UStar]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [HasLinearPairing U UStar 𝕜]

open SaddleFunction

local instance : HasPairing UStar U (WithBotTop 𝕜) := HasPairing.swap

/-- Proposition 36.4.6 on the intrinsic Chapter 34 owner: if `F` is jointly convex, then the
inverse-slice upper representative `upperConcavePairing (F _*)` is concave-convex. -/
theorem upperConcavePairing_inverse_isConcaveConvex_of_isConvex
    (F : U → X → WithBotTop 𝕜) (hF : (Function.uncurry F).IsConvex 𝕜) :
    IsConcaveConvex 𝕜 ((upperConcavePairing (F _*)) : UStar → X → WithBotTop 𝕜) := by
  sorry

/-- Companion bridge form of Proposition 36.4.6 on the Chapter 6 kernel
`lagrangian (toOrderDual F)`. -/
theorem lagrangian_toOrderDual_isConcaveConvex_of_isConvex
    (F : U → X → WithBotTop 𝕜) (hF : (Function.uncurry F).IsConvex 𝕜) :
    IsConcaveConvex 𝕜 ((lagrangian (toOrderDual F)) : UStar → X → WithBotTop 𝕜) := by
  sorry

-- Rewrite the bridge owner through `lagrangian_eq_iInf_pairing_add`; the source formula is a
-- companion-only surface to the intrinsic owner theorem above.
/-- Companion source formula form: if `F` is jointly convex, then
`(uStar, x) ↦ inf_u (⟪u, uStar⟫ₚ + F u x)` is concave in `uStar` and convex in `x`. -/
theorem lagrangianFormula_isConcaveConvex_of_isConvex
    (F : U → X → WithBotTop 𝕜) (hF : (Function.uncurry F).IsConvex 𝕜) :
    IsConcaveConvex 𝕜 (fun (uStar : UStar) x ↦ ⨅ u : U, ⟪u, uStar⟫ₚ + F u x) := by
  sorry

/-!
The two companion surfaces are intentionally downstream:
- `lagrangian (toOrderDual F)` is a bridge equality rewrite of `upperConcavePairing (F _*)`;
- the explicit `iInf` kernel is a second bridge rewrite of that same owner theorem.
-/

end Shape

end Bifunction
