import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_4
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_4
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_14
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_8

noncomputable section

universe u v u' v' w z u1

open scoped Rockafellar

namespace Bifunction

/-!
Source/core/bridge triage for this item.

- `source-facing`: Definition33.0.28 recalls the chapter's convex-bifunction notion together with
  the adjoint `F⋆` and the two slice pairings `⟨F u, x⋆⟩` and `⟨u, F⋆ x⋆⟩`.
- `core/canonical`: the owner layer already present in the project is
  `convᵇ[𝕜](F)` (equivalently `(Function.uncurry F).IsConvex 𝕜`) for graph convexity,
  `Bifunction.adjoint` for the
  adjoint, `convexConjugate` for the first slice pairing, and `concaveConjugate` for the second.
- `bridge/view`: the convexity clause is pure canonical recall/use, while the adjoint and pairing
  formulas below are thin source-facing companions over those existing owners.

Domain-style sampling used here:
- the Chapter 6 convex-bifunction owner notation `convᵇ[𝕜](F)` from `Chap06.Definition_6_29_4`;
- `Bifunction.adjoint` from `Chap06.Definition_6_30_14`;
- `convexConjugate_eq_iSup_pairing_sub` from `Chap03.Defn_12_2`;
- `concaveConjugate_eq_iInf_pairing_sub` from `Chap06.Definition_6_30_4`.

Primitive data vs derived API:
- primitive source data: a bifunction `F : U → X → L`;
- canonical graph-convexity owner: `convᵇ[𝕜](F)` (owner definition
  `(Function.uncurry F).IsConvex 𝕜`);
- reused canonical owners: `adjoint F`, `convexConjugate_eq_iSup_pairing_sub` applied to
  the slice `F u`, `⟪F u, xStar⟫ᶠ`, and `⟪u, adjoint F xStar⟫ᶜ`;
- derived API here: the textbook pointwise formulas for the adjoint and the two pairings, with the
  `WithTopBot` infimum formulas exposed as bridge/view corollaries.

Layer target: convexity is `core/canonical recall/use`; the adjoint and pairing formulas are
`bridge/view`, kept at the canonical pairing-based owner layer instead of introducing a new
Euclidean or inner-product-specific package.
-/

section Convex

variable {𝕜 : Type z} {U : Type u} {X : Type v} {L : Type w}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid U] [SMul 𝕜 U]
variable [AddCommMonoid X] [SMul 𝕜 X]
variable [AddCommMonoid L] [SMul 𝕜 L] [LE L]

variable (F : U → X → L)

/- Definition33.0.28: the convex-bifunction notion is already the Chapter 6 canonical owner
notation `convᵇ[𝕜](F)` (definitionally `(Function.uncurry F).IsConvex 𝕜`); no parallel
`Bifunction.IsConvex` wrapper is introduced. -/
#check (convᵇ[𝕜](F) : Prop)

end Convex

section FirstPairing

variable {U : Type u} {X : Type v} {XStar : Type v'} {L : Type w}
variable [Sub L] [SupSet L] [HasPairing X XStar L]

variable (F : U → X → L) (u : U) (xStar : XStar)

/- The first textbook pairing `⟨F u, x⋆⟩` is already the canonical owner formula
`convexConjugate_eq_iSup_pairing_sub` applied to the slice `F u`. -/
#check
  (convexConjugate_eq_iSup_pairing_sub (F u) xStar :
    ⟪F u, xStar⟫ᶠ =
      ⨆ x : X, ⟪x, xStar⟫ₚ - F u x)

end FirstPairing

section Adjoint

variable {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'} {L : Type u1}
variable [Sub L] [Neg L] [SupSet L]
variable [Neg UStar]

/- The source adjoint bifunction `F⋆` is already the canonical owner
`Bifunction.adjoint`. -/
recall Bifunction.adjoint

/-- Evaluating the adjoint bifunction gives the primitive product-space formula as a negated
supremum:
`-sup_{(u, x)} (⟪(u, x), (-u⋆, x⋆)⟫ - F(u, x))`. -/
theorem adjoint_apply_eq_neg_iSup_pairing_sub_prod
    [HasPairing (U × X) (UStar × XStar) L]
    (F : U → X → L) (xStar : XStar) (uStar : UStar) :
    F⋆ xStar uStar =
      - (⨆ ux : U × X, ⟪ux, (-uStar, xStar)⟫ₚ - Function.uncurry F ux) := by
  calc
    F⋆ xStar uStar = - ((Function.uncurry F)⋆ (-uStar, xStar)) := by
      exact adjoint_apply F xStar uStar
    _ = - (⨆ ux : U × X, ⟪ux, (-uStar, xStar)⟫ₚ - Function.uncurry F ux) := by
      rw [convexConjugate_eq_iSup_pairing_sub]

section WithTopBot

variable {α : Type u1}
variable [AddCommGroup α] [ConditionallyCompleteLattice α] [IsOrderedAddMonoid α]

/-- On `WithTopBot α`, evaluating the adjoint bifunction gives the source-facing product-space
infimum formula `inf_{(u, x)} (F(u, x) - ⟪(u, x), (-u⋆, x⋆)⟫)`. -/
theorem adjoint_apply_eq_iInf_sub_pairing_prod
    [HasPairing (U × X) (UStar × XStar) α]
    (F : U → X → WithTopBot α) (xStar : XStar) (uStar : UStar) :
    F⋆ xStar uStar =
      ⨅ ux : U × X, Function.uncurry F ux - ⟪ux, (-uStar, xStar)⟫ₚ := by
  calc
    F⋆ xStar uStar = - ((Function.uncurry F)⋆ (-uStar, xStar)) := by
      exact adjoint_apply F xStar uStar
    _ = -(- (⨅ ux : U × X, Function.uncurry F ux - ⟪ux, (-uStar, xStar)⟫ₚ)) := by
      rw [convexConjugate_eq_neg_iInf_sub_pairing]
    _ = ⨅ ux : U × X, Function.uncurry F ux - ⟪ux, (-uStar, xStar)⟫ₚ := by simp

section SplitPairingFormula

variable [HasPairing U UStar α] [HasPairing X XStar α]
variable [HasPairingNegRight U UStar α]

/-- Evaluating the adjoint bifunction gives the textbook infimum formula
`inf_{u, x} (F(u, x) - ⟪x, x⋆⟫ + ⟪u, u⋆⟫)`. -/
-- Proof sketch: start from the primitive product-space infimum formula and then expand the
-- product pairing into the two displayed pairings.
theorem adjoint_apply_eq_iInf_pairing_sub_add_pairing
    (F : U → X → WithTopBot α) (xStar : XStar) (uStar : UStar) :
    F⋆ xStar uStar =
      ⨅ u : U, ⨅ x : X, F u x - ⟪x, xStar⟫ₚ + ⟪u, uStar⟫ₚ := by
  calc
    F⋆ xStar uStar = ⨅ ux : U × X, Function.uncurry F ux - ⟪ux, (-uStar, xStar)⟫ₚ := by
      simpa using adjoint_apply_eq_iInf_sub_pairing_prod F xStar uStar
    _ = ⨅ u : U, ⨅ x : X, F u x - ⟪x, xStar⟫ₚ + ⟪u, uStar⟫ₚ := by
      rw [iInf_prod]
      refine iInf_congr fun u ↦ ?_
      refine iInf_congr fun x ↦ ?_
      have hpair :
          (((⟪u, -uStar⟫ₚ : α) : WithTopBot α)) = -(((⟪u, uStar⟫ₚ : α) : WithTopBot α)) := by
        exact
          congrArg ((↑) : α → WithTopBot α)
            (HasPairingNegRight.pairing_neg_right u uStar)
      let pu : WithTopBot α := ((⟪u, uStar⟫ₚ : α) : WithTopBot α)
      let puminus : WithTopBot α := ((⟪u, -uStar⟫ₚ : α) : WithTopBot α)
      let px : WithTopBot α := ((⟪x, xStar⟫ₚ : α) : WithTopBot α)
      change
        F u x - (puminus + px) = F u x - px + pu
      have hpuminus : puminus = -pu := by
        simpa [puminus, pu] using hpair
      rw [hpuminus]
      have hneg_add : -(-pu + px) = -(-pu) - px := by
        refine WithBotTop.neg_add ?_ ?_
        · exact Or.inl (by simp [pu])
        · exact Or.inl (by simp [pu])
      rw [WithBotTop.sub_eq_add_neg]
      rw [hneg_add]
      simp [WithBotTop.sub_eq_add_neg, add_left_comm, add_comm]

end SplitPairingFormula

end WithTopBot

end Adjoint

section SecondPairing

variable {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'} {L : Type u1}
variable [Sub L] [Neg L] [SupSet L] [InfSet L]
variable [Neg UStar]
variable [HasPairing U UStar L] [HasPairing (U × X) (UStar × XStar) L]

/-- The reversed pairing lets the second textbook pairing be read as a concave conjugate of the
adjoint slice. -/
local instance reversedPairing : HasPairing UStar U L :=
  HasPairing.swap

variable (F : U → X → L) (u : U) (xStar : XStar)

local notation "F⋆" => adjoint XStar UStar F

/- The second textbook pairing `⟨u, F⋆ x⋆⟩` is already the canonical owner formula
`concaveConjugate_eq_iInf_pairing_sub` applied to the adjoint slice `F⋆ xStar`; with the local
swapped pairing above, the source-facing chapter notation elaborates directly. -/
#check
  (concaveConjugate_eq_iInf_pairing_sub (F⋆ xStar) u :
    ⟪u, F⋆ xStar⟫ᶜ =
      ⨅ uStar : UStar, ⟪u, uStar⟫ₚ - F⋆ xStar uStar)

end SecondPairing

end Bifunction
