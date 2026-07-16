import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

open scoped Rockafellar

section WithTopBotPairingCompat

variable {X : Type u} {Y : Type v} {α : Type w}
variable [HasPairing X Y α]

/-- Lift left-addition pairing compatibility from `α` to `WithTopBot α`. -/
instance instHasPairingAddLeftWithTopBot
    [Add X] [Add α] [HasPairingAddLeft X Y α] :
    HasPairingAddLeft X Y (WithTopBot α) where
  pairing_add_left x₁ x₂ y := by
    simpa [coe_add] using
      congrArg (fun t : α ↦ (t : WithTopBot α))
        (HasPairingAddLeft.pairing_add_left (X := X) (Y := Y) (𝕜 := α) x₁ x₂ y)

/-- Lift right-subtraction pairing compatibility from `α` to `WithTopBot α`. -/
instance instHasPairingSubRightWithTopBot
    [Sub Y] [AddGroup α] [HasPairingSubRight X Y α] :
    HasPairingSubRight X Y (WithTopBot α) where
  pairing_sub_right x y₁ y₀ := by
    simpa [coe_sub] using
      congrArg (fun t : α ↦ (t : WithTopBot α))
        (HasPairingSubRight.pairing_sub_right (X := X) (Y := Y) (𝕜 := α) x y₁ y₀)

end WithTopBotPairingCompat

section

variable {X : Type u} {Y : Type v} {α : Type w}
variable [SupSet (WithTopBot α)] [Add (WithTopBot α)] [Sub (WithTopBot α)]
variable [Sub X] [Sub Y]
variable [HasPairing X Y (WithTopBot α)]
variable [HasPairingAddLeft X Y (WithTopBot α)] [HasPairingSubRight X Y (WithTopBot α)]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 12.3 gives the affine-conjugation formula
  `(fun x ↦ h (A (x - a)) + ⟪x, a⋆⟫ₚ + β)⋆`.
- `core/canonical`: the owner declaration is `convexConjugate` on the pairing layer
  `HasPairing X Y (WithTopBot α)`, with chapter-facing codomain `WithTopBot α`, together with
  the minimal pairing-compatibility owners needed by the affine-shift algebra
  (`HasPairingAddLeft`, `HasPairingSubRight`).
- `bridge/view`: the textbook dual inverse `A^{*-1}` is modeled by an explicit dual-side
  bijection parameter `AStar.symm`, with the pairing-compatibility hypothesis
  `⟪A x, x⋆⟫ₚ = ⟪x, AStar x⋆⟫ₚ`.

Domain-style sampling used here:
- `convexConjugate` together with the chapter notation `f⋆`;
- `convexConjugate_eq_iSup_pairing_sub`;
- the pairing notation owner `⟪·, ·⟫ₚ`;
- dual-bijection transport on the dual side through `AStar`.

Primitive data vs derived API:
- primitive inputs: the `WithTopBot α`-valued function `h`, bijections `A` and `AStar`, the
  pairing-compatibility witness `hAStar`, the vectors `a`, `a⋆`, and the scalar shift `β`;
- primitive owner-side data already upstream: the conjugation operator on pairings;
- primitive compatibility owners used by the affine-shift formula:
  `HasPairingAddLeft X Y (WithTopBot α)` and `HasPairingSubRight X Y (WithTopBot α)`.
- derived API here: the single textbook affine-change formula for the transformed function.

Layer target: `source-facing`; this file keeps the textbook formula as the public theorem while
moving the owner to the intrinsic pairing layer and removing dependence on inner-product
self-duality.
-/

-- Proof sketch: expand both conjugates with `convexConjugate_eq_iSup_pairing_sub`; reindex the
-- primal variable by the translation `x ↦ x + a`; move the finite affine term outside the
-- supremum; and use the compatibility identity `hAStar` to rewrite the transformed pairing term
-- through `AStar.symm`.
theorem convexConjugate_affineChange
    (h : X → WithTopBot α) (A : X ≃ X) (AStar : Y ≃ Y)
    (hAStar : ∀ x xStar, ⟪A x, xStar⟫ₚ = ⟪x, AStar xStar⟫ₚ)
    (a : X) (aStar : Y) (β : WithTopBot α) :
    (fun x ↦ h (A (x - a)) + ⟪x, aStar⟫ₚ + β)⋆ =
      fun xStar ↦
        h⋆ (AStar.symm (xStar - aStar)) +
          (⟪a, xStar⟫ₚ - β - ⟪a, aStar⟫ₚ) := by
  sorry

end
