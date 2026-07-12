import ConvexAnalysis_Rockafellar_1970.Chap01.HasPairing
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_14
import ConvexAnalysis_Rockafellar_1970.Chap06.Remark_31_4_3
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_33

noncomputable section

universe u v u' v' z

open scoped Rockafellar

namespace Bifunction

section

variable {𝕜 : Type z} {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'}
variable [CommRing 𝕜] [ConditionallyCompleteLattice 𝕜]
variable [AddCommGroup U] [Module 𝕜 U]
variable [AddCommGroup X] [Module 𝕜 X]
variable [AddCommGroup UStar] [Module 𝕜 UStar]
variable [AddCommGroup XStar] [Module 𝕜 XStar]
variable [HasLinearPairing U UStar 𝕜] [HasLinearPairing X XStar 𝕜]

/-!
Source/core/bridge triage:

- `source-facing`: Lemma33.0.34 computes the adjoint of Rockafellar's translated pairing
  perturbation `H(v, y) = F(u + v, y) - ⟪y, x⋆⟫ₚ`.
- `core/canonical`: the chapter owner objects are `translatedSubPairing` for `H` and
  `adjoint` for `H⋆`.
- `bridge/view`: the textbook displayed infimum formula is packaged here as the canonical equality
  of adjoint bifunctions, so later uses can rewrite directly at the owner level.

The assumptions stay at the linear-pairing layer because the owner proof reuses the Chapter 6
translation theorem `convexConjugate_translate_sub_pairing` on the product pairing, and the
pairing additivity/zero identities are derived from `HasLinearPairing`.
-/

variable (F : U → X → WithTopBot 𝕜) (u : U) (xStar : XStar)

local notation "F⋆" => adjoint XStar UStar F
local notation "H⋆" => adjoint XStar UStar H[F | u, xStar]

/-- Lemma33.0.34: the adjoint of the translated pairing perturbation `H(v, y) = F(u + v, y) -
⟪y, xStar⟫ₚ` is the shifted adjoint slice `F⋆(xStar + yStar, vStar)` minus the pairing
`⟪u, vStar⟫ₚ`. -/
theorem adjoint_translatedSubPairing :
    H⋆ =
      fun (yStar : XStar) (vStar : UStar) ↦
        F⋆ (xStar + yStar) vStar - ⟪u, vStar⟫ₚ := by
  ext yStar vStar
  change
    -((Function.uncurry (H[F | u, xStar]))⋆ (-vStar, yStar)) =
      -((Function.uncurry F)⋆ (-vStar, xStar + yStar)) - ⟪u, vStar⟫ₚ
  have htranslate :=
    congrFun
      (convexConjugate_translate_sub_pairing (Function.uncurry F) (u, (0 : X))
        ((0 : UStar), xStar))
      (-vStar, yStar)
  have hpair_left :
      (⟪(u, (0 : X)), (-vStar, yStar)⟫ₚ : WithTopBot 𝕜) = -⟪u, vStar⟫ₚ := by
    rw [pairing_prod]
    simp [HasLinearPairing.pairing_eq_pairingLinear]
  have hpair_right :
      (⟪(u, (0 : X)), ((0 : UStar), xStar)⟫ₚ : WithTopBot 𝕜) = 0 := by
    rw [pairing_prod]
    simp [HasLinearPairing.pairing_eq_pairingLinear]
  have htranslate' :
      (Function.uncurry (H[F | u, xStar]))⋆ (-vStar, yStar) =
        (Function.uncurry F)⋆ (-vStar, xStar + yStar) + ⟪u, vStar⟫ₚ := by
    have htranslate'' :
        (Function.uncurry (H[F | u, xStar]))⋆ (-vStar, yStar) =
          (Function.uncurry F)⋆ (-vStar, xStar + yStar) +
            (-⟪(u, (0 : X)), (-vStar, yStar)⟫ₚ + -⟪(u, (0 : X)), ((0 : UStar), xStar)⟫ₚ) := by
      simpa [uncurry_translatedSubPairing, Function.uncurry, sub_eq_add_neg, add_assoc, add_left_comm,
        add_comm] using
        (show
          (fun x : U × X ↦ (Function.uncurry F) ((u, (0 : X)) + x) - ⟪x, ((0 : UStar), xStar)⟫ₚ)⋆
              (-vStar, yStar) =
            (Function.uncurry F)⋆ (((0 : UStar), xStar) + (-vStar, yStar)) -
              ⟪(u, (0 : X)), (-vStar, yStar)⟫ₚ - ⟪(u, (0 : X)), ((0 : UStar), xStar)⟫ₚ from
            htranslate)
    rw [hpair_left, hpair_right] at htranslate''
    simpa [add_assoc, add_left_comm, add_comm] using htranslate''
  let b : WithBotTop 𝕜 := (show WithBotTop 𝕜 from (⟪u, vStar⟫ₚ : WithTopBot 𝕜))
  have htop : b ≠ ⊤ := by
    change (((⟪u, vStar⟫ₚ : 𝕜) : WithBotTop 𝕜)) ≠ ⊤
    exact WithBotTop.coe_ne_top (⟪u, vStar⟫ₚ : 𝕜)
  have hbot : b ≠ ⊥ := by
    change (((⟪u, vStar⟫ₚ : 𝕜) : WithBotTop 𝕜)) ≠ ⊥
    exact WithBotTop.coe_ne_bot (⟪u, vStar⟫ₚ : 𝕜)
  calc
    -((Function.uncurry (H[F | u, xStar]))⋆ (-vStar, yStar)) =
        -((Function.uncurry F)⋆ (-vStar, xStar + yStar) + ⟪u, vStar⟫ₚ) := by
      rw [htranslate']
    _ = -((Function.uncurry F)⋆ (-vStar, xStar + yStar)) - ⟪u, vStar⟫ₚ := by
      let a : WithBotTop 𝕜 :=
        (show WithBotTop 𝕜 from (Function.uncurry F)⋆ (-vStar, xStar + yStar))
      change -(a + b) = -a - b
      simpa using
        ((WithBotTop.neg_add (Or.inr htop) (Or.inr hbot)) : -(a + b) = -a + -b)

/-- Evaluating `H⋆`, the adjoint of `translatedSubPairing F u xStar`, gives the shifted adjoint
slice `F⋆` minus the pairing term `⟪u, vStar⟫ₚ`. -/
@[simp] theorem adjoint_translatedSubPairing_apply
    (yStar : XStar) (vStar : UStar) :
    H⋆ yStar vStar =
      F⋆ (xStar + yStar) vStar - ⟪u, vStar⟫ₚ := by
  exact congrFun (congrFun (adjoint_translatedSubPairing F u xStar) yStar) vStar

end

end Bifunction
