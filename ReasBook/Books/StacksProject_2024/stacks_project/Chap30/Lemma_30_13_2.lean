import Mathlib
import StacksProject_2024.stacks_project.Chap30.Lemma_30_10_3_Artin_Rees

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}
variable [MonoidalCategory (SheafOfModules X.ringCatSheaf)]
variable [MonoidalClosed (SheafOfModules X.ringCatSheaf)]
variable [MonoidalCategory (SheafOfModules Y.ringCatSheaf)]
variable [MonoidalClosed (SheafOfModules Y.ringCatSheaf)]

-- Semantic recall: Chapter 30 already exposes the ideal-action owner
-- `idealPowerProductSubobject I ℱ 1` for the subsheaf `I \mathcal F`, while
-- `Scheme.IdealSheafData.comap` is the canonical inverse-image ideal-sheaf owner. The
-- source-facing identity `\mathcal I f_* \mathcal F = f_*(f^{-1}\mathcal I \mathcal F)` is
-- therefore recorded directly as an equality between the Chapter 30 ideal-product subobject on
-- `f_* \mathcal F` and the canonical `Subobject.map` pushforward of the inverse-image
-- ideal-product subobject.

/-- Lemma 30.13.2: for an affine morphism `f : Y ⟶ X`, a quasi-coherent
`\mathcal O_Y`-module `\mathcal F`, and an ideal sheaf `\mathcal I` on `X`, the ideal-product
subsheaf of the pushed-forward module is the pushforward of the ideal-product subsheaf cut out by
the inverse-image ideal sheaf `f^{-1}\mathcal I`. -/
@[stacks 01YP]
theorem idealPowerProductSubobject_pushforward_eq_map_of_isAffineHom
    (f : Y ⟶ X) [IsAffineHom f]
    (ℱ : Y.Modules) [ℱ.IsQuasicoherent] (I : X.IdealSheafData) :
    idealPowerProductSubobject I ((pushforward f).obj ℱ) 1 =
      (Subobject.map
          ((pushforward f).map (idealPowerProductSubobject (I.comap f) ℱ 1).arrow)).obj ⊤ := sorry

/-- Affine-open companion to Lemma 30.13.2, obtained by evaluating the canonical subobject
identity on sections over an affine open of `X`. -/
theorem idealSmulTop_pushforwardSections_eq_of_isAffineHom
    (f : Y ⟶ X) [IsAffineHom f]
    (ℱ : Y.Modules) [ℱ.IsQuasicoherent] (I : X.IdealSheafData) (U : X.affineOpens) :
    affineOpenSubsheafSectionsSubmodule
        (idealPowerProductSubobject I ((pushforward f).obj ℱ) 1) U =
      affineOpenSubsheafSectionsSubmodule
        ((Subobject.map
            ((pushforward f).map (idealPowerProductSubobject (I.comap f) ℱ 1).arrow)).obj ⊤) U := by
  let h :=
    idealPowerProductSubobject_pushforward_eq_map_of_isAffineHom f ℱ I
  simpa using congrArg
    (fun 𝒢 : Subobject ((pushforward f).obj ℱ) ↦ affineOpenSubsheafSectionsSubmodule 𝒢 U) h

end AlgebraicGeometry.Scheme.Modules
