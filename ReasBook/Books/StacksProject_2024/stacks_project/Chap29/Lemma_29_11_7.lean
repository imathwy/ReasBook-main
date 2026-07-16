import Mathlib
import StacksProject_2024.stacks_project.Chap06.Definition_6_26_1
import StacksProject_2024.stacks_project.Chap29.Lemma_29_11_6

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.ObjectProperty
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry

section

variable {X S : Scheme.{u}} (f : X ⟶ S)

local notation "J" => Opens.grothendieckTopology S
local notation "𝒜" => Functor.obj (TopCat.Sheaf.pushforward CommRingCat f.base) X.sheaf
local notation "Mod(" 𝒪 ")" => ringedSiteModuleCategory J 𝒪

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-module pushforward owner
-- `Scheme.Modules.pushforward`. Chapter 6 records the raw `f_* 𝒪_X`-module owner as the identity-
-- pushforward functor `SheafOfModules.pushforward (𝟙 (f_* 𝒪_X))`, and full-subcategory
-- restrictions in this repository are expressed with `ObjectProperty.lift`.

/-- The direct image `f_* ℱ`, viewed as a module over `f_* \mathcal O_X`, is quasi-coherent when
`f` is affine and `ℱ` is quasi-coherent on `X`. -/
theorem pushforwardAsModule_obj_isQuasicoherent_of_isAffineHom
    {ℱ : X.Modules} [ℱ.IsQuasicoherent] (hf : IsAffineHom f) :
    ((SheafOfModules.pushforward (𝟙 (ringSheaf J 𝒜))).obj ℱ).IsQuasicoherent := sorry

/-- Lemma 29.11.7 (1): if `f : X ⟶ S` is an affine morphism of schemes and
`\mathcal A = f_* \mathcal O_X`, then the functor `\mathcal F ↦ f_* \mathcal F`, viewed as taking
values in `\mathcal A`-modules, induces an equivalence from the category of quasi-coherent
`\mathcal O_X`-modules to the category of quasi-coherent `\mathcal A`-modules. -/
@[stacks 01SB]
theorem affinePushforwardAsModule_isEquivalence
    (hf : IsAffineHom f) :
    Functor.IsEquivalence
      (ObjectProperty.lift (fun ℱ : Mod(𝒜) ↦ ℱ.IsQuasicoherent)
        ((ObjectProperty.ι (fun ℱ : X.Modules ↦ ℱ.IsQuasicoherent)) ⋙
          (SheafOfModules.pushforward (𝟙 (ringSheaf J 𝒜))))
        (fun ℱ ↦
          let _ :
              ((ObjectProperty.ι (fun ℱ : X.Modules ↦ ℱ.IsQuasicoherent)).obj ℱ).IsQuasicoherent :=
            ℱ.property
          pushforwardAsModule_obj_isQuasicoherent_of_isAffineHom f hf)) := sorry

/-- Lemma 29.11.7 (2): if `f : X ⟶ S` is an affine morphism of schemes and
`\mathcal A = f_* \mathcal O_X`, then an `\mathcal A`-module is quasi-coherent as an
`\mathcal O_S`-module if and only if it is quasi-coherent as an `\mathcal A`-module. -/
@[stacks 01SB]
theorem pushforwardStructureSheafModule_isQuasicoherent_iff
    (hf : IsAffineHom f) (ℱ : Mod(𝒜)) :
    ((restrictionAlong (RingedSpace.Hom.commRingSheafPushforwardMap f.toShHom)).obj ℱ).IsQuasicoherent ↔
      ℱ.IsQuasicoherent := sorry

end

end AlgebraicGeometry
