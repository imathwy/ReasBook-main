import Mathlib
import StacksProject_2024.Chap17.Definition_17_14_1
import StacksProject_2024.Chap20.Definition_20_26_14

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry

noncomputable section

set_option checkBinderAnnotations false

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace}

/-- The structure-sheaf morphism `\mathcal O_Y \to f_*\mathcal O_X` attached to a morphism of
ringed spaces, after forgetting commutativity. -/
noncomputable abbrev projectionFormulaPushforwardStructureSheafHom (f : X ⟶ Y) :
    (RingedSpace.ringCatSheaf Y) ⟶
      (TopCat.Sheaf.pushforward RingCat f.hom.base).obj (RingedSpace.ringCatSheaf X) :=
  (sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat RingCat)).map
    (show Y.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat f.hom.base).obj X.sheaf from
      ⟨f.hom.c⟩)

/-- The direct-image functor on `\mathcal O_X`-modules induced by `f`. -/
noncomputable abbrev projectionFormulaModulePushforward (f : X ⟶ Y) :
    (RingedSpace.Modules X) ⥤ (RingedSpace.Modules Y) :=
  SheafOfModules.pushforward (projectionFormulaPushforwardStructureSheafHom f)

/-- The pullback functor on `\mathcal O_Y`-modules induced by `f`. -/
noncomputable abbrev projectionFormulaModulePullback (f : X ⟶ Y) :
    (RingedSpace.Modules Y) ⥤ (RingedSpace.Modules X) :=
  SheafOfModules.pullback (projectionFormulaPushforwardStructureSheafHom f)

-- Proof sketch: resolve `ℱ` by injectives on `X`; tensoring that resolution with the finite
-- locally free pullback `f^*ℰ` stays injective, so the higher direct images of
-- `f^*ℰ ⊗ \mathcal F` can be computed after tensoring the chosen resolution. The underived
-- identity `f_*(f^*ℰ ⊗ -) ≅ ℰ ⊗ f_*(-)` then yields the claimed isomorphism degreewise.
/-- Lemma 20.54.2: if `f : X ⟶ Y` is a morphism of ringed spaces, `ℱ` is an `\mathcal O_X`-module,
and `ℰ` is a finite locally free `\mathcal O_Y`-module, then for every `q ≥ 0` there is an
isomorphism
`ℰ \otimes_{\mathcal O_Y} R^q f_* \mathcal F \cong
R^q f_* (f^* \mathcal E \otimes_{\mathcal O_X} \mathcal F)`. -/
theorem finiteLocallyFree_projectionFormula_higherDirectImage
    (f : X ⟶ Y) [(projectionFormulaModulePushforward f).Additive]
    [HasInjectiveResolutions (RingedSpace.Modules X)]
    [MonoidalCategory (RingedSpace.Modules X)] [MonoidalCategory (RingedSpace.Modules Y)]
    (ℰ : (RingedSpace.Modules Y)) [SheafOfModules.IsFiniteLocallyFree ℰ] (ℱ : (RingedSpace.Modules X)) (q : ℕ) :
    IsIsomorphic
      (ℰ ⊗ (((projectionFormulaModulePushforward f).rightDerived q).obj ℱ))
      (((projectionFormulaModulePushforward f).rightDerived q).obj
        (((projectionFormulaModulePullback f).obj ℰ) ⊗ ℱ)) := sorry

end AlgebraicGeometry.RingedSpace
