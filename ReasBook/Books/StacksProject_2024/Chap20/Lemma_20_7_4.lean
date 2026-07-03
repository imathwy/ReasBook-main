import Mathlib
import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap06.Definition_6_31_2
import StacksProject_2024.Chap06.Restriction_and_extension_by_zero_for_module_valued_sheaves

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/-- The `RingCat`-valued structure sheaf on an open subspace agrees with restricting the
ambient `RingCat`-valued structure sheaf to that open. -/
-- Proof sketch: unfold the open-subspace structure sheaf as pullback of the ambient
-- `CommRingCat`-valued structure sheaf, then commute the forgetful functor
-- `CommRingCat ⥤ RingCat` with this pullback.
private theorem restrict_ringCatSheaf_eq
    {X : RingedSpace.{u}} (U : Opens X.carrier) :
    RingedSpace.ringCatSheaf (X.restrict U.isOpenEmbedding) =
      (TopCat.Sheaf.pullback RingCat.{u} U.inclusion').obj ((RingedSpace.ringCatSheaf X)) := sorry

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)

/-- The image of the restriction of `f` to `f ⁻¹(V)` lands in the open subspace `V`. -/
-- Proof sketch: a point of `f ⁻¹(V)` is, by definition, a point of `X` whose image under `f`
-- lies in `V`, so the composite `f^{-1}(V) ⟶ X ⟶ Y` factors through the inclusion `V ↪ Y`.
private theorem restrictedMorphism_range_subset (V : Opens Y.carrier) :
    Set.range
        (((X.ofRestrict ((Opens.map f.hom.base).obj V).isOpenEmbedding) ≫ f).hom.base) ⊆
      Set.range (Y.ofRestrict V.isOpenEmbedding).hom.base := sorry

/-- The restriction `g : f^{-1}(V) ⟶ V` of a morphism of ringed spaces `f : X ⟶ Y` to an open
subspace `V ⊆ Y`. -/
noncomputable def restrictedMorphismToOpen (V : Opens Y.carrier) :
    X.restrict ((Opens.map f.hom.base).obj V).isOpenEmbedding ⟶ Y.restrict V.isOpenEmbedding :=
  InducedCategory.homMk
    (PresheafedSpace.IsOpenImmersion.lift
      (Y.ofRestrict V.isOpenEmbedding).hom
      (((X.ofRestrict ((Opens.map f.hom.base).obj V).isOpenEmbedding) ≫ f).hom)
      (restrictedMorphism_range_subset f V))

/-- The restriction of an `\mathcal O_X`-module to the open subspace `f^{-1}(V)`, transported to
the module category attached to the restricted ringed space. -/
noncomputable def restrictedModuleOnPreimageOpen
    (V : Opens Y.carrier) (ℱ : SheafOfModules ((RingedSpace.ringCatSheaf X))) :
    SheafOfModules
      (RingedSpace.ringCatSheaf (X.restrict ((Opens.map f.hom.base).obj V).isOpenEmbedding)) :=
  Eq.mp
    (congrArg SheafOfModules
      (restrict_ringCatSheaf_eq ((Opens.map f.hom.base).obj V)).symm)
    ((moduleSheafRestrictionToOpen ((Opens.map f.hom.base).obj V)
      ((RingedSpace.ringCatSheaf X))).obj ℱ)

/-- The higher direct image for the restricted morphism `g : f^{-1}(V) ⟶ V`, transported back to
the standard category of modules over the restricted ambient structure sheaf on `V`. -/
noncomputable def restrictedHigherDirectImageOnOpen
    (V : Opens Y.carrier)
    (p : ℕ)
    (ℱ : SheafOfModules ((RingedSpace.ringCatSheaf X)))
    [(RingedSpace.Hom.pushforward (restrictedMorphismToOpen f V)).Additive]
    [HasInjectiveResolutions
      (SheafOfModules
        (RingedSpace.ringCatSheaf (X.restrict ((Opens.map f.hom.base).obj V).isOpenEmbedding)))] :
    SheafOfModules ((TopCat.Sheaf.pullback RingCat.{u} V.inclusion').obj
      ((RingedSpace.ringCatSheaf Y))) :=
  Eq.mp
    (congrArg SheafOfModules
      (restrict_ringCatSheaf_eq V))
    (((RingedSpace.Hom.pushforward (restrictedMorphismToOpen f V)).rightDerived p).obj
      (restrictedModuleOnPreimageOpen f V ℱ))

variable [(RingedSpace.Hom.pushforward f).Additive]
variable [HasInjectiveResolutions (SheafOfModules ((RingedSpace.ringCatSheaf X)))]

/-- Lemma 20.7.4: for `g : f^{-1}(V) ⟶ V` obtained by restricting a morphism of ringed spaces
`f : X ⟶ Y` to an open subset `V ⊆ Y`, the restriction of `R^p f_* \mathcal F` to `V` is
canonically isomorphic to `R^p g_* (\mathcal F|_{f^{-1}(V)})`. -/
-- Proof sketch: apply Lemma `20.7.3` to both `f` and the restricted morphism `g`, and use
-- Lemma `20.7.1` to identify the cohomology groups on opens of `V` with the cohomology groups of
-- the restricted module on the corresponding opens of `f^{-1}(V)`, yielding the required
-- isomorphism class.
theorem ringedSpaceModulePushforward_rightDerived_restrict_isomorphic
    (p : ℕ)
    (ℱ : SheafOfModules ((RingedSpace.ringCatSheaf X)))
    (V : Opens Y.carrier)
    [(RingedSpace.Hom.pushforward (restrictedMorphismToOpen f V)).Additive]
    [HasInjectiveResolutions
      (SheafOfModules
        (RingedSpace.ringCatSheaf (X.restrict ((Opens.map f.hom.base).obj V).isOpenEmbedding)))] :
    IsIsomorphic
      ((moduleSheafRestrictionToOpen V ((RingedSpace.ringCatSheaf Y))).obj
        (((RingedSpace.Hom.pushforward f).rightDerived p).obj ℱ))
      (restrictedHigherDirectImageOnOpen f V p ℱ) := sorry

end AlgebraicGeometry
