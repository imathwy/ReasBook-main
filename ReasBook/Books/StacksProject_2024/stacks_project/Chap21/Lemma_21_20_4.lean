import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Sites.Over
import StacksProject_2024.Chap13.Lemma_13_14_16
import StacksProject_2024.Chap18.Lemma_18_20_1
import StacksProject_2024.Chap21.Lemma_21_19_1_core
import StacksProject_2024.Chap21.RingedSiteDerivedBasic

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open scoped RingedSiteDerived

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false

namespace RingedSite.Hom

local notation "Mod(" X ")" => ModuleCat X
local notation "DMod(" X ")" => ModuleDerived X

/- Domain-style sampling for Lemma 21.20.4:
- primary domain: localization of ringed sites and compatibility of derived direct image with
  restriction to a localized site;
- sampled owner declarations:
  `RingedSite.Hom.modulePushforward`,
  `RingedSite.Hom.localizedRestriction`,
  `SheafOfModules.pushforwardComp`,
  `CategoryTheory.Functor.mapDerivedCategory`,
  `Functor.totalRightDerived`;
- best owner abstraction:
  `source-facing`: the localized derived pushforward comparison on functors;
  `core/canonical`: `modulePushforwardDerived` together with the existing Chapter 21 owner
    `localizedRestriction`;
  `bridge/view`: the proposition-level functor and objectwise isomorphism statements below.

Primitive vs. derived:
- primitive data: a ringed site `X`, an object `U : X`, and the Chapter 21 owner
  `localizedRestriction X U`;
- derived API: the induced exact derived restriction functor and the source-facing localized
  pushforward comparison on derived functors.
-/

section

variable {X Y : _root_.RingedSite.{u, v}} (f : X ⟶ Y) (V : Y)

variable [HasBinaryProducts X.carrier] [HasBinaryProducts Y.carrier]
variable [CategoryWithHomology (Mod(X))] [CategoryWithHomology (Mod(Y))]
variable [CategoryWithHomology (Mod(X.localization (f.base.obj V)))]
variable [CategoryWithHomology (Mod(Y.localization V))]

variable [f.modulePushforward.Additive]
variable [(f.localization V).modulePushforward.Additive]

variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived f) (ModuleQis X)]
variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived (f.localization V))
  (ModuleQis (X.localization (f.base.obj V)))]

variable [PreservesFiniteLimits (localizedRestriction X (f.base.obj V))]
variable [PreservesFiniteColimits (localizedRestriction X (f.base.obj V))]

variable [PreservesFiniteLimits (localizedRestriction Y V)]
variable [PreservesFiniteColimits (localizedRestriction Y V)]

/-- Helper for Lemma 21.20.4: the common normalized structure-sheaf map is the actual
structure-sheaf map of the localized morphism. -/
private noncomputable def modulePushforward_localizedRestrictionCommonMap :
    (Y.localization V).structureSheaf ⟶
      (((Over.forget V ⋙ f.base).sheafPushforwardContinuous RingCat.{max u v}
          (Y.localization V).siteTopology X.siteTopology).obj X.structureSheaf) := by
  -- Proof comment: the localized morphism already packages the needed slice-site structure-sheaf
  -- map, so we normalize every underived comparison to that canonical owner.
  simpa [RingedSite.Hom.localization_base] using
    (f.localization V).structureSheafMap

/-- Helper for Lemma 21.20.4: the left-hand underived composite already normalizes to the common
pushforward along `Over.forget V ⋙ f.base`. -/
private noncomputable def modulePushforward_localizedRestriction_leftIso :
    pushforward f ⋙ localizedRestriction Y V ≅
      SheafOfModules.pushforward
        (modulePushforward_localizedRestrictionCommonMap (f := f) (V := V)) := by
  -- Proof comment: combine the pushforward along `f.base` with restriction to the slice site on
  -- `V` by the canonical pushforward-composition owner, then rewrite the common map to the
  -- localized structure-sheaf map.
  simpa [RingedSite.Hom.pushforward, RingedSite.Hom.localizedRestriction,
    modulePushforward_localizedRestrictionCommonMap,
    RingedSite.Hom.localization_structureSheafMap_eq] using
    (SheafOfModules.pushforwardComp (𝟙 (Y.structureSheaf.over V)) f.structureSheafMap)

/-- Helper for Lemma 21.20.4: the right-hand underived composite also normalizes to the common
pushforward along `Over.forget V ⋙ f.base`. -/
private noncomputable def modulePushforward_localizedRestriction_rightIso :
    localizedRestriction X (f.base.obj V) ⋙ pushforward (f.localization V) ≅
      SheafOfModules.pushforward
        (modulePushforward_localizedRestrictionCommonMap (f := f) (V := V)) := by
  -- Route correction: after normalizing to `(f.localization V).structureSheafMap`, the right-hand
  -- composite is the direct pushforward-composition owner with no extra transport.
  simpa [RingedSite.Hom.pushforward, RingedSite.Hom.localizedRestriction,
    modulePushforward_localizedRestrictionCommonMap] using
    (SheafOfModules.pushforwardComp
      (f.localization V).structureSheafMap
      (𝟙 (X.structureSheaf.over (f.base.obj V))))

/-- Helper for Lemma 21.20.4: before passing to homotopy or derived categories, localizing after
pushforward agrees with pushing forward after localizing. -/
private noncomputable abbrev modulePushforward_localizedRestrictionIso :
    pushforward f ⋙ localizedRestriction Y V ≅
      localizedRestriction X (f.base.obj V) ⋙ pushforward (f.localization V) :=
  -- Proof comment: both underived composites normalize to the same pushforward along
  -- `Over.forget V ⋙ f.base`, so their comparison is the composite of the two normal forms.
  modulePushforward_localizedRestriction_leftIso (f := f) (V := V) ≪≫
    (modulePushforward_localizedRestriction_rightIso (f := f) (V := V)).symm

/-- Helper for Lemma 21.20.4: on the homotopy-to-derived source functors, localizing after
pushforward agrees with pushing forward after localizing. -/
private noncomputable def modulePushforwardToDerived_localizedRestriction_underivedIso :
    modulePushforwardToDerived f ⋙ localizedRestrictionDerived Y V ≅
      (localizedRestriction X (f.base.obj V)).mapHomotopyCategory (up ℤ) ⋙
        modulePushforwardToDerived (f.localization V) :=
  let pushH := (pushforward f).mapHomotopyCategory (up ℤ)
  let restrictYH := (localizedRestriction Y V).mapHomotopyCategory (up ℤ)
  let restrictXH := (localizedRestriction X (f.base.obj V)).mapHomotopyCategory (up ℤ)
  let pushLocH := (pushforward (f.localization V)).mapHomotopyCategory (up ℤ)
  let QY :
      HomotopyCategory (Mod(Y)) (up ℤ) ⥤ DMod(Y) :=
    DerivedCategory.Qh
  let QV :
      HomotopyCategory (Mod(Y.localization V)) (up ℤ) ⥤
        DMod(Y.localization V) :=
    DerivedCategory.Qh
  let hComp :
      pushH ⋙ restrictYH ≅ restrictXH ⋙ pushLocH :=
    (Functor.mapHomotopyCategoryCompIso
      (pushforward f)
      (localizedRestriction Y V)).symm ≪≫
      Functor.mapHomotopyCategoryIso
        (modulePushforward_localizedRestrictionIso (f := f) (V := V)) ≪≫
      Functor.mapHomotopyCategoryCompIso
        (localizedRestriction X (f.base.obj V))
        (pushforward (f.localization V))
  -- Proof comment: first replace derived localized restriction by its homotopy-level exact model,
  -- then apply the already-proved module-level Beck-Chevalley iso on homotopy categories.
  (Functor.associator pushH QY (localizedRestrictionDerived Y V)).symm ≪≫
    Functor.isoWhiskerLeft pushH (localizedRestriction Y V).mapDerivedCategoryFactorsh ≪≫
    Functor.associator pushH restrictYH QV ≪≫
    Functor.isoWhiskerRight hComp QV ≪≫
    (Functor.associator restrictXH pushLocH QV).symm

/-- Helper for Lemma 21.20.4: exact localized restriction on derived categories is the right
derived functor of homotopy-level localized restriction. -/
private instance localizedRestrictionDerived_isRightDerived
    (Z : _root_.RingedSite.{u, v}) (W : Z)
    [HasBinaryProducts Z.carrier]
    [CategoryWithHomology (Mod(Z))]
    [CategoryWithHomology (Mod(Z.localization W))]
    [PreservesFiniteLimits (localizedRestriction Z W)]
    [PreservesFiniteColimits (localizedRestriction Z W)] :
    (localizedRestrictionDerived Z W).IsRightDerivedFunctor
      ((localizedRestriction Z W).mapDerivedCategoryFactorsh.inv)
      (ModuleQis Z) := by
  -- Proof comment: exact functors already invert quasi-isomorphisms, so the exact derived owner
  -- furnishes its own right-derived witness.
  simpa [localizedRestrictionDerived] using
    (Functor.isRightDerivedFunctor_of_inverts
      (ModuleQis Z)
      (localizedRestrictionDerived Z W)
      (localizedRestriction Z W).mapDerivedCategoryFactorsh)

/-- Helper for Lemma 21.20.4: the left-hand derived composite carries the canonical right-derived
structure obtained by postcomposing `R(f)_*` with exact localized restriction on `Y/V`. -/
private noncomputable def modulePushforwardDerived_localizedRestriction_sourceNat :
    modulePushforwardToDerived f ⋙ localizedRestrictionDerived Y V ⟶
      (show
        HomotopyCategory (Mod(X)) (up ℤ) ⥤ DMod(X)
       from
        DerivedCategory.Qh) ⋙
        (R(f)_* ⋙ localizedRestrictionDerived Y V) :=
  Functor.whiskerRight
      (Functor.totalRightDerivedUnit
        (modulePushforwardToDerived f)
        (show
          HomotopyCategory (Mod(X)) (up ℤ) ⥤ DMod(X)
         from
          DerivedCategory.Qh)
        (ModuleQis X))
      (localizedRestrictionDerived Y V) ≫
    (Functor.associator
      (show
        HomotopyCategory (Mod(X)) (up ℤ) ⥤ DMod(X)
       from
        DerivedCategory.Qh)
      (R(f)_*)
      (localizedRestrictionDerived Y V)).hom

/-- Helper for Lemma 21.20.4: the left-hand theorem side is a right derived functor of the
homotopy-level composite `modulePushforwardToDerived f ⋙ localizedRestrictionDerived Y V`. -/
private instance modulePushforwardDerived_localizedRestriction_source_isRightDerivedFunctor :
    (R(f)_* ⋙ localizedRestrictionDerived Y V).IsRightDerivedFunctor
      (modulePushforwardDerived_localizedRestriction_sourceNat (f := f) (V := V))
      (ModuleQis X) := by
  -- Proof comment: compose the total-right-derived witness for `R(f)_*` with the exact witness for
  -- localized restriction on the target site.
  infer_instance

/-- Helper for Lemma 21.20.4: after normalizing the underived source by the Beck-Chevalley
comparison, the right-hand theorem side receives the canonical right-derived unit. -/
private noncomputable def modulePushforwardDerived_localizedRestriction_targetNat :
    (localizedRestriction X (f.base.obj V)).mapHomotopyCategory (up ℤ) ⋙
        modulePushforwardToDerived (f.localization V) ⟶
      (show
        HomotopyCategory (Mod(X)) (up ℤ) ⥤ DMod(X)
       from
        DerivedCategory.Qh) ⋙
        (localizedRestrictionDerived X (f.base.obj V) ⋙
          R((f.localization V))_*) :=
  Functor.whiskerLeft
      ((localizedRestriction X (f.base.obj V)).mapHomotopyCategory (up ℤ))
      (Functor.totalRightDerivedUnit
        (modulePushforwardToDerived (f.localization V))
        (show
          HomotopyCategory (Mod(X.localization (f.base.obj V))) (up ℤ) ⥤
            DMod(X.localization (f.base.obj V))
         from
          DerivedCategory.Qh)
        (ModuleQis (X.localization (f.base.obj V)))) ≫
    (Functor.associator
      ((localizedRestriction X (f.base.obj V)).mapHomotopyCategory (up ℤ))
      (show
        HomotopyCategory (Mod(X.localization (f.base.obj V))) (up ℤ) ⥤
          DMod(X.localization (f.base.obj V))
       from
        DerivedCategory.Qh)
      (R((f.localization V))_*)).inv ≫
    Functor.whiskerRight
      ((localizedRestriction X (f.base.obj V)).mapDerivedCategoryFactorsh.inv :
        (localizedRestriction X (f.base.obj V)).mapHomotopyCategory (up ℤ) ⋙
            (show
              HomotopyCategory (Mod(X.localization (f.base.obj V))) (up ℤ) ⥤
                DMod(X.localization (f.base.obj V))
             from
              DerivedCategory.Qh) ⟶
          (show
            HomotopyCategory (Mod(X)) (up ℤ) ⥤ DMod(X)
           from
            DerivedCategory.Qh) ⋙
            localizedRestrictionDerived X (f.base.obj V))
      (R((f.localization V))_*) ≫
    (Functor.associator
      (show
        HomotopyCategory (Mod(X)) (up ℤ) ⥤ DMod(X)
       from
        DerivedCategory.Qh)
      (localizedRestrictionDerived X (f.base.obj V))
      (R((f.localization V))_*)).hom

/-- Helper for Lemma 21.20.4: the right-hand theorem side is a right derived functor of the
normalized homotopy-level localized pushforward composite. -/
private instance modulePushforwardDerived_localizedRestriction_target_isRightDerivedFunctor :
    (localizedRestrictionDerived X (f.base.obj V) ⋙ R((f.localization V))_*).IsRightDerivedFunctor
      (modulePushforwardDerived_localizedRestriction_targetNat (f := f) (V := V))
      (ModuleQis X) := by
  -- Proof comment: first derive the localized pushforward on `X/f(V)`, then transport it through
  -- the exact localized restriction on the source.
  infer_instance

/-- Helper for Lemma 21.20.4: the canonical derived Beck-Chevalley comparison is the isomorphism
obtained by applying `Functor.rightDerivedNatIso` to the underived localization isomorphism. -/
private noncomputable abbrev modulePushforwardDerived_localizedRestrictionFunctorIso :
    (R(f)_* ⋙ localizedRestrictionDerived Y V) ≅
      (localizedRestrictionDerived X (f.base.obj V) ⋙ R((f.localization V))_*) :=
  -- Route correction: keep the final comparison in the canonical `Iso` normal form from
  -- `Functor.rightDerivedNatIso` instead of introducing a separate comparison morphism.
  Functor.rightDerivedNatIso
    (R(f)_* ⋙ localizedRestrictionDerived Y V)
    (localizedRestrictionDerived X (f.base.obj V) ⋙ R((f.localization V))_*)
    (modulePushforwardDerived_localizedRestriction_sourceNat (f := f) (V := V))
    (modulePushforwardDerived_localizedRestriction_targetNat (f := f) (V := V))
    (ModuleQis X)
    (modulePushforwardToDerived_localizedRestriction_underivedIso (f := f) (V := V))

/- Lemma 21.20.4, proposition form. -/
@[stacks 0D6G]
theorem modulePushforwardDerived_localizedRestriction_isIsomorphic :
    IsIsomorphic
      (R(f)_* ⋙ localizedRestrictionDerived Y V)
      (localizedRestrictionDerived X (f.base.obj V) ⋙ R((f.localization V))_*) :=
  by
  -- Proof comment: package the canonical derived Beck-Chevalley functor isomorphism directly.
  exact ⟨modulePushforwardDerived_localizedRestrictionFunctorIso (f := f) (V := V)⟩

/- Companion proposition form of the objectwise comparison in Lemma 21.20.4. -/
@[stacks 0D6G]
theorem modulePushforwardDerived_localizedRestriction_app_isIsomorphic
    (E : DMod(X)) :
    IsIsomorphic
      ((R(f)_* ⋙ localizedRestrictionDerived Y V).obj E)
      ((localizedRestrictionDerived X (f.base.obj V) ⋙ R((f.localization V))_*).obj E) := by
  -- Proof comment: specialize the functor-level derived Beck-Chevalley isomorphism to `E`.
  exact
    ⟨(modulePushforwardDerived_localizedRestrictionFunctorIso
        (f := f) (V := V)).app E⟩

/-- Lemma 21.20.4: for a derived `𝒪_X`-module `E`, the localized derived direct image
`(Rf_* E)|_{Y/V}` is represented by the canonical localized pushforward morphism
`Rg_*(E|_{X/f(V)})`. -/
@[stacks 0D6G]
theorem modulePushforwardDerived_localizedRestriction_iso
    (E : DMod(X)) :
    let U := f.base.obj V
    let g := _root_.RingedSite.Hom.localization f V
    ∃ η :
      ((localizedRestrictionDerived Y V).obj ((modulePushforwardDerived f).obj E)) ⟶
        ((modulePushforwardDerived g).obj ((localizedRestrictionDerived X U).obj E)),
      IsIso η := by
  -- Proof comment: unfold the source-facing notation once and reuse the canonical objectwise
  -- comparison isomorphism already constructed above.
  dsimp
  refine
    ⟨((modulePushforwardDerived_localizedRestrictionFunctorIso
        (f := f) (V := V)).app E).hom, ?_⟩
  infer_instance

end

end RingedSite.Hom
