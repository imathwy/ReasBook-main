import StacksProject_2024.Chap20.Lemma_20_27_2
import StacksProject_2024.Chap20.Global_sections_module_owners_core
import StacksProject_2024.Chap20.RingedSpaceOpensModuleCategory
import StacksProject_2024.Chap21.Lemma_21_19_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open RingedSite.Hom
open SheafOfModules
open scoped RingedSpace.Hom RingedSpaceDerivedPullback RingedSpaceDerivedPushforward

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X Y Z : RingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
variable [CategoryWithHomology (RingedSpace.Modules X)]
variable [CategoryWithHomology (RingedSpace.Modules Y)]
variable [CategoryWithHomology (RingedSpace.Modules Z)]
variable [(f _*).Additive] [(g _*).Additive]
variable [(f^*).Additive] [(g^*).Additive]
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

local notation "ModX" => RingedSpace.Modules X

/- Domain-style sampling for Lemma 20.28.2:
- primary domain: composition compatibility for derived pushforward on module sheaves over ringed
  spaces;
- sampled owner declarations:
  `modulePullbackCompIso`,
  `DifferentialGradedModule.leftDerivedPullbackCompIso`,
  `RingedSite.Hom.modulePushforwardDerived_compIso`,
  `RingedSite.Hom.modulePushforwardDerived_compIso_hom_app_counit`,
  `opensRingedSiteHom`;
- best owner abstraction: the source-facing owner is the canonical comparison morphism
  `R((f ≫ g))_* ⟶ R(f)_* ⋙ R(g)_*`, viewed as the inverse of the canonical ringed-site
  comparison `modulePushforwardDerived_compIso` specialized along `opensRingedSiteHom`. The
  source statement of Lemma `20.28.2` is then the theorem that this canonical comparison is an
  isomorphism.

Primitive data are only the composable morphisms `f` and `g`; the canonical pullback-composition
isomorphism and the Chapter 21 ringed-site pushforward-composition comparison are already
available owners. The public API should therefore expose the ringed-space bridge to that canonical
comparison together with the source-facing inverse comparison morphism and its objectwise counit
characterization.

Source/core/bridge triage:
- `source-facing`: the canonical comparison morphism `R((f ≫ g))_* ⟶ R(f)_* ⋙ R(g)_*` and the
  statement that it is an isomorphism;
- `core/canonical`: `modulePullbackCompIso`,
  `DifferentialGradedModule.leftDerivedPullbackCompIso`,
  `RingedSite.Hom.modulePushforwardDerived_compIso`, and
  `RingedSite.Hom.modulePushforwardDerived_compIso_hom_app_counit`;
- `bridge/view`: the ringed-space specialization along `opensRingedSiteHom`.
-/

/-- Lemma 20.28.2: for composable morphisms of ringed spaces `f : X ⟶ Y` and `g : Y ⟶ Z`, the
canonical pullback-composition isomorphism specializes the Chapter 21 ringed-site comparison to a
canonical isomorphism from the composite derived pushforward `R(f)_* ⋙ R(g)_*` to the derived
pushforward of the composite `R((f ≫ g))_*`. -/
@[stacks 0D5T]
noncomputable abbrev moduleDerivedPushforward_compIso :
    R(f)_* ⋙ R(g)_* ≅ R((f ≫ g))_* := by
  let f' : opensRingedSite X ⟶ opensRingedSite Y := opensRingedSiteHom f
  let g' : opensRingedSite Y ⟶ opensRingedSite Z := opensRingedSiteHom g
  let fg' : opensRingedSite X ⟶ opensRingedSite Z := opensRingedSiteHom (f ≫ g)
  let hAddCompPush : (modulePushforward fg').Additive := by
    simpa [fg'] using (inferInstance : ((f ≫ g) _*).Additive)
  let hAddCompPull : (SheafOfModules.pullback fg'.structureSheafMap).Additive := by
    simpa [fg'] using (inferInstance : ((f ≫ g)^*).Additive)
  let hLeftDerivedComp :
      Functor.HasLeftDerivedFunctor
        (RingedSite.Hom.modulePullbackToDerived fg')
        (RingedSite.Hom.ModuleQis (opensRingedSite Z)) := by
    simpa [fg'] using
      (inferInstance :
        Functor.HasLeftDerivedFunctor
          (AlgebraicGeometry.RingedSpace.modulePullbackToDerived (f ≫ g))
          (AlgebraicGeometry.RingedSpace.ModuleQis Z))
  simpa [f', g', fg'] using
    (@RingedSite.Hom.modulePushforwardDerived_compIso
      _ _ _ f' g'
      _ _ _ _
      _ _ hAddCompPush
      _ _ _
      _ _ hAddCompPull
      _ _ _
      _ _ hLeftDerivedComp
      (DifferentialGradedModule.leftDerivedPullbackCompIso
        (f^*) (g^*) ((f ≫ g)^*) (modulePullbackCompIso f g)))

/-- Lemma 20.28.2: for composable morphisms of ringed spaces `f : X ⟶ Y` and `g : Y ⟶ Z`, the
canonical comparison morphism from the derived pushforward of the composite morphism to the
composite derived pushforward is the inverse of `moduleDerivedPushforward_compIso f g`. -/
@[stacks 0D5T]
noncomputable abbrev moduleDerivedPushforward_compComparison :
    R((f ≫ g))_* ⟶ R(f)_* ⋙ R(g)_* :=
  (moduleDerivedPushforward_compIso f g).inv

/-- The component of `moduleDerivedPushforward_compIso f g` at `K` identifies the counit of
`L((f ≫ g))^* ⊣ R((f ≫ g))_*` with the counit of the transported composite adjunction obtained
from the Chapter 21 ringed-site comparison. -/
theorem moduleDerivedPushforward_compIso_hom_app_counit
    (K : DerivedCategory ModX) :
    (L((f ≫ g))^*).map ((moduleDerivedPushforward_compIso f g).hom.app K) ≫
        (modulePullbackDerived_pushforward_adjunction
          (opensRingedSiteHom (f ≫ g))).counit.app K =
        (((modulePullbackDerived_pushforward_adjunction (opensRingedSiteHom g)).comp
            (modulePullbackDerived_pushforward_adjunction (opensRingedSiteHom f))).ofNatIsoLeft
          (DifferentialGradedModule.leftDerivedPullbackCompIso
            (f^*) (g^*) ((f ≫ g)^*) (modulePullbackCompIso f g))).counit.app K := by
  let f' : opensRingedSite X ⟶ opensRingedSite Y := opensRingedSiteHom f
  let g' : opensRingedSite Y ⟶ opensRingedSite Z := opensRingedSiteHom g
  let fg' : opensRingedSite X ⟶ opensRingedSite Z := opensRingedSiteHom (f ≫ g)
  let hAddCompPush : (modulePushforward fg').Additive := by
    simpa [fg'] using (inferInstance : ((f ≫ g) _*).Additive)
  let hAddCompPull : (SheafOfModules.pullback fg'.structureSheafMap).Additive := by
    simpa [fg'] using (inferInstance : ((f ≫ g)^*).Additive)
  let hLeftDerivedComp :
      Functor.HasLeftDerivedFunctor
        (RingedSite.Hom.modulePullbackToDerived fg')
        (RingedSite.Hom.ModuleQis (opensRingedSite Z)) := by
    simpa [fg'] using
      (inferInstance :
        Functor.HasLeftDerivedFunctor
          (AlgebraicGeometry.RingedSpace.modulePullbackToDerived (f ≫ g))
          (AlgebraicGeometry.RingedSpace.ModuleQis Z))
  simpa [moduleDerivedPushforward_compIso, f', g', fg'] using
    (@RingedSite.Hom.modulePushforwardDerived_compIso_hom_app_counit
      _ _ _ f' g'
      _ _ _ _
      _ _ hAddCompPush
      _ _ _
      _ _ hAddCompPull
      _ _ _
      _ _ hLeftDerivedComp
      (DifferentialGradedModule.leftDerivedPullbackCompIso
        (f^*) (g^*) ((f ≫ g)^*) (modulePullbackCompIso f g))
      K)

-- Proof sketch: this is the source-facing unbounded analogue of the bounded-below composition
-- comparison of Lemma `20.13.7`; the remaining proof identifies the comparison with the canonical
-- isomorphism obtained from the pullback/pushforward adjunctions.
/-- Lemma 20.28.2, source-facing form: the canonical comparison morphism
`R((f ≫ g))_* ⟶ R(f)_* ⋙ R(g)_*` is an isomorphism. -/
@[stacks 0D5T]
instance moduleDerivedPushforward_compComparison_isIso :
    IsIso (moduleDerivedPushforward_compComparison f g) := by
  infer_instance

/-
The component of the canonical composition comparison on a derived object is an isomorphism.
-/
theorem moduleDerivedPushforward_compComparison_app_isIso
    (K : DerivedCategory ModX) :
    IsIso ((moduleDerivedPushforward_compComparison f g).app K) := by
  infer_instance

end

end AlgebraicGeometry.RingedSpace
