import StacksProject_2024.Chap13.Definition_13_15_3
import StacksProject_2024.Chap18.Definition_18_21_2
import StacksProject_2024.Chap21.Definition_21_13_4
import StacksProject_2024.Chap21.Lemma_21_20_5_core
import StacksProject_2024.Chap21.Lemma_21_20_7_core

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Sheaf
open Opposite
open ComplexShape
open scoped RingedSite.Hom

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace RingedSite.Hom

/-- The additive sections functor `Γ(K, -)` on `𝒪_X`-modules, defined by restricting
to the localization of `X` at `K` and then taking global sections there. -/
abbrev moduleSectionsOverSheafAdditiveFunctor (X : RingedSite.{max u v, v})
    (K : Sheaf X.siteTopology (Type v))
    [HasWeakSheafify (RingedSite.localizationAtSheaf X.structureSheaf K).siteTopology
      AddCommGrpCat.{max u v}]
    [HasGlobalSectionsFunctor (RingedSite.localizationAtSheaf X.structureSheaf K).siteTopology
      AddCommGrpCat.{max u v}] :
    ModuleCat X ⥤ AddCommGrpCat.{max u v} :=
  SheafOfModules.pushforward
      (𝟙 ((RingedSite.localizationAtSheaf X.structureSheaf K).structureSheaf)) ⋙
    moduleGlobalSectionsAdditiveFunctor (RingedSite.localizationAtSheaf X.structureSheaf K)

instance moduleSectionsOverSheafAdditiveFunctor_additive (X : RingedSite.{max u v, v})
    (K : Sheaf X.siteTopology (Type v))
    [HasWeakSheafify (RingedSite.localizationAtSheaf X.structureSheaf K).siteTopology
      AddCommGrpCat.{max u v}]
    [HasGlobalSectionsFunctor (RingedSite.localizationAtSheaf X.structureSheaf K).siteTopology
      AddCommGrpCat.{max u v}] :
    (moduleSectionsOverSheafAdditiveFunctor X K).Additive := by
  let XK := RingedSite.localizationAtSheaf X.structureSheaf K
  let F : ModuleCat X ⥤ ModuleCat XK :=
    SheafOfModules.pushforward (𝟙 XK.structureSheaf)
  let G := moduleGlobalSectionsAdditiveFunctor XK
  letI : F.Additive := by
    refine ⟨?_⟩
    intro M N f g
    ext U x
    rfl
  letI : G.Additive := moduleGlobalSectionsAdditiveFunctor_additive XK
  refine ⟨?_⟩
  intro M N f g
  change G.map (F.map (f + g)) = G.map (F.map f) + G.map (F.map g)
  rw [F.map_add, G.map_add]

/-- The homotopy-to-derived functor induced by sections over a sheaf of sets `K`. -/
abbrev moduleSectionsOverSheafToDerived (X : RingedSite.{max u v, v})
    (K : Sheaf X.siteTopology (Type v))
    [HasWeakSheafify (RingedSite.localizationAtSheaf X.structureSheaf K).siteTopology
      AddCommGrpCat.{max u v}]
    [HasGlobalSectionsFunctor (RingedSite.localizationAtSheaf X.structureSheaf K).siteTopology
      AddCommGrpCat.{max u v}] :
    HomotopyCategory (ModuleCat X) (up ℤ) ⥤ DerivedCategory AddCommGrpCat.{max u v} :=
  mapHomotopyCategoryToDerived (moduleSectionsOverSheafAdditiveFunctor X K)

end RingedSite.Hom

namespace CategoryTheory

open RingedSite.Hom

/- Domain-style sampling for Lemma 21.14.3:
- primary domain: right-acyclicity of sections and direct-image functors for sheaves of modules on
  a ringed site, expressed through the derived owner
  `IsRightAcyclicForAdditiveFunctor`;
- sampled owner declarations:
  `IsRightAcyclicForAdditiveFunctor`,
  `Sheaf.IsTotallyAcyclicOne`,
  `RingedSite.Hom.moduleSectionsOverSheafAdditiveFunctor`,
  `RingedSite.Hom.moduleSectionsOverSheafToDerived`,
  `SheafOfModules.evaluation`,
  `RingedSite.Hom.modulePushforward`;
- best owner abstraction:
  `source-facing`: the four Stacks acyclicity assertions for sections over a sheaf of sets, over an
    object, for global sections, and for direct image;
  `core/canonical`: `IsRightAcyclicForAdditiveFunctor`, `Sheaf.IsTotallyAcyclicOne`,
    `RingedSite.Hom.moduleSectionsOverSheafAdditiveFunctor`,
    `RingedSite.Hom.moduleSectionsOverSheafToDerived`, `SheafOfModules.evaluation`, and
    `RingedSite.Hom.modulePushforward`;
  `bridge/view`: the canonical localized restriction functor
    `SheafOfModules.pushforward
      (𝟙 ((RingedSite.localizationAtSheaf X.structureSheaf K).structureSheaf))`, and
    forgetting the natural `𝒪(U)`-module structure on
    `SheafOfModules.evaluation X.structureSheaf (op U)` to the source-facing
    `AddCommGrpCat`-valued sections functor.

Primitive data versus derived API:
- primitive data: a ringed site `X`, a sheaf of sets `K` or object `U`, a module sheaf `ℱ`, and
  total acyclicity of the underlying abelian sheaf;
- derived API: the corresponding right-acyclicity statements for localized sections, objectwise
  sections, global sections, and direct image.
-/

section

variable (X : RingedSite.{max u v, v})
variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
variable [HasSheafify X.siteTopology AddCommGrpCat.{max u v}]
variable [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [HasExt (Sheaf X.siteTopology AddCommGrpCat.{max u v})]

-- Proof sketch: identify the higher right-derived functors of sections over `K` with the positive
-- cohomology groups `H^p(K, (SheafOfModules.toSheaf X.structureSheaf).obj ℱ)`, and then apply the
-- defining vanishing built into `IsTotallyAcyclicOne`.
/-- Lemma 21.14.3: if the underlying abelian sheaf of an `𝒪`-module sheaf on a
ringed topos presentation `X` is totally acyclic, then the module sheaf is right acyclic for the
sections functor over any sheaf of sets `K` on `X`. -/
@[stacks 0731]
instance totallyAcyclicModule_isRightAcyclicForSectionsOnSheaf
    (K : Sheaf X.siteTopology (Type v))
    [HasWeakSheafify (RingedSite.localizationAtSheaf X.structureSheaf K).siteTopology
      AddCommGrpCat.{max u v}]
    [HasSheafify (RingedSite.localizationAtSheaf X.structureSheaf K).siteTopology
      AddCommGrpCat.{max u v}]
    [HasGlobalSectionsFunctor (RingedSite.localizationAtSheaf X.structureSheaf K).siteTopology
      AddCommGrpCat.{max u v}]
    [HasExt
      (Sheaf (RingedSite.localizationAtSheaf X.structureSheaf K).siteTopology
        AddCommGrpCat.{max u v})]
    [Functor.HasRightDerivedFunctor (moduleSectionsOverSheafToDerived X K) (ModuleQis X)]
    (ℱ : SheafOfModules X.structureSheaf)
    [IsTotallyAcyclicOne ((SheafOfModules.toSheaf X.structureSheaf).obj ℱ)] :
    IsRightAcyclicForAdditiveFunctor (moduleSectionsOverSheafAdditiveFunctor X K) ℱ := sorry

-- Proof sketch: the higher right-derived functors of sections over `U` compute the groups
-- `H^p(U, (SheafOfModules.toSheaf X.structureSheaf).obj ℱ)`, so total acyclicity forces them to
-- vanish in positive degree.
/-- A totally acyclic `𝒪`-module sheaf on a ringed topos presentation `X` is right
acyclic for the functor `H^0(U, -)` for every object `U` of the underlying site. -/
instance totallyAcyclicModule_isRightAcyclicForSectionsOverObject
    (U : X) (ℱ : SheafOfModules X.structureSheaf)
    [Functor.HasRightDerivedFunctor (moduleSectionsAsAbelianToDerived X U) (ModuleQis X)]
    [IsTotallyAcyclicOne ((SheafOfModules.toSheaf X.structureSheaf).obj ℱ)] :
    IsRightAcyclicForAdditiveFunctor (moduleSectionsAsAbelianFunctor X U) ℱ := sorry

-- Proof sketch: the right-derived functors of
-- `SheafOfModules.toSheaf X.structureSheaf ⋙ Sheaf.Γ X.siteTopology AddCommGrpCat`
-- compute global sheaf cohomology of the underlying abelian sheaf, so total acyclicity forces the
-- positive degrees to vanish.
/-- A totally acyclic `𝒪`-module sheaf on `X` is right acyclic for global sections on the
underlying topos. -/
instance totallyAcyclicModule_isRightAcyclicForGlobalSections
    [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{max u v}]
    [Functor.HasRightDerivedFunctor (moduleGlobalSectionsToDerived X) (ModuleQis X)]
    (ℱ : SheafOfModules X.structureSheaf)
    [IsTotallyAcyclicOne ((SheafOfModules.toSheaf X.structureSheaf).obj ℱ)] :
    IsRightAcyclicForAdditiveFunctor (moduleGlobalSectionsAdditiveFunctor X) ℱ :=
  sorry

end

section

variable {X Y : RingedSite.{u, v}} (f : X ⟶ Y)
variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
variable [HasSheafify X.siteTopology AddCommGrpCat.{max u v}]
variable [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [HasExt (Sheaf X.siteTopology AddCommGrpCat.{max u v})]

-- Proof sketch: by Lemma `18.7.2`, any morphism of ringed topoi may be presented by a morphism
-- of sites, and in that setting the higher direct images are computed by sectionwise cohomology.
-- Total acyclicity kills those positive cohomology groups, so the positive right-derived
-- pushforwards vanish.
/-- For a morphism of ringed topoi, formalized here by a morphism of ringed sites `f`, a totally
acyclic `𝒪_X`-module sheaf is right acyclic for direct image. -/
instance totallyAcyclicModule_isRightAcyclicForPushforward
    (ℱ : SheafOfModules X.structureSheaf)
    [IsTotallyAcyclicOne ((SheafOfModules.toSheaf X.structureSheaf).obj ℱ)]
    [f.modulePushforward.Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)] :
    IsRightAcyclicForAdditiveFunctor f.modulePushforward ℱ := sorry

end

end CategoryTheory
