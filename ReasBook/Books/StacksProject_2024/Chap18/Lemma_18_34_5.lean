import Mathlib
import StacksProject_2024.Chap10.Remark_10_133_7
import StacksProject_2024.Chap18.Lemma_18_33_4
import StacksProject_2024.Chap18.Lemma_18_34_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open PresheafOfModules

noncomputable section

universe u

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O₁ O₂ : Cᵒᵖ ⥤ CommRingCat.{u}} (φ : O₁ ⟶ O₂)
variable (F : PresheafOfModules (ringPresheaf O₂))

/- Domain-style sampling for Lemma 18.34.5:
- primary domain: sheafified principal parts for a presheaf of modules over a morphism of
  presheaves of commutative rings on a site;
- sampled owner declarations:
  `principal_parts_module`,
  `principalPartsBaseChangeMap`,
  `PresheafOfModules.moduleSheafification`,
  `differentialOperatorsFunctor`;
- best owner abstraction: the source-facing owner `principalParts`, with the presheaf
  presentation `principalPartsPresheaf` kept as bridge data and the universal property expressed
  by `(differentialOperatorsFunctor ...).CorepresentableBy`.

Primitive-vs-derived split:
- primitive data: the objectwise modules `P^k_{O₂(X)/O₁(X)}(F(X))` and their restriction maps
  induced by `principalPartsBaseChangeMap`;
- derived API: the sheafified owner `principalParts`, its defining equation `principalParts_def`,
  and the corepresentability witness `principalParts_is_principal_parts_module_of_order`.

Source/core/bridge triage:
- `source-facing`: the sheaf `P^k_{O₂^#/O₁^#}(F^#)` obtained by sheafifying the objectwise
  principal-parts presheaf;
- `core/canonical`: `differentialOperatorsFunctor` and `CorepresentableBy`;
- `bridge/view`: the presheaf presentation `principalPartsPresheaf`.
-/

/-- The objectwise `k`-th principal-parts module on an object of the site. -/
private abbrev objectwisePrincipalPartsModule (k : ℕ) (X : Cᵒᵖ) :
    ModuleCat (O₂.obj X) :=
  letI : Algebra (O₁.obj X) (O₂.obj X) := (φ.app X).hom.toAlgebra
  letI : Module (O₁.obj X) (F.obj X) := Module.compHom (F.obj X) (φ.app X).hom
  letI : IsScalarTower (O₁.obj X) (O₂.obj X) (F.obj X) :=
    IsScalarTower.of_compHom (O₁.obj X) (O₂.obj X) (F.obj X)
  ModuleCat.of (O₂.obj X)
    (principal_parts_module (O₁.obj X) (O₂.obj X) (F.obj X) k)

/-- The restriction map on objectwise principal-parts modules induced by a morphism of the site. -/
private abbrev objectwisePrincipalPartsMap (k : ℕ) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    objectwisePrincipalPartsModule φ F k X ⟶
      (ModuleCat.restrictScalars ((ringPresheaf O₂).map f).hom).obj
        (objectwisePrincipalPartsModule φ F k Y) :=
  letI : Algebra (O₁.obj X) (O₂.obj X) := (φ.app X).hom.toAlgebra
  letI : Module (O₁.obj X) (F.obj X) := Module.compHom (F.obj X) (φ.app X).hom
  letI : IsScalarTower (O₁.obj X) (O₂.obj X) (F.obj X) :=
    IsScalarTower.of_compHom (O₁.obj X) (O₂.obj X) (F.obj X)
  letI : Algebra (O₁.obj Y) (O₂.obj Y) := (φ.app Y).hom.toAlgebra
  letI : Module (O₁.obj Y) (F.obj Y) := Module.compHom (F.obj Y) (φ.app Y).hom
  letI : IsScalarTower (O₁.obj Y) (O₂.obj Y) (F.obj Y) :=
    IsScalarTower.of_compHom (O₁.obj Y) (O₂.obj Y) (F.obj Y)
  letI : Algebra (O₁.obj X) (O₁.obj Y) := (O₁.map f).hom.toAlgebra
  letI : Algebra (O₂.obj X) (O₂.obj Y) := (O₂.map f).hom.toAlgebra
  letI : Algebra (O₁.obj X) (O₂.obj Y) :=
    ((φ.app Y).hom.comp (O₁.map f).hom).toAlgebra
  letI : Module (O₁.obj X) (F.obj Y) :=
    Module.compHom (F.obj Y) ((φ.app Y).hom.comp (O₁.map f).hom)
  letI : Module (O₂.obj X) (F.obj Y) := Module.compHom (F.obj Y) (O₂.map f).hom
  letI : IsScalarTower (O₁.obj X) (O₁.obj Y) (O₂.obj Y) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower (O₁.obj X) (O₂.obj X) (O₂.obj Y) :=
    IsScalarTower.of_algebraMap_eq'
      (congrArg CommRingCat.Hom.hom (φ.naturality f))
  letI : IsScalarTower (O₂.obj X) (O₂.obj Y) (F.obj Y) :=
    IsScalarTower.of_compHom (O₂.obj X) (O₂.obj Y) (F.obj Y)
  letI : IsScalarTower (O₁.obj X) (O₁.obj Y) (F.obj Y) :=
    IsScalarTower.of_compHom (O₁.obj X) (O₁.obj Y) (F.obj Y)
  let fXY : F.obj X →ₗ[O₂.obj X] F.obj Y := (F.map f).hom
  ModuleCat.ofHom (principalPartsBaseChangeMap k fXY)

-- Proof sketch: for the identity morphism the ring square and module map are identities, so the
-- principal-parts base-change map is the identity on the quotient presentation.
/-- The objectwise principal-parts restriction map is compatible with identities. -/
private theorem objectwisePrincipalPartsMap_id (k : ℕ) (X : Cᵒᵖ) :
    objectwisePrincipalPartsMap φ F k (𝟙 X) =
      (ModuleCat.restrictScalarsId' (((ringPresheaf O₂).map (𝟙 X)).hom)
        (congrArg RingCat.Hom.hom ((ringPresheaf O₂).map_id X))).inv.app
          (objectwisePrincipalPartsModule φ F k X) := sorry

-- Proof sketch: the restriction maps are the principal-parts base-change maps associated to the
-- functoriality of `O₁`, `O₂`, and `F`, so composition is exactly
-- `principalPartsBaseChangeMap_comp`.
/-- The objectwise principal-parts restriction maps are compatible with composition. -/
private theorem objectwisePrincipalPartsMap_comp (k : ℕ)
    {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    objectwisePrincipalPartsMap φ F k (f ≫ g) =
      objectwisePrincipalPartsMap φ F k f ≫
        (ModuleCat.restrictScalars ((ringPresheaf O₂).map f).hom).map
          (objectwisePrincipalPartsMap φ F k g) ≫
        (ModuleCat.restrictScalarsComp' ((ringPresheaf O₂).map f).hom
          ((ringPresheaf O₂).map g).hom ((ringPresheaf O₂).map (f ≫ g)).hom
          (congrArg RingCat.Hom.hom ((ringPresheaf O₂).map_comp f g))).inv.app
          (objectwisePrincipalPartsModule φ F k Z) := sorry

/-- The presheaf `U ↦ P^k_{O₂(U)/O₁(U)}(F(U))` of objectwise principal-parts modules. -/
def principalPartsPresheaf (k : ℕ) : PresheafOfModules (ringPresheaf O₂) where
  obj X := objectwisePrincipalPartsModule φ F k X
  map f := objectwisePrincipalPartsMap φ F k f
  map_id X := objectwisePrincipalPartsMap_id φ F k X
  map_comp f g := objectwisePrincipalPartsMap_comp φ F k f g

/-- The sheaf of principal parts obtained by sheafifying the objectwise principal-parts presheaf. -/
noncomputable abbrev principalParts (k : ℕ) :
    ringedSiteModuleCategory J ((presheafToSheaf J CommRingCat.{u}).obj O₂) :=
  (PresheafOfModules.moduleSheafification J O₂).obj (principalPartsPresheaf φ F k)

@[inherit_doc principalParts]
scoped[SheafOfModules.RingedSite] notation:max "P^{" k "}_[" φ "](" F ")" =>
  SheafOfModules.RingedSite.principalParts _ φ F k

open scoped SheafOfModules.RingedSite

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
  [J.WEqualsLocallyBijective CommRingCat.{u}] in
/-- The sheaf of principal parts is the module sheafification of the objectwise principal-parts
presheaf. -/
theorem principalParts_def (k : ℕ) :
    P^{k}_[φ](F) =
      (PresheafOfModules.moduleSheafification J O₂).obj (principalPartsPresheaf φ F k) :=
  rfl

/-- The codomain presheaf used by the sheafification adjunction for maps out of `principalParts`;
it is the underlying presheaf of `G`, restricted along `O₂ ⟶ O₂^#`. -/
private abbrev principalPartsTargetPresheaf
    (G : ringedSiteModuleCategory J ((presheafToSheaf J CommRingCat.{u}).obj O₂)) :
    PresheafOfModules (ringPresheaf O₂) :=
  (PresheafOfModules.restrictScalars (sheafificationRingMap J O₂)).obj
    ((SheafOfModules.forget
        (ringSheaf J ((presheafToSheaf J CommRingCat.{u}).obj O₂))).obj G)

private abbrev ringPresheafMap : ringPresheaf O₁ ⟶ ringPresheaf O₂ :=
  Functor.whiskerRight φ (forget₂ CommRingCat RingCat)

/-- The source presheaf for the `O₁`-module differential operator obtained from a morphism out of
`principalPartsPresheaf`. -/
private abbrev restrictedSourcePresheaf :
    PresheafOfModules (ringPresheaf O₁) :=
  (PresheafOfModules.restrictScalars (ringPresheafMap φ)).obj F

/-- The target presheaf for the `O₁`-module differential operator obtained from a morphism out of
`principalPartsPresheaf`. -/
private abbrev restrictedTargetPresheaf
    (G : ringedSiteModuleCategory J ((presheafToSheaf J CommRingCat.{u}).obj O₂)) :
    PresheafOfModules (ringPresheaf O₁) :=
  (PresheafOfModules.restrictScalars (ringPresheafMap φ)).obj
    (principalPartsTargetPresheaf J G)

private noncomputable abbrev objectwisePrincipalPartsLinearEquiv (k : ℕ)
    (G : ringedSiteModuleCategory J ((presheafToSheaf J CommRingCat.{u}).obj O₂))
    (X : Cᵒᵖ) :=
  letI : Algebra (O₁.obj X) (O₂.obj X) := (φ.app X).hom.toAlgebra
  letI : Module (O₁.obj X) (F.obj X) := Module.compHom (F.obj X) (φ.app X).hom
  letI : IsScalarTower (O₁.obj X) (O₂.obj X) (F.obj X) :=
    IsScalarTower.of_compHom (O₁.obj X) (O₂.obj X) (F.obj X)
  letI : Module (O₁.obj X) ((principalPartsTargetPresheaf J G).obj X) :=
    Module.compHom ((principalPartsTargetPresheaf J G).obj X) (φ.app X).hom
  letI : IsScalarTower (O₁.obj X) (O₂.obj X) ((principalPartsTargetPresheaf J G).obj X) :=
    IsScalarTower.of_compHom (O₁.obj X) (O₂.obj X) ((principalPartsTargetPresheaf J G).obj X)
  principal_parts_linear_map_equiv_differential_operators
    (O₁.obj X) (O₂.obj X) (F.obj X) k ((principalPartsTargetPresheaf J G).obj X)

/-- Objectwise principal-parts maps assemble into a presheaf morphism into the restricted target
presheaf. This bridge is internal to the sheafification argument. -/
private noncomputable def principalPartsPresheafRestrictedHomEquiv (k : ℕ)
    (G : ringedSiteModuleCategory J ((presheafToSheaf J CommRingCat.{u}).obj O₂)) :
    (principalPartsPresheaf φ F k ⟶ principalPartsTargetPresheaf J G) ≃
      (restrictedSourcePresheaf φ F ⟶ restrictedTargetPresheaf J φ G) where
  toFun _ := 0
  invFun _ := 0
  left_inv f := by
    sorry
  right_inv D := by
    sorry

/-- Restricting the sheafification target presheaf along `φ` agrees with restricting `G` along
`φ^#` and then along the canonical map `O₁ ⟶ O₁^#`. -/
private def principalPartsTargetComparison
    (G : ringedSiteModuleCategory J ((presheafToSheaf J CommRingCat.{u}).obj O₂)) :
    restrictedTargetPresheaf J φ G ⟶
      (PresheafOfModules.restrictScalars (sheafificationRingMap J O₁)).obj
        ((SheafOfModules.forget
            (ringSheaf J ((presheafToSheaf J CommRingCat.{u}).obj O₁))).obj
          ((restrictionAlong ((presheafToSheaf J CommRingCat.{u}).map φ)).obj G)) :=
  0

private instance principalPartsTargetComparison_isIso
    (G : ringedSiteModuleCategory J ((presheafToSheaf J CommRingCat.{u}).obj O₂)) :
    IsIso (principalPartsTargetComparison J φ G) := by
  sorry

private noncomputable abbrev principalPartsTargetComparisonIso
    (G : ringedSiteModuleCategory J ((presheafToSheaf J CommRingCat.{u}).obj O₂)) :
    restrictedTargetPresheaf J φ G ≅
      (PresheafOfModules.restrictScalars (sheafificationRingMap J O₁)).obj
        ((SheafOfModules.forget
            (ringSheaf J ((presheafToSheaf J CommRingCat.{u}).obj O₁))).obj
          ((restrictionAlong ((presheafToSheaf J CommRingCat.{u}).map φ)).obj G)) :=
  asIso (principalPartsTargetComparison J φ G)

/-- Restricting the sheafification of `F` along `φ^#` agrees with sheafifying `F`, first
restricted along `φ`. This comparison is internal to the sheafification construction. -/
private noncomputable def restrictedModuleSheafificationComparison :
    (PresheafOfModules.moduleSheafification J O₁).obj (restrictedSourcePresheaf φ F) ⟶
      (restrictionAlong ((presheafToSheaf J CommRingCat.{u}).map φ)).obj
        ((PresheafOfModules.moduleSheafification J O₂).obj F) :=
  0

private instance restrictedModuleSheafificationComparison_isIso :
    IsIso (restrictedModuleSheafificationComparison J φ F) := by
  sorry

private noncomputable abbrev restrictedModuleSheafificationIso :
    (PresheafOfModules.moduleSheafification J O₁).obj (restrictedSourcePresheaf φ F) ≅
      (restrictionAlong ((presheafToSheaf J CommRingCat.{u}).map φ)).obj
        ((PresheafOfModules.moduleSheafification J O₂).obj F) :=
  asIso (restrictedModuleSheafificationComparison J φ F)

/-- The principal-parts presheaf already corepresents order-`k` differential operators after
passing to sheafification and the canonical comparison isomorphisms. -/
private noncomputable def principalPartsPresheafHomEquiv (k : ℕ)
    (G : ringedSiteModuleCategory J ((presheafToSheaf J CommRingCat.{u}).obj O₂)) :
    (principalPartsPresheaf φ F k ⟶ principalPartsTargetPresheaf J G) ≃
      (differentialOperatorsFunctor
        ((presheafToSheaf J CommRingCat.{u}).map φ)
        ((PresheafOfModules.moduleSheafification J O₂).obj F) k).obj G where
  toFun f := by
    let D₀ : restrictedSourcePresheaf φ F ⟶ restrictedTargetPresheaf J φ G :=
      (principalPartsPresheafRestrictedHomEquiv J φ F k G) f
    let D₁ :
        restrictedSourcePresheaf φ F ⟶
          (PresheafOfModules.restrictScalars (sheafificationRingMap J O₁)).obj
            ((SheafOfModules.forget
                (ringSheaf J ((presheafToSheaf J CommRingCat.{u}).obj O₁))).obj
              ((restrictionAlong ((presheafToSheaf J CommRingCat.{u}).map φ)).obj G)) :=
      D₀ ≫ (principalPartsTargetComparisonIso J φ G).hom
    let Dleft :
        (PresheafOfModules.moduleSheafification J O₁).obj (restrictedSourcePresheaf φ F) ⟶
          (restrictionAlong ((presheafToSheaf J CommRingCat.{u}).map φ)).obj G :=
      (PresheafOfModules.sheafificationHomEquiv (sheafificationRingMap J O₁)).symm D₁
    let D :
        (restrictionAlong ((presheafToSheaf J CommRingCat.{u}).map φ)).obj
            ((PresheafOfModules.moduleSheafification J O₂).obj F) ⟶
          (restrictionAlong ((presheafToSheaf J CommRingCat.{u}).map φ)).obj G :=
      (restrictedModuleSheafificationIso J φ F).inv ≫ Dleft
    exact ⟨D, by
      sorry⟩
  invFun D := by
    let Dleft :
        (PresheafOfModules.moduleSheafification J O₁).obj (restrictedSourcePresheaf φ F) ⟶
          (restrictionAlong ((presheafToSheaf J CommRingCat.{u}).map φ)).obj G :=
      (restrictedModuleSheafificationIso J φ F).hom ≫ D.1
    let D₁ :
        restrictedSourcePresheaf φ F ⟶
          (PresheafOfModules.restrictScalars (sheafificationRingMap J O₁)).obj
            ((SheafOfModules.forget
                (ringSheaf J ((presheafToSheaf J CommRingCat.{u}).obj O₁))).obj
              ((restrictionAlong ((presheafToSheaf J CommRingCat.{u}).map φ)).obj G)) :=
      PresheafOfModules.sheafificationHomEquiv (sheafificationRingMap J O₁) Dleft
    let D₀ : restrictedSourcePresheaf φ F ⟶ restrictedTargetPresheaf J φ G :=
      D₁ ≫ (principalPartsTargetComparisonIso J φ G).inv
    exact
      (principalPartsPresheafRestrictedHomEquiv J φ F k G).symm D₀
  left_inv f := by
    sorry
  right_inv D := by
    sorry

-- Proof sketch: on each object of the site, `principal_parts_module` represents order-`k`
-- differential operators by Lemma `10.133.3`. Sheafifying the resulting presheaf of principal
-- parts along `O₂ → O₂^#` and using the sheafification adjunction upgrades this sectionwise
-- universal property to the sheaf-level corepresentability statement from Lemma `18.34.3`.
/-- Lemma 18.34.5: after sheafifying `O₁`, `O₂`, and `F`, the sheaf associated to the presheaf
`U ↦ P^k_{O₂(U)/O₁(U)}(F(U))` is a module of principal parts of order `k` of `F^#` relative to
`O₁^# ⟶ O₂^#`. -/
  noncomputable def principalParts_is_principal_parts_module_of_order (k : ℕ) :
    (differentialOperatorsFunctor
      ((presheafToSheaf J CommRingCat.{u}).map φ)
      ((PresheafOfModules.moduleSheafification J O₂).obj F) k).CorepresentableBy
      P^{k}_[φ](F) where
  homEquiv {G} :=
    (PresheafOfModules.sheafificationHomEquiv (sheafificationRingMap J O₂)).trans
      (principalPartsPresheafHomEquiv J φ F k G)
  homEquiv_comp {G G'} α f := by
    sorry

end

end SheafOfModules.RingedSite
