import Mathlib
import stacks_project.Chap10.Remark_10_133_7
import stacks_project.Chap17.Definition_17_28_3
import stacks_project.Chap17.Definition_17_29_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace

noncomputable section

universe u

namespace TopCat.Sheaf

/- Domain-style sampling for Lemma 17.29.5:
- primary domain: sheafified principal parts of modules over a morphism of sheaves of commutative
  rings on a topological space;
- sampled owner declarations:
  `principal_parts_module`,
  `principalPartsBaseChangeMap`,
  `PresheafOfModules.DifferentialsConstruction.relativeDifferentials'`,
  `TopCat.Sheaf.relativeDifferentials`,
  `CategoryTheory.Functor.CorepresentableBy`;
- best owner abstraction: the source-facing sheafified owner `principalParts`, with
  `principalPartsPresheaf` as its presheaf-level bridge presentation;
- primitive data: the objectwise principal-parts module and its restriction maps assembling into
  `principalPartsPresheaf`;
- derived API: the sheafified owner `principalParts`, its defining equation `principalParts_def`,
  and the corepresentability theorem
  `principalParts_is_principal_parts_module_of_order`.

Source/core/bridge triage:
- `core/canonical`: the sectionwise algebraic owner `principal_parts_module` and its base-change
  map `principalPartsBaseChangeMap`;
- `source-facing`: the sheafified owner `principalParts`;
- `bridge/view`: the presheaf presentation `principalPartsPresheaf` and the defining equation
  `principalParts_def`.
-/

section

variable {X : TopCat.{u}}
variable {𝒪₁ 𝒪₂ : TopCat.Sheaf CommRingCat.{u} X}

/-- The morphism `𝒪₁(U) → 𝒪₂(U)` on an open set, viewed as an algebra structure. -/
private abbrev sectionAlgebra (varphi : 𝒪₁ ⟶ 𝒪₂) (U : (Opens X)ᵒᵖ) :
    Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) :=
  RingHom.toAlgebra (varphi.hom.app U).hom

/-- The `𝒪₂(U)`-module of sections of `ℱ` on `U`, restricted along `𝒪₁(U) → 𝒪₂(U)`. -/
private abbrev sectionModule (varphi : 𝒪₁ ⟶ 𝒪₂) (ℱ : SheafOfModules (ringSheaf 𝒪₂))
    (U : (Opens X)ᵒᵖ) : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) :=
  Module.compHom (ℱ.val.obj U) (((ringSheafMap varphi).hom.app U).hom)

/-- The objectwise `k`-th principal-parts module on an open set. -/
private abbrev objectwisePrincipalPartsModule (varphi : 𝒪₁ ⟶ 𝒪₂)
    (ℱ : SheafOfModules (ringSheaf 𝒪₂)) (k : ℕ) (U : (Opens X)ᵒᵖ) :
    ModuleCat ((ringSheaf 𝒪₂).obj.obj U) :=
  letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := sectionAlgebra varphi U
  letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) :=
    IsScalarTower.of_compHom (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U)
  show ModuleCat ((ringSheaf 𝒪₂).obj.obj U) from
    ModuleCat.of (𝒪₂.obj.obj U)
      (principal_parts_module (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) k)

private theorem restrictionRing_isScalarTower_right {U V : (Opens X)ᵒᵖ}
    (varphi : 𝒪₁ ⟶ 𝒪₂) (i : U ⟶ V) :
    letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := RingHom.toAlgebra (varphi.hom.app U).hom
    letI : Algebra (𝒪₂.obj.obj U) (𝒪₂.obj.obj V) := RingHom.toAlgebra (𝒪₂.obj.map i).hom
    letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj V) :=
      RingHom.toAlgebra (((varphi.hom.app V).hom).comp ((𝒪₁.obj.map i).hom))
    IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (𝒪₂.obj.obj V) := by
  sorry

private theorem restrictionModule_isScalarTower_right {U V : (Opens X)ᵒᵖ}
    (ℱ : SheafOfModules (ringSheaf 𝒪₂)) (i : U ⟶ V) :
    letI : Algebra (𝒪₂.obj.obj U) (𝒪₂.obj.obj V) := RingHom.toAlgebra (𝒪₂.obj.map i).hom
    letI : Module (𝒪₂.obj.obj U) (ℱ.val.obj V) := Module.compHom (ℱ.val.obj V) ((𝒪₂.obj.map i).hom)
    IsScalarTower (𝒪₂.obj.obj U) (𝒪₂.obj.obj V) (ℱ.val.obj V) := by
  letI : Algebra (𝒪₂.obj.obj U) (𝒪₂.obj.obj V) := RingHom.toAlgebra (𝒪₂.obj.map i).hom
  letI : Module (𝒪₂.obj.obj U) (ℱ.val.obj V) := Module.compHom (ℱ.val.obj V) ((𝒪₂.obj.map i).hom)
  exact IsScalarTower.of_compHom (𝒪₂.obj.obj U) (𝒪₂.obj.obj V) (ℱ.val.obj V)

/-- The restriction map on objectwise principal-parts modules. -/
private abbrev objectwisePrincipalPartsRestriction (varphi : 𝒪₁ ⟶ 𝒪₂)
    (ℱ : SheafOfModules (ringSheaf 𝒪₂)) (k : ℕ) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    objectwisePrincipalPartsModule varphi ℱ k U ⟶
      (ModuleCat.restrictScalars ((ringSheaf 𝒪₂).obj.map i).hom).obj
        (objectwisePrincipalPartsModule varphi ℱ k V) :=
  letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := sectionAlgebra varphi U
  letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) :=
    IsScalarTower.of_compHom (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U)
  letI : Algebra (𝒪₁.obj.obj V) (𝒪₂.obj.obj V) := sectionAlgebra varphi V
  letI : Module (𝒪₁.obj.obj V) (ℱ.val.obj V) := sectionModule varphi ℱ V
  letI : IsScalarTower (𝒪₁.obj.obj V) (𝒪₂.obj.obj V) (ℱ.val.obj V) :=
    IsScalarTower.of_compHom (𝒪₁.obj.obj V) (𝒪₂.obj.obj V) (ℱ.val.obj V)
  letI : Algebra (𝒪₁.obj.obj U) (𝒪₁.obj.obj V) := RingHom.toAlgebra (𝒪₁.obj.map i).hom
  letI : Algebra (𝒪₂.obj.obj U) (𝒪₂.obj.obj V) := RingHom.toAlgebra (𝒪₂.obj.map i).hom
  letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj V) :=
    RingHom.toAlgebra (((varphi.hom.app V).hom).comp ((𝒪₁.obj.map i).hom))
  letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj V) :=
    Module.compHom (ℱ.val.obj V) (((varphi.hom.app V).hom).comp ((𝒪₁.obj.map i).hom))
  letI : Module (𝒪₂.obj.obj U) (ℱ.val.obj V) := Module.compHom (ℱ.val.obj V) ((𝒪₂.obj.map i).hom)
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₁.obj.obj V) (𝒪₂.obj.obj V) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (𝒪₂.obj.obj V) :=
    restrictionRing_isScalarTower_right varphi i
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₁.obj.obj V) (ℱ.val.obj V) :=
    IsScalarTower.of_compHom (𝒪₁.obj.obj U) (𝒪₁.obj.obj V) (ℱ.val.obj V)
  letI : IsScalarTower (𝒪₂.obj.obj U) (𝒪₂.obj.obj V) (ℱ.val.obj V) :=
    restrictionModule_isScalarTower_right ℱ i
  let fUV : ℱ.val.obj U →ₗ[𝒪₂.obj.obj U] ℱ.val.obj V := (ℱ.val.map i).hom
  ModuleCat.ofHom (principalPartsBaseChangeMap k fUV)

-- Proof sketch: the base-change map for principal parts along the identity restriction on an open
-- set is the identity map on the quotient presentation, which matches the identity structure map
-- required in `PresheafOfModules`.
/-- The objectwise principal-parts restriction map is compatible with identity inclusions of opens. -/
private theorem objectwisePrincipalPartsRestriction_id (varphi : 𝒪₁ ⟶ 𝒪₂)
    (ℱ : SheafOfModules (ringSheaf 𝒪₂)) (k : ℕ) (U : (Opens X)ᵒᵖ) :
    objectwisePrincipalPartsRestriction varphi ℱ k (𝟙 U) =
      (ModuleCat.restrictScalarsId' (((ringSheaf 𝒪₂).obj).map (𝟙 U)).hom
        (congrArg RingCat.Hom.hom (((ringSheaf 𝒪₂).obj).map_id U))).inv.app
          (objectwisePrincipalPartsModule varphi ℱ k U) := sorry

-- Proof sketch: the restriction maps are exactly the principal-parts base-change maps attached to
-- the restriction maps of `𝒪₁`, `𝒪₂`, and `ℱ`; their compatibility with composition is the
-- functoriality statement `principalPartsBaseChangeMap_comp`.
/-- The objectwise principal-parts restriction maps are compatible with composition of opens. -/
private theorem objectwisePrincipalPartsRestriction_comp (varphi : 𝒪₁ ⟶ 𝒪₂)
    (ℱ : SheafOfModules (ringSheaf 𝒪₂)) (k : ℕ)
    {U V W : (Opens X)ᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) :
    objectwisePrincipalPartsRestriction varphi ℱ k (i ≫ j) =
      objectwisePrincipalPartsRestriction varphi ℱ k i ≫
        (ModuleCat.restrictScalars (((ringSheaf 𝒪₂).obj).map i).hom).map
          (objectwisePrincipalPartsRestriction varphi ℱ k j) ≫
        (ModuleCat.restrictScalarsComp' (((ringSheaf 𝒪₂).obj).map i).hom
          (((ringSheaf 𝒪₂).obj).map j).hom (((ringSheaf 𝒪₂).obj).map (i ≫ j)).hom
          (congrArg RingCat.Hom.hom (((ringSheaf 𝒪₂).obj).map_comp i j))).inv.app
          (objectwisePrincipalPartsModule varphi ℱ k W) := sorry

/-- The presheaf `U ↦ P^k_{𝒪₂(U)/𝒪₁(U)}(ℱ(U))` of objectwise principal-parts modules. -/
def principalPartsPresheaf (varphi : 𝒪₁ ⟶ 𝒪₂)
    (ℱ : SheafOfModules (ringSheaf 𝒪₂)) (k : ℕ) :
    PresheafOfModules (ringSheaf 𝒪₂).obj :=
  { obj := objectwisePrincipalPartsModule varphi ℱ k
    map := objectwisePrincipalPartsRestriction varphi ℱ k
    map_id := objectwisePrincipalPartsRestriction_id varphi ℱ k
    map_comp := objectwisePrincipalPartsRestriction_comp varphi ℱ k }

/-- The sheaf `P^k_{𝒪₂/𝒪₁}(ℱ)` obtained by sheafifying the objectwise principal-parts presheaf. -/
noncomputable def principalParts (varphi : 𝒪₁ ⟶ 𝒪₂)
    (ℱ : SheafOfModules (ringSheaf 𝒪₂)) (k : ℕ) :
    SheafOfModules (ringSheaf 𝒪₂) :=
  (PresheafOfModules.sheafification (𝟙 (ringSheaf 𝒪₂).obj)).obj
    (principalPartsPresheaf varphi ℱ k)

end

end TopCat.Sheaf
end

notation:max "P^{" k "}_[" φ "](" ℱ ")" =>
  TopCat.Sheaf.principalParts φ ℱ k

noncomputable section

namespace TopCat.Sheaf

section

variable {X : TopCat.{u}}
variable {𝒪₁ 𝒪₂ : TopCat.Sheaf CommRingCat.{u} X}

/-- The sheaf of principal parts is the sheafification of the objectwise principal-parts
presheaf. -/
theorem principalParts_def (varphi : 𝒪₁ ⟶ 𝒪₂)
    (ℱ : SheafOfModules (ringSheaf 𝒪₂)) (k : ℕ) :
    P^{k}_[varphi](ℱ) =
      (PresheafOfModules.sheafification (𝟙 (ringSheaf 𝒪₂).obj)).obj
        (principalPartsPresheaf varphi ℱ k) := rfl

/-- The codomain presheaf used by the sheafification adjunction for maps out of `principalParts`;
it is just the underlying presheaf of `𝒢`, viewed through restriction of scalars along the
identity of `ringSheaf 𝒪₂`. -/
private abbrev principalPartsTargetPresheaf (𝒢 : SheafOfModules (ringSheaf 𝒪₂)) :
    PresheafOfModules (ringSheaf 𝒪₂).obj :=
  (PresheafOfModules.restrictScalars (𝟙 (ringSheaf 𝒪₂).obj)).obj 𝒢.val

private noncomputable abbrev objectwisePrincipalPartsLinearEquiv (varphi : 𝒪₁ ⟶ 𝒪₂)
    (ℱ 𝒢 : SheafOfModules (ringSheaf 𝒪₂)) (k : ℕ) (U : (Opens X)ᵒᵖ) :=
  letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := sectionAlgebra varphi U
  letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
  letI : Module (𝒪₁.obj.obj U) (𝒢.val.obj U) := sectionModule varphi 𝒢 U
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) :=
    IsScalarTower.of_compHom (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U)
  letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (𝒢.val.obj U) :=
    IsScalarTower.of_compHom (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (𝒢.val.obj U)
  principal_parts_linear_map_equiv_differential_operators
    (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) k (𝒢.val.obj U)

private noncomputable def principalPartsPresheafHomEquiv (varphi : 𝒪₁ ⟶ 𝒪₂)
    (ℱ : SheafOfModules (ringSheaf 𝒪₂)) (k : ℕ)
    (𝒢 : SheafOfModules (ringSheaf 𝒪₂)) :
    (principalPartsPresheaf varphi ℱ k ⟶ principalPartsTargetPresheaf 𝒢) ≃
      (differentialOperatorsFunctor varphi ℱ k).obj 𝒢 where
  toFun f := by
    let Dm :
        (SheafOfModules.restrictScalars (ringSheafMap varphi)).obj ℱ ⟶
          (SheafOfModules.restrictScalars (ringSheafMap varphi)).obj 𝒢 :=
      ⟨{
        app := fun U ↦
          letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := sectionAlgebra varphi U
          letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
          letI : Module (𝒪₁.obj.obj U) (𝒢.val.obj U) := sectionModule varphi 𝒢 U
          letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) :=
            IsScalarTower.of_compHom (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U)
          letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (𝒢.val.obj U) :=
            IsScalarTower.of_compHom (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (𝒢.val.obj U)
          let fU :
              principal_parts_module (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) k →ₗ[𝒪₂.obj.obj U]
                𝒢.val.obj U :=
            { toFun := (f.app U).hom
              map_add' := (f.app U).hom.map_add
              map_smul' := (f.app U).hom.map_smul }
          letI : Module ((ringSheaf 𝒪₁).obj.obj U) (ℱ.val.obj U) :=
            Module.compHom (ℱ.val.obj U) (((ringSheafMap varphi).hom.app U).hom)
          letI : Module ((ringSheaf 𝒪₁).obj.obj U) (𝒢.val.obj U) :=
            Module.compHom (𝒢.val.obj U) (((ringSheafMap varphi).hom.app U).hom)
          show ((SheafOfModules.restrictScalars (ringSheafMap varphi)).obj ℱ).val.obj U ⟶
              ((SheafOfModules.restrictScalars (ringSheafMap varphi)).obj 𝒢).val.obj U from
            ModuleCat.ofHom
              { toFun := ((objectwisePrincipalPartsLinearEquiv varphi ℱ 𝒢 k U fU).1)
                map_add' := ((objectwisePrincipalPartsLinearEquiv varphi ℱ 𝒢 k U fU).1).map_add
                map_smul' := ((objectwisePrincipalPartsLinearEquiv varphi ℱ 𝒢 k U fU).1).map_smul }
        naturality := by
          intro U V i
          sorry
      }⟩
    exact ⟨Dm, by
      sorry⟩
  invFun D := by
    refine
      {
        app := fun U ↦
          letI : Algebra (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) := sectionAlgebra varphi U
          letI : Module (𝒪₁.obj.obj U) (ℱ.val.obj U) := sectionModule varphi ℱ U
          letI : Module (𝒪₁.obj.obj U) (𝒢.val.obj U) := sectionModule varphi 𝒢 U
          letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U) :=
            IsScalarTower.of_compHom (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (ℱ.val.obj U)
          letI : IsScalarTower (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (𝒢.val.obj U) :=
            IsScalarTower.of_compHom (𝒪₁.obj.obj U) (𝒪₂.obj.obj U) (𝒢.val.obj U)
          let DU : ℱ.val.obj U →ₗ[𝒪₁.obj.obj U] 𝒢.val.obj U :=
            { toFun := (D.1.val.app U).hom
              map_add' := (D.1.val.app U).hom.map_add
              map_smul' := (D.1.val.app U).hom.map_smul }
          ModuleCat.ofHom <|
            (objectwisePrincipalPartsLinearEquiv varphi ℱ 𝒢 k U).symm
              ⟨DU, by
                sorry⟩
        naturality := by
          intro U V i
          sorry
      }
  left_inv f := by
    sorry
  right_inv D := by
    sorry

-- Proof sketch: argue exactly as in Lemma `17.28.4`, replacing Kähler differentials by
-- `principal_parts_module`. On each open set, Lemma `10.133.3` gives the universal
-- principal-parts representation, and the sheafification adjunction upgrades these objectwise
-- universal properties to the sheaf-level representing property from Lemma `17.29.3`.
/-- Lemma 17.29.5: the sheaf `P^k_{𝒪₂/𝒪₁}(ℱ)`, equivalently the sheaf associated to the
presheaf `U ↦ P^k_{𝒪₂(U)/𝒪₁(U)}(ℱ(U))`, is a module of principal parts of order `k` of `ℱ`
relative to `𝒪₁ ⟶ 𝒪₂`. -/
noncomputable def principalParts_is_principal_parts_module_of_order
    (varphi : 𝒪₁ ⟶ 𝒪₂) (ℱ : SheafOfModules (ringSheaf 𝒪₂)) (k : ℕ) :
    (differentialOperatorsFunctor varphi ℱ k).CorepresentableBy
      P^{k}_[varphi](ℱ) where
  homEquiv {𝒢} :=
    (PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf 𝒪₂).obj)).trans
      (principalPartsPresheafHomEquiv varphi ℱ k 𝒢)
  homEquiv_comp {𝒢 𝒢'} α f := by
    sorry

end

end TopCat.Sheaf
end
