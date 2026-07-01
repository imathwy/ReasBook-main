import Mathlib
import stacks_project.Chap18.Lemma_18_28_15
import stacks_project.Chap18.Lemma_18_28_13
import stacks_project.Chap18.Lemma_18_33_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open PresheafOfModules.DifferentialsConstruction
open scoped SheafOfModules.RingedSite TensorProduct

noncomputable section

universe u

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O₁ O₂ O₂' : Sheaf J CommRingCat.{u}}

/- Domain-style sampling for Lemma 18.33.8:
- primary domain: the conormal exact sequence for a locally surjective morphism of sheaves of
  commutative rings on a Grothendieck site;
- sampled owner declarations:
  `ringedSiteStructureMap`,
  `Ω(φ)`,
  `KaehlerDifferential.kerCotangentToTensor`,
  `KaehlerDifferential.mapBaseChange`,
  `SheafOfModules.pullback`;
- best owner abstraction: the site-level scalar-extended conormal sequence of `O₂'`-module sheaves
  attached to a composable pair `φ : O₁ ⟶ O₂`, `α : O₂ ⟶ O₂'`;
- primitive data: the source-side kernel ideal presheaf of `α`, its cotangent presheaf
  `Ker(α)/Ker(α)^2` over `O₂`, and the canonical Kähler maps on sections;
- derived API: the sheaf-level maps
  `conormalMap φ α : conormalSource α ⟶ conormalTensorTerm φ α` and
  `conormalToDifferentials φ α : conormalTensorTerm φ α ⟶ Ω(φ ≫ α)`, their exactness under local
  surjectivity of `α`, and the objectwise formula sending the class of `f` to `1 ⊗ df`.

Source/core/bridge triage:
- `source-facing`: the scalar-extended conormal sequence
  `conormalSource α ⟶ O₂' ⊗[O₂] Ω(O₂/O₁) ⟶ Ω(O₂'/O₁) ⟶ 0`, which agrees with the textbook
  `Ker(α)/Ker(α)^2` sequence once local surjectivity identifies the left term with the intrinsic
  target-side conormal module;
- `core/canonical`: `Ω(φ)`, `ringedSiteStructureMap α`, `SheafOfModules.pullback`, and the
  ring-level Kähler maps from mathlib/Chapter 10;
- `bridge/view`: the objectwise section maps and the internal presheaf-level realizations used to
  build the sheaf morphisms.

Accordingly, this file keeps the scalar-extended sheaf-level conormal sequence as the public owner
and relegates the sectionwise maps to companion bridge API. It also reuses the chapter owner
`Ω(φ)` instead of rephrasing the lemma purely as objectwise ring statements. -/

/-- The underlying `RingCat`-sheaf morphism of a morphism of sheaves of commutative rings. -/
private abbrev ringSheafMap {O O' : Sheaf J CommRingCat.{u}} (α : O ⟶ O') :
    ringSheaf J O ⟶ ringSheaf J O' :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).map α

private abbrev conormalScalarPresheaf (α : O₂ ⟶ O₂') :
    PresheafOfModules (ringSheaf J O₂).obj :=
  (PresheafOfModules.restrictScalars (ringSheafMap α).hom).obj
    (PresheafOfModules.unit (ringSheaf J O₂').obj)

private abbrev conormalTensorSpacePresheaf (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂') :
    PresheafOfModules (ringSheaf J O₂).obj :=
  PresheafOfModules.Monoidal.tensorObj
    (conormalScalarPresheaf α)
    (relativeDifferentials' φ.hom)

private abbrev conormalTensorTermOverSource
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂') :
    SheafOfModules (ringSheaf J O₂) :=
  (PresheafOfModules.sheafification
      (𝟙 (ringSheaf J O₂).obj)).obj
    (conormalTensorSpacePresheaf φ α)

private abbrev conormalIdeal
    (α : O₂ ⟶ O₂') (U : Cᵒᵖ) :
    Ideal (O₂.obj.obj U) :=
  RingHom.ker ((α.hom.app U).hom)

private theorem conormalIdeal_le_comap
    (α : O₂ ⟶ O₂') {U V : Cᵒᵖ} (i : U ⟶ V) :
    conormalIdeal α U ≤
      (conormalIdeal α V).comap ((O₂.obj.map i).hom) := by
  sorry

private abbrev conormalObj
    (α : O₂ ⟶ O₂') (U : Cᵒᵖ) :
    ModuleCat (O₂.obj.obj U) :=
  ModuleCat.of (O₂.obj.obj U) (conormalIdeal α U).Cotangent

private abbrev conormalRestriction
    (α : O₂ ⟶ O₂') {U V : Cᵒᵖ} (i : U ⟶ V) :
    conormalObj α U ⟶
      (ModuleCat.restrictScalars
        (((ringSheaf J O₂).obj.map i).hom)).obj
        (conormalObj α V) :=
  let R := O₂.obj.obj U
  let S := O₂.obj.obj V
  let _ : Algebra R R := RingHom.toAlgebra (RingHom.id R)
  let _ : Algebra R S := (O₂.obj.map i).hom.toAlgebra
  ModuleCat.ofHom
    (Ideal.mapCotangent
      (conormalIdeal α U)
      (conormalIdeal α V)
      { toRingHom := (O₂.obj.map i).hom
        commutes' := by
          intro r
          rfl }
      (conormalIdeal_le_comap α i))

private theorem conormalRestriction_id
    (α : O₂ ⟶ O₂') (U : Cᵒᵖ) :
    conormalRestriction α (𝟙 U) =
      (ModuleCat.restrictScalarsId'
        (((ringSheaf J O₂).obj.map (𝟙 U)).hom)
        (congrArg RingCat.Hom.hom
          ((ringSheaf J O₂).obj.map_id U))).inv.app
        (conormalObj α U) := by
  sorry

private theorem conormalRestriction_comp
    (α : O₂ ⟶ O₂') {U V W : Cᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) :
    conormalRestriction α (i ≫ j) =
      conormalRestriction α i ≫
        (ModuleCat.restrictScalars
          (((ringSheaf J O₂).obj.map i).hom)).map
          (conormalRestriction α j) ≫
        (ModuleCat.restrictScalarsComp'
          (((ringSheaf J O₂).obj.map i).hom)
          (((ringSheaf J O₂).obj.map j).hom)
          (((ringSheaf J O₂).obj.map (i ≫ j)).hom)
          (congrArg RingCat.Hom.hom
            ((ringSheaf J O₂).obj.map_comp i j))).inv.app
          (conormalObj α W) := by
  sorry

private def conormalPresheaf (α : O₂ ⟶ O₂') :
    PresheafOfModules (ringSheaf J O₂).obj :=
  { obj := conormalObj α
    map := conormalRestriction α
    map_id := conormalRestriction_id α
    map_comp := conormalRestriction_comp α }

private noncomputable def conormalSourceOverSource
    (α : O₂ ⟶ O₂') :
    SheafOfModules (ringSheaf J O₂) :=
  (PresheafOfModules.sheafification
      (𝟙 (ringSheaf J O₂).obj)).obj
    (conormalPresheaf α)

/-- The objectwise left map in the conormal sequence on sections over `U`. -/
abbrev sectionConormalMap
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂') (U : Cᵒᵖ) :
    let _ : Algebra (O₁.obj.obj U) (O₂.obj.obj U) := ((φ.hom.app U).hom).toAlgebra
    let _ : Algebra (O₂.obj.obj U) (O₂'.obj.obj U) := ((α.hom.app U).hom).toAlgebra
    (RingHom.ker ((α.hom.app U).hom)).Cotangent →ₗ[O₂.obj.obj U]
      O₂'.obj.obj U ⊗[O₂.obj.obj U] Ω[O₂.obj.obj U⁄O₁.obj.obj U] :=
  let _ : Algebra (O₁.obj.obj U) (O₂.obj.obj U) := ((φ.hom.app U).hom).toAlgebra
  let _ : Algebra (O₂.obj.obj U) (O₂'.obj.obj U) := ((α.hom.app U).hom).toAlgebra
  KaehlerDifferential.kerCotangentToTensor
    (O₁.obj.obj U) (O₂.obj.obj U) (O₂'.obj.obj U)

private abbrev sectionConormalHom
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂') (U : Cᵒᵖ) :
    conormalObj α U ⟶
      (conormalTensorSpacePresheaf φ α).obj U := by
  let _ : Algebra (O₁.obj.obj U) (O₂.obj.obj U) := ((φ.hom.app U).hom).toAlgebra
  let _ : Algebra (O₂.obj.obj U) (O₂'.obj.obj U) := ((α.hom.app U).hom).toAlgebra
  change conormalObj α U ⟶
    ModuleCat.of (O₂.obj.obj U)
      (O₂'.obj.obj U ⊗[O₂.obj.obj U] Ω[O₂.obj.obj U⁄O₁.obj.obj U])
  exact ModuleCat.ofHom (sectionConormalMap φ α U)

private theorem sectionConormalHom_naturality
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂') {U V : Cᵒᵖ} (i : U ⟶ V) :
    (conormalPresheaf α).map i ≫
        (ModuleCat.restrictScalars
          (((ringSheaf J O₂).obj.map i).hom)).map
          (sectionConormalHom φ α V) =
      sectionConormalHom φ α U ≫
        (conormalTensorSpacePresheaf φ α).map i := by
  sorry

private def conormalPresheafHom
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂') :
    conormalPresheaf α ⟶ conormalTensorSpacePresheaf φ α where
  app U := sectionConormalHom φ α U
  naturality i := sectionConormalHom_naturality φ α i

private noncomputable def conormalMapOverSource
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂') :
    conormalSourceOverSource α ⟶
      conormalTensorTermOverSource φ α :=
  ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (ringSheaf J O₂).obj)).homEquiv
      (conormalPresheaf α)
      (conormalTensorTermOverSource φ α)).symm
    (conormalPresheafHom φ α ≫
      by
        simpa [conormalTensorTermOverSource, conormalTensorSpacePresheaf] using
          (PresheafOfModules.sheafificationAdjunction
            (𝟙 (ringSheaf J O₂).obj)).unit.app
            (conormalTensorSpacePresheaf φ α))

/-- The objectwise right map in the conormal sequence on sections over `U`. -/
abbrev sectionBaseChangeMap
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂') (U : Cᵒᵖ) :
    let _ : Algebra (O₁.obj.obj U) (O₂.obj.obj U) := ((φ.hom.app U).hom).toAlgebra
    let _ : Algebra (O₂.obj.obj U) (O₂'.obj.obj U) := ((α.hom.app U).hom).toAlgebra
    let _ : Algebra (O₁.obj.obj U) (O₂'.obj.obj U) :=
      (((α.hom.app U).hom).comp ((φ.hom.app U).hom)).toAlgebra
    let _ : IsScalarTower (O₁.obj.obj U) (O₂.obj.obj U) (O₂'.obj.obj U) :=
      IsScalarTower.of_algebraMap_eq' rfl
    O₂'.obj.obj U ⊗[O₂.obj.obj U] Ω[O₂.obj.obj U⁄O₁.obj.obj U] →ₗ[O₂'.obj.obj U]
      Ω[O₂'.obj.obj U⁄O₁.obj.obj U] :=
  let _ : Algebra (O₁.obj.obj U) (O₂.obj.obj U) := ((φ.hom.app U).hom).toAlgebra
  let _ : Algebra (O₂.obj.obj U) (O₂'.obj.obj U) := ((α.hom.app U).hom).toAlgebra
  let _ : Algebra (O₁.obj.obj U) (O₂'.obj.obj U) :=
    (((α.hom.app U).hom).comp ((φ.hom.app U).hom)).toAlgebra
  let _ : IsScalarTower (O₁.obj.obj U) (O₂.obj.obj U) (O₂'.obj.obj U) :=
    IsScalarTower.of_algebraMap_eq' rfl
  KaehlerDifferential.mapBaseChange
    (O₁.obj.obj U) (O₂.obj.obj U) (O₂'.obj.obj U)

private theorem conormalTensorSpacePresheaf_obj_eq
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂') (U : Cᵒᵖ) :
    let _ : Algebra (O₁.obj.obj U) (O₂.obj.obj U) := ((φ.hom.app U).hom).toAlgebra
    let _ : Algebra (O₂.obj.obj U) (O₂'.obj.obj U) := ((α.hom.app U).hom).toAlgebra
    (conormalTensorSpacePresheaf φ α).obj U =
      ModuleCat.of (O₂.obj.obj U)
        (O₂'.obj.obj U ⊗[O₂.obj.obj U] Ω[O₂.obj.obj U⁄O₁.obj.obj U]) := by
  sorry

private theorem restrictedDifferentialsPresheaf_obj_eq
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂') (U : Cᵒᵖ) :
    let _ : Algebra (O₁.obj.obj U) (O₂.obj.obj U) := ((φ.hom.app U).hom).toAlgebra
    let _ : Algebra (O₂.obj.obj U) (O₂'.obj.obj U) := ((α.hom.app U).hom).toAlgebra
    let _ : Algebra (O₁.obj.obj U) (O₂'.obj.obj U) :=
      (((α.hom.app U).hom).comp ((φ.hom.app U).hom)).toAlgebra
    ((PresheafOfModules.restrictScalars (ringSheafMap α).hom).obj
      (relativeDifferentials' (φ ≫ α).hom)).obj U =
      ModuleCat.of (O₂.obj.obj U) Ω[O₂'.obj.obj U⁄O₁.obj.obj U] := by
  sorry

private abbrev sectionBaseChangeHom
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂') (U : Cᵒᵖ) :
    (conormalTensorSpacePresheaf φ α).obj U ⟶
      ((PresheafOfModules.restrictScalars (ringSheafMap α).hom).obj
        (relativeDifferentials' (φ ≫ α).hom)).obj U := by
  let _ : Algebra (O₁.obj.obj U) (O₂.obj.obj U) := ((φ.hom.app U).hom).toAlgebra
  let _ : Algebra (O₂.obj.obj U) (O₂'.obj.obj U) := ((α.hom.app U).hom).toAlgebra
  let _ : Algebra (O₁.obj.obj U) (O₂'.obj.obj U) :=
    (((α.hom.app U).hom).comp ((φ.hom.app U).hom)).toAlgebra
  let _ : IsScalarTower (O₁.obj.obj U) (O₂.obj.obj U) (O₂'.obj.obj U) :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact
    eqToHom (conormalTensorSpacePresheaf_obj_eq φ α U) ≫
      ModuleCat.ofHom
        ((sectionBaseChangeMap φ α U).restrictScalars (O₂.obj.obj U)) ≫
      eqToHom (restrictedDifferentialsPresheaf_obj_eq φ α U).symm

private def tensorToDifferentialsPresheafHom
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂') :
    conormalTensorSpacePresheaf φ α ⟶
      (PresheafOfModules.restrictScalars (ringSheafMap α).hom).obj
        (relativeDifferentials' (φ ≫ α).hom) where
  app U := sectionBaseChangeHom φ α U
  naturality := by
    intro U V i
    sorry

private abbrev restrictedDifferentialsUnit
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂') :
    (PresheafOfModules.restrictScalars (ringSheafMap α).hom).obj
        (relativeDifferentials' (φ ≫ α).hom) ⟶
      ((restrictionAlong α).obj Ω(φ ≫ α)).val :=
  (PresheafOfModules.restrictScalars (ringSheafMap α).hom).map
    ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf J O₂').obj)).unit.app
      (relativeDifferentials' (φ ≫ α).hom))

private noncomputable def tensorToDifferentialsOverSource
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂') :
    conormalTensorTermOverSource φ α ⟶
      (restrictionAlong α).obj Ω(φ ≫ α) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf J O₂).obj)).homEquiv
      (conormalTensorSpacePresheaf φ α)
      ((restrictionAlong α).obj Ω(φ ≫ α))).symm
    (tensorToDifferentialsPresheafHom φ α ≫
      restrictedDifferentialsUnit φ α)

private abbrev conormalPullback (α : O₂ ⟶ O₂') :
    SheafOfModules (ringSheaf J O₂) ⥤
      SheafOfModules (ringSheaf J O₂') :=
  SheafOfModules.pullback (ringedSiteStructureMap α)

/-- The pullback of the source-side conormal module `Ker(α) / Ker(α)^2` along `α`, viewed as a
sheaf of `O₂'`-modules.

This is the scalar-extended left term used in the site-level conormal sequence below. When `α` is
locally surjective, it models the textbook `O₂'`-module conormal sheaf. -/
abbrev conormalSource
    (α : O₂ ⟶ O₂') :
    SheafOfModules (ringSheaf J O₂') :=
  (conormalPullback α).obj (conormalSourceOverSource α)

/-- The tensor middle term `O₂' \otimes_{O₂} \Omega_{O₂/O₁}`, viewed as a sheaf of
`O₂'`-modules. -/
abbrev conormalTensorTerm
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂') :
    SheafOfModules (ringSheaf J O₂') :=
  (conormalPullback α).obj (conormalTensorTermOverSource φ α)

/-- The left map in the scalar-extended site-level conormal sequence attached to
`O₁ ⟶ O₂ ⟶ O₂'`. -/
noncomputable def conormalMap
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂') :
    conormalSource α ⟶ conormalTensorTerm φ α :=
  (conormalPullback α).map (conormalMapOverSource φ α)

/-- The canonical map `O₂' \otimes_{O₂} \Omega_{O₂/O₁} \to \Omega_{O₂'/O₁}`. -/
noncomputable def conormalToDifferentials
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂') :
    conormalTensorTerm φ α ⟶ Ω(φ ≫ α) :=
  ((SheafOfModules.pullbackPushforwardAdjunction
      (ringedSiteStructureMap α)).homEquiv
      (conormalTensorTermOverSource φ α)
      Ω(φ ≫ α)).symm
    (tensorToDifferentialsOverSource φ α)

-- Proof sketch: the composite is obtained by sheafifying the objectwise identity
-- `mapBaseChange ∘ kerCotangentToTensor = 0`.
/-- The scalar-extended canonical conormal sequence of sheaves has zero composite. -/
theorem conormal_comp_zero
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂') :
    conormalMap φ α ≫ conormalToDifferentials φ α = 0 := by
  sorry

-- Proof sketch: let `O₂''` be the image presheaf of `α.hom`. Algebra, Lemma `10.131.9` gives the
-- exact objectwise sequences for `O₂(U) → O₂''(U)`. Sheafifying those sequences and using local
-- surjectivity of `α` identifies `(O₂'')^#` with `O₂'`; Lemma `18.33.4` identifies the
-- sheafification of the right term with `Ω(φ ≫ α)`.
/-- Lemma 18.33.8: if `α : O₂ ⟶ O₂'` is locally surjective, then the scalar-extended canonical
conormal sequence of `O₂'`-modules
`conormalSource α ⟶ O₂' \otimes_{O₂} \Omega_{O₂/O₁} ⟶ \Omega_{O₂'/O₁} ⟶ 0`
is exact.

Here `conormalSource α` is, by definition, the pullback along `α` of the source-side conormal
module `Ker(α)/Ker(α)^2`; under local surjectivity this matches the textbook target-side conormal
module. -/
theorem conormalSequence_exact
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂')
    (hα : Sheaf.IsLocallySurjective α) :
    (ShortComplex.mk
      (conormalMap φ α)
      (conormalToDifferentials φ α)
      (conormal_comp_zero φ α)).Exact ∧
      Epi (conormalToDifferentials φ α) := by
  sorry

-- Proof sketch: objectwise surjectivity is a special case of local surjectivity of sheaves, so
-- the main sheaf-level exactness theorem applies directly.
/-- Companion bridge: sectionwise-surjective maps satisfy the hypotheses of the scalar-extended
conormal exact sequence. -/
theorem conormalSequence_exact_of_sectionwiseSurjective
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂')
    (hα : ∀ U : Cᵒᵖ, Function.Surjective ((α.hom.app U).hom)) :
    (ShortComplex.mk
      (conormalMap φ α)
      (conormalToDifferentials φ α)
      (conormal_comp_zero φ α)).Exact ∧
      Epi (conormalToDifferentials φ α) := by
  have hloc : Sheaf.IsLocallySurjective α := by
    exact Presheaf.isLocallySurjective_of_surjective J α.hom hα
  exact conormalSequence_exact φ α hloc

-- Proof sketch: this is exactly
-- `KaehlerDifferential.kerCotangentToTensor_toCotangent` for the section ring map
-- `O₂(U) → O₂'(U)`.
/-- Lemma 18.33.8, formula for the left map: in library tensor order, the class of a local section
`f` of the kernel ideal over `U` maps to `1 ⊗ df`. -/
theorem sectionConormalMap_toCotangent
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂') (U : Cᵒᵖ)
    (x : RingHom.ker ((α.hom.app U).hom)) :
    let _ : Algebra (O₁.obj.obj U) (O₂.obj.obj U) := ((φ.hom.app U).hom).toAlgebra
    let _ : Algebra (O₂.obj.obj U) (O₂'.obj.obj U) := ((α.hom.app U).hom).toAlgebra
    sectionConormalMap φ α U (Ideal.toCotangent (RingHom.ker ((α.hom.app U).hom)) x) =
      (1 : O₂'.obj.obj U) ⊗ₜ[O₂.obj.obj U]
        KaehlerDifferential.D (O₁.obj.obj U) (O₂.obj.obj U) x := by
  sorry

end SheafOfModules.RingedSite
