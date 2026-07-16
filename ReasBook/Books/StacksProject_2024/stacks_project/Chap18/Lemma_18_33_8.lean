import Mathlib
import StacksProject_2024.stacks_project.Chap18.Lemma_18_33_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open PresheafOfModules.DifferentialsConstruction
open scoped SheafOfModules.RingedSite TensorProduct

noncomputable section

universe u

namespace SheafOfModules.RingedSite

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
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
  -- Proof comment: kernel membership is preserved by restriction because `α.hom` is natural.
  intro x hx
  change (α.hom.app V).hom ((O₂.obj.map i).hom x) = 0
  have hnat :=
    DFunLike.congr_fun
      (congrArg CommRingCat.Hom.hom (α.hom.naturality i)) x
  have hx' : (α.hom.app U).hom x = 0 := hx
  simpa [hx'] using hnat

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

/-- Helper for Lemma 18.33.8: the cotangent restriction maps send a generator to the generator
induced by restricting its representative section. -/
private theorem conormalRestriction_toCotangent
    (α : O₂ ⟶ O₂') {U V : Cᵒᵖ} (i : U ⟶ V) (x : conormalIdeal α U) :
    conormalRestriction α i ((conormalIdeal α U).toCotangent x) =
      (conormalIdeal α V).toCotangent
        ⟨((O₂.obj.map i).hom) x, conormalIdeal_le_comap α i x.2⟩ := by
  let _ : Algebra (O₂.obj.obj U) (O₂.obj.obj V) := (O₂.obj.map i).hom.toAlgebra
  -- Proof comment: this is the canonical generator formula for `Ideal.mapCotangent`.
  change
    Ideal.mapCotangent
        (conormalIdeal α U)
        (conormalIdeal α V)
        { toRingHom := (O₂.obj.map i).hom
          commutes' := by
            intro r
            rfl }
        (conormalIdeal_le_comap α i)
        ((conormalIdeal α U).toCotangent x) =
      (conormalIdeal α V).toCotangent
        ⟨((O₂.obj.map i).hom) x, conormalIdeal_le_comap α i x.2⟩
  rfl

private theorem conormalRestriction_id
    (α : O₂ ⟶ O₂') (U : Cᵒᵖ) :
    conormalRestriction α (𝟙 U) =
      (ModuleCat.restrictScalarsId'
        (((ringSheaf J O₂).obj.map (𝟙 U)).hom)
        (congrArg RingCat.Hom.hom
          ((ringSheaf J O₂).obj.map_id U))).inv.app _ := by
  -- Route correction: compare the two maps on cotangent generators instead of unfolding the
  -- restriction-of-scalars coherence isomorphism.
  refine ModuleCat.hom_ext ?_
  ext z
  -- Proof comment: the cotangent module is generated by the image of the kernel ideal.
  obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective (conormalIdeal α U) z
  have hmap :
      ((O₂.obj.map (𝟙 U)).hom) (x : O₂.obj.obj U) = x := by
    -- The section ring restriction along the identity is the identity map.
    simpa using congrArg (fun h ↦ h (x : O₂.obj.obj U))
      (congrArg RingCat.Hom.hom ((ringSheaf J O₂).obj.map_id U))
  have hx :
      (conormalIdeal α U).toCotangent
          ⟨((O₂.obj.map (𝟙 U)).hom) x, conormalIdeal_le_comap α (𝟙 U) x.2⟩ =
        (conormalIdeal α U).toCotangent x := by
    exact congrArg (Ideal.toCotangent (conormalIdeal α U)) (Subtype.ext hmap)
  -- Proof comment: both maps now reduce to the same cotangent generator after rewriting the
  -- identity section restriction and the restriction-of-scalars coherence map.
  rw [conormalRestriction_toCotangent]
  rw [hx]
  symm
  exact ModuleCat.restrictScalarsId'App_inv_apply
    (((ringSheaf J O₂).obj.map (𝟙 U)).hom)
    (congrArg RingCat.Hom.hom ((ringSheaf J O₂).obj.map_id U))
    (conormalObj α U)
    ((conormalIdeal α U).toCotangent x)

/-- Helper for Lemma 18.33.8: the cotangent restriction maps satisfy the functorial composition
formula on generators. -/
private theorem conormalRestriction_comp_on_toCotangent
    (α : O₂ ⟶ O₂') {U V W : Cᵒᵖ} (i : U ⟶ V) (j : V ⟶ W)
    (x : conormalIdeal α U) :
    conormalRestriction α (i ≫ j) ((conormalIdeal α U).toCotangent x) =
      (conormalRestriction α i ≫
        (ModuleCat.restrictScalars
          (((ringSheaf J O₂).obj.map i).hom)).map
          (conormalRestriction α j) ≫
        (ModuleCat.restrictScalarsComp'
          (((ringSheaf J O₂).obj.map i).hom)
          (((ringSheaf J O₂).obj.map j).hom)
          (((ringSheaf J O₂).obj.map (i ≫ j)).hom)
          (congrArg RingCat.Hom.hom
            ((ringSheaf J O₂).obj.map_comp i j))).inv.app _)
        ((conormalIdeal α U).toCotangent x) := by
  have hmap :
      ((O₂.obj.map (i ≫ j)).hom) (x : O₂.obj.obj U) =
        ((O₂.obj.map j).hom) (((O₂.obj.map i).hom) x) := by
    -- The sheaf restriction maps compose on sections.
    simpa using congrArg (fun h ↦ h (x : O₂.obj.obj U))
      (congrArg RingCat.Hom.hom ((ringSheaf J O₂).obj.map_comp i j))
  -- Proof comment: after evaluating both maps on a generator, only the sectionwise
  -- composition identity remains.
  rw [conormalRestriction_toCotangent]
  simp only [conormalRestriction_toCotangent, ModuleCat.restrictScalarsComp'App_inv_apply]
  exact congrArg (Ideal.toCotangent (conormalIdeal α W)) (Subtype.ext hmap)

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
            ((ringSheaf J O₂).obj.map_comp i j))).inv.app _ := by
  -- Route correction: prove composition on cotangent generators first.
  apply ModuleCat.hom_ext
  ext z
  -- Proof comment: equality of maps out of the cotangent module is reduced to its generators.
  obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective (conormalIdeal α U) z
  -- Proof comment: the generator-level composition formula already computes both sides.
  simpa using conormalRestriction_comp_on_toCotangent α i j x

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

/-- Helper for Lemma 18.33.8: objectwise, the wrapped left map sends a cotangent generator to
`1 ⊗ d x`. -/
private theorem sectionConormalHom_on_toCotangent
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂') (U : Cᵒᵖ) (x : conormalIdeal α U) :
    let _ : Algebra (O₁.obj.obj U) (O₂.obj.obj U) := ((φ.hom.app U).hom).toAlgebra
    let _ : Algebra (O₂.obj.obj U) (O₂'.obj.obj U) := ((α.hom.app U).hom).toAlgebra
    sectionConormalHom φ α U ((conormalIdeal α U).toCotangent x) =
      (1 : O₂'.obj.obj U) ⊗ₜ[O₂.obj.obj U]
        KaehlerDifferential.D (O₁.obj.obj U) (O₂.obj.obj U) x := by
  let _ : Algebra (O₁.obj.obj U) (O₂.obj.obj U) := ((φ.hom.app U).hom).toAlgebra
  let _ : Algebra (O₂.obj.obj U) (O₂'.obj.obj U) := ((α.hom.app U).hom).toAlgebra
  let x' : RingHom.ker (algebraMap (O₂.obj.obj U) (O₂'.obj.obj U)) := x
  -- Proof comment: the wrapped section map is definitionally the canonical owner
  -- `kerCotangentToTensor`, so its generator formula is the ring-level owner theorem.
  change
    KaehlerDifferential.kerCotangentToTensor
        (O₁.obj.obj U) (O₂.obj.obj U) (O₂'.obj.obj U)
        (Ideal.toCotangent
          (RingHom.ker (algebraMap (O₂.obj.obj U) (O₂'.obj.obj U))) x') =
      (1 : O₂'.obj.obj U) ⊗ₜ[O₂.obj.obj U]
        KaehlerDifferential.D (O₁.obj.obj U) (O₂.obj.obj U) x'
  exact KaehlerDifferential.kerCotangentToTensor_toCotangent
    (O₁.obj.obj U) (O₂.obj.obj U) (O₂'.obj.obj U) x'

/-- Helper for Lemma 18.33.8: restricting scalars along `α` does not change the underlying
section restriction map on `O₂'`. -/
private theorem conormalScalarPresheaf_map_apply
    (α : O₂ ⟶ O₂') {U V : Cᵒᵖ} (i : U ⟶ V) (b : O₂'.obj.obj U) :
    (ConcreteCategory.hom ((conormalScalarPresheaf α).map i)) b =
      (O₂'.obj.map i).hom b := by
  -- Proof comment: `conormalScalarPresheaf α` is only a restriction-of-scalars wrapper around
  -- the unit `O₂'`-module, so its section restriction is definitionally the same map.
  rfl

/-- Helper for Lemma 18.33.8: the tensor-presheaf restriction map sends a pure tensor to the pure
tensor of the restricted factors. -/
private theorem conormalTensorSpacePresheaf_map_tmul
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂') {U V : Cᵒᵖ} (i : U ⟶ V)
    (b : O₂'.obj.obj U) (x : O₂.obj.obj U) :
    let _ : Algebra (O₁.obj.obj U) (O₂.obj.obj U) := ((φ.hom.app U).hom).toAlgebra
    let _ : Algebra (O₂.obj.obj U) (O₂'.obj.obj U) := ((α.hom.app U).hom).toAlgebra
    let _ : Algebra (O₁.obj.obj V) (O₂.obj.obj V) := ((φ.hom.app V).hom).toAlgebra
    let _ : Algebra (O₂.obj.obj V) (O₂'.obj.obj V) := ((α.hom.app V).hom).toAlgebra
    ((conormalTensorSpacePresheaf φ α).map i).hom
        (b ⊗ₜ[O₂.obj.obj U]
          KaehlerDifferential.D (O₁.obj.obj U) (O₂.obj.obj U) x) =
      ((O₂'.obj.map i).hom b) ⊗ₜ[O₂.obj.obj V]
        KaehlerDifferential.D (O₁.obj.obj V) (O₂.obj.obj V) ((O₂.obj.map i).hom x) := by
  -- TODO: use `PresheafOfModules.Monoidal.tensorObj_map_tmul` once in a stabilized normal form,
  -- then rewrite the first factor by `conormalScalarPresheaf_map_apply` and the second factor by
  -- `relativeDifferentials'_map_d`. The current blocker is the wrapped `restrictScalars` object
  -- on the first factor, which triggers `whnf/isDefEq` timeouts before the tensor map lemma can
  -- be instantiated cleanly.
  sorry

private theorem sectionConormalHom_naturality
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂') {U V : Cᵒᵖ} (i : U ⟶ V) :
    (conormalPresheaf α).map i ≫
        (ModuleCat.restrictScalars
          (((ringSheaf J O₂).obj.map i).hom)).map
          (sectionConormalHom φ α V) =
      sectionConormalHom φ α U ≫
        (conormalTensorSpacePresheaf φ α).map i := by
  -- TODO: reduce to cotangent generators using `Ideal.toCotangent_surjective`, compute the left
  -- branch with `conormalRestriction_toCotangent` and `sectionConormalHom_on_toCotangent`, and
  -- finish with `conormalTensorSpacePresheaf_map_tmul` on `1 ⊗ d x`. This is blocked exactly by
  -- the tensor-map normalization issue recorded in `conormalTensorSpacePresheaf_map_tmul`.
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
  -- Proof comment: this is the objectwise description of the tensor presheaf by definition.
  rfl

private theorem restrictedDifferentialsPresheaf_obj_eq
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂') (U : Cᵒᵖ) :
    let _ : Algebra (O₁.obj.obj U) (O₂.obj.obj U) := ((φ.hom.app U).hom).toAlgebra
    let _ : Algebra (O₂.obj.obj U) (O₂'.obj.obj U) := ((α.hom.app U).hom).toAlgebra
    let _ : Algebra (O₁.obj.obj U) (O₂'.obj.obj U) :=
      (((α.hom.app U).hom).comp ((φ.hom.app U).hom)).toAlgebra
    ((PresheafOfModules.restrictScalars (ringSheafMap α).hom).obj
      (relativeDifferentials' (φ ≫ α).hom)).obj U =
      ModuleCat.of (O₂.obj.obj U) Ω[O₂'.obj.obj U⁄O₁.obj.obj U] := by
  -- Proof comment: restricting scalars does not change the underlying objectwise differential
  -- module; only the base ring action is viewed through `α`.
  rfl

-- TODO: construct the wrapped base-change morphism from the objectwise Kähler map once the
-- restriction-of-scalars instance bookkeeping is stabilized.
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
  change ModuleCat.of (O₂.obj.obj U)
      (O₂'.obj.obj U ⊗[O₂.obj.obj U] Ω[O₂.obj.obj U⁄O₁.obj.obj U]) ⟶
    ModuleCat.of (O₂.obj.obj U) Ω[O₂'.obj.obj U⁄O₁.obj.obj U]
  exact ModuleCat.ofHom
    ((sectionBaseChangeMap φ α U).restrictScalars (O₂.obj.obj U))

/-- Helper for Lemma 18.33.8: objectwise, the wrapped right map is exactly the sectionwise Kähler
base-change map. -/
private theorem sectionBaseChangeHom_typed
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂') (U : Cᵒᵖ) :
    sectionBaseChangeHom φ α U =
      let _ : Algebra (O₁.obj.obj U) (O₂.obj.obj U) := ((φ.hom.app U).hom).toAlgebra
      let _ : Algebra (O₂.obj.obj U) (O₂'.obj.obj U) := ((α.hom.app U).hom).toAlgebra
      let _ : Algebra (O₁.obj.obj U) (O₂'.obj.obj U) :=
        (((α.hom.app U).hom).comp ((φ.hom.app U).hom)).toAlgebra
      let _ : IsScalarTower (O₁.obj.obj U) (O₂.obj.obj U) (O₂'.obj.obj U) :=
        IsScalarTower.of_algebraMap_eq' rfl
      ModuleCat.ofHom
        ((sectionBaseChangeMap φ α U).restrictScalars (O₂.obj.obj U)) := by
  -- Proof comment: `sectionBaseChangeHom` is defined by this wrapped base-change map.
  rfl

/-- Helper for Lemma 18.33.8: on a pure tensor `b ⊗ d x`, the sectionwise right map is the
expected Kähler base-change formula `b • d(α(x))`. -/
private theorem sectionBaseChangeHom_on_tmul_d
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂') (U : Cᵒᵖ) :
    let _ : Algebra (O₁.obj.obj U) (O₂.obj.obj U) := ((φ.hom.app U).hom).toAlgebra
    let _ : Algebra (O₂.obj.obj U) (O₂'.obj.obj U) := ((α.hom.app U).hom).toAlgebra
    let _ : Algebra (O₁.obj.obj U) (O₂'.obj.obj U) :=
      (((α.hom.app U).hom).comp ((φ.hom.app U).hom)).toAlgebra
    let _ : IsScalarTower (O₁.obj.obj U) (O₂.obj.obj U) (O₂'.obj.obj U) :=
      IsScalarTower.of_algebraMap_eq' rfl
    ∀ (b : O₂'.obj.obj U) (x : O₂.obj.obj U),
      sectionBaseChangeHom φ α U
          (b ⊗ₜ[O₂.obj.obj U]
            KaehlerDifferential.D (O₁.obj.obj U) (O₂.obj.obj U) x) =
        b • KaehlerDifferential.D (O₁.obj.obj U) (O₂'.obj.obj U)
          ((α.hom.app U).hom x) := by
  let _ : Algebra (O₁.obj.obj U) (O₂.obj.obj U) := ((φ.hom.app U).hom).toAlgebra
  let _ : Algebra (O₂.obj.obj U) (O₂'.obj.obj U) := ((α.hom.app U).hom).toAlgebra
  let _ : Algebra (O₁.obj.obj U) (O₂'.obj.obj U) :=
    (((α.hom.app U).hom).comp ((φ.hom.app U).hom)).toAlgebra
  let _ : IsScalarTower (O₁.obj.obj U) (O₂.obj.obj U) (O₂'.obj.obj U) :=
    IsScalarTower.of_algebraMap_eq' rfl
  simpa using
    (fun b x ↦ by
      -- Proof comment: unfold the wrapped morphism and apply the ring-level base-change formulas.
      rw [sectionBaseChangeHom_typed]
      change
        KaehlerDifferential.mapBaseChange
            (O₁.obj.obj U) (O₂.obj.obj U) (O₂'.obj.obj U)
            (b ⊗ₜ[O₂.obj.obj U]
              KaehlerDifferential.D (O₁.obj.obj U) (O₂.obj.obj U) x) =
          b • KaehlerDifferential.D (O₁.obj.obj U) (O₂'.obj.obj U) ((α.hom.app U).hom x)
      rw [KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D]
      rfl)

/-- Helper for Lemma 18.33.8: the presheaf-level right map naturality square agrees on the pure
tensors `b ⊗ d x`. -/
private theorem sectionBaseChangeHom_naturality_on_tmul_d
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂') {U V : Cᵒᵖ} (i : U ⟶ V) :
    let _ : Algebra (O₁.obj.obj U) (O₂.obj.obj U) := ((φ.hom.app U).hom).toAlgebra
    let _ : Algebra (O₂.obj.obj U) (O₂'.obj.obj U) := ((α.hom.app U).hom).toAlgebra
    let _ : Algebra (O₁.obj.obj U) (O₂'.obj.obj U) :=
      (((α.hom.app U).hom).comp ((φ.hom.app U).hom)).toAlgebra
    let _ : IsScalarTower (O₁.obj.obj U) (O₂.obj.obj U) (O₂'.obj.obj U) :=
      IsScalarTower.of_algebraMap_eq' rfl
    let _ : Algebra (O₁.obj.obj V) (O₂.obj.obj V) := ((φ.hom.app V).hom).toAlgebra
    let _ : Algebra (O₂.obj.obj V) (O₂'.obj.obj V) := ((α.hom.app V).hom).toAlgebra
    let _ : Algebra (O₁.obj.obj V) (O₂'.obj.obj V) :=
      (((α.hom.app V).hom).comp ((φ.hom.app V).hom)).toAlgebra
    let _ : IsScalarTower (O₁.obj.obj V) (O₂.obj.obj V) (O₂'.obj.obj V) :=
      IsScalarTower.of_algebraMap_eq' rfl
    ∀ (b : O₂'.obj.obj U) (x : O₂.obj.obj U),
      ((conormalTensorSpacePresheaf φ α).map i ≫
          (ModuleCat.restrictScalars
            (((ringSheaf J O₂).obj.map i).hom)).map
            (sectionBaseChangeHom φ α V))
          (b ⊗ₜ[O₂.obj.obj U]
            KaehlerDifferential.D (O₁.obj.obj U) (O₂.obj.obj U) x) =
        (sectionBaseChangeHom φ α U ≫
          ((PresheafOfModules.restrictScalars (ringSheafMap α).hom).obj
            (relativeDifferentials' (φ ≫ α).hom)).map i)
          (b ⊗ₜ[O₂.obj.obj U]
            KaehlerDifferential.D (O₁.obj.obj U) (O₂.obj.obj U) x) := by
  -- TODO: normalize the left branch with `conormalTensorSpacePresheaf_map_tmul`, compute the
  -- right branch by `sectionBaseChangeHom_on_tmul_d` and `map_smul`, and close with the naturality
  -- equation for `α` together with `relativeDifferentials'_map_d`.
  sorry

-- TODO: assemble the presheaf-level right map once the objectwise wrapped base-change map and its
-- naturality are proved.
private def tensorToDifferentialsPresheafHom
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂') :
    conormalTensorSpacePresheaf φ α ⟶
      (PresheafOfModules.restrictScalars (ringSheafMap α).hom).obj
        (relativeDifferentials' (φ ≫ α).hom) where
  app U := sectionBaseChangeHom φ α U
  naturality {U V} i := by
    -- TODO: after reinstating `sectionBaseChangeHom_naturality_on_tmul_d`, extend the generator
    -- equality to all pure tensors by `ModuleCat.MonoidalCategory.tensor_ext` and the fact that
    -- Kähler differentials are spanned by the universal generators `d x`.
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

/-- Helper for Lemma 18.33.8: the source-side conormal map is defined by transposing the
presheaf-level conormal morphism across sheafification. -/
private theorem conormalMapOverSource_def
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂') :
    conormalMapOverSource φ α =
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf J O₂).obj)).homEquiv
          (conormalPresheaf α)
          (conormalTensorTermOverSource φ α)).symm
        (conormalPresheafHom φ α ≫
          ((PresheafOfModules.sheafificationAdjunction
              (𝟙 (ringSheaf J O₂).obj)).unit.app
            (conormalTensorSpacePresheaf φ α))) := by
  -- Proof comment: this is exactly the defining adjoint transpose.
  rfl

/-- Helper for Lemma 18.33.8: under the sheafification adjunction, the source-side tensor-to-
differentials map recovers the presheaf morphism used in its definition. -/
private theorem tensorToDifferentialsOverSource_def
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂') :
    tensorToDifferentialsOverSource φ α =
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf J O₂).obj)).homEquiv
          (conormalTensorSpacePresheaf φ α)
          ((restrictionAlong α).obj Ω(φ ≫ α))).symm
        (tensorToDifferentialsPresheafHom φ α ≫
          restrictedDifferentialsUnit φ α) := by
  -- Proof comment: this is exactly the defining adjoint transpose.
  rfl

/-- Helper for Lemma 18.33.8: sectionwise, the composite of the left conormal map with the right
base-change map kills every cotangent generator coming from the kernel ideal. -/
private theorem sectionComposite_zero_on_generator
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂') (U : Cᵒᵖ) (x : conormalIdeal α U) :
    sectionBaseChangeHom φ α U
        ((sectionConormalHom φ α U).hom ((conormalIdeal α U).toCotangent x)) = 0 := by
  -- Proof comment: the left map sends the cotangent generator to `1 ⊗ d x`.
  rw [sectionConormalHom_on_toCotangent]
  -- Proof comment: the right map then computes to the differential of `α(x)`, which vanishes
  -- because `x` lies in the kernel ideal.
  have h :=
    sectionBaseChangeHom_on_tmul_d φ α U (1 : O₂'.obj.obj U) (x : O₂.obj.obj U)
  simpa [RingHom.mem_ker.mp x.2, map_zero] using h

/-- Helper for Lemma 18.33.8: the presheaf-level conormal composite is zero. -/
private theorem conormalPresheafComposite_zero
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂') :
    conormalPresheafHom φ α ≫ tensorToDifferentialsPresheafHom φ α = 0 := by
  ext U z
  -- Proof comment: the cotangent source is generated by kernel classes, so the composite is
  -- determined by its value on one generator.
  obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective (conormalIdeal α U) z
  exact sectionComposite_zero_on_generator φ α U x

/-- Helper for Lemma 18.33.8: after sheafifying the source-side presheaf row, the composite is
still zero. -/
private theorem conormalOverSourceCompZero
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂') :
    conormalMapOverSource φ α ≫ tensorToDifferentialsOverSource φ α = 0 := by
  -- TODO: move the composite through `PresheafOfModules.sheafificationHomEquiv`, rewrite the two
  -- source-side maps with `conormalMapOverSource_def` and `tensorToDifferentialsOverSource_def`,
  -- and then identify the resulting presheaf composite with
  -- `conormalPresheafHom φ α ≫ tensorToDifferentialsPresheafHom φ α`, which is already zero by
  -- `conormalPresheafComposite_zero`.
  sorry

private abbrev conormalPullback (α : O₂ ⟶ O₂') :
    SheafOfModules (ringSheaf J O₂) ⥤
      SheafOfModules (ringSheaf J O₂') :=
  SheafOfModules.pullback (SheafOfModules.RingedSite.ringedSiteStructureMap α)

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
      (SheafOfModules.RingedSite.ringedSiteStructureMap α)).homEquiv
      (conormalTensorTermOverSource φ α)
      Ω(φ ≫ α)).symm
    (tensorToDifferentialsOverSource φ α)

-- Proof sketch: the composite is obtained by sheafifying the objectwise identity
-- `mapBaseChange ∘ kerCotangentToTensor = 0`.
/-- The scalar-extended canonical conormal sequence of sheaves has zero composite. -/
theorem conormal_comp_zero
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₂') :
    conormalMap φ α ≫ conormalToDifferentials φ α = 0 := by
  apply ((SheafOfModules.pullbackPushforwardAdjunction
    (SheafOfModules.RingedSite.ringedSiteStructureMap α)).homEquiv _ _).injective
  -- Proof comment: under the pullback-pushforward adjunction, the public composite is exactly
  -- the source-side composite already shown to vanish after sheafification.
  rw [conormalMap]
  rw [CategoryTheory.Adjunction.homEquiv_naturality_left
    (SheafOfModules.pullbackPushforwardAdjunction
      (SheafOfModules.RingedSite.ringedSiteStructureMap α))
    (conormalMapOverSource φ α) (conormalToDifferentials φ α)]
  rw [conormalToDifferentials, Equiv.apply_symm_apply]
  exact conormalOverSourceCompZero φ α

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
  -- TODO: package the source-proof route through the image ring presheaf, sheafify the objectwise
  -- exact conormal rows, and compare the resulting sheaf with `O₂'` using `hα`.
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
    (x : conormalIdeal α U) :
    let _ : Algebra (O₁.obj.obj U) (O₂.obj.obj U) := ((φ.hom.app U).hom).toAlgebra
    let _ : Algebra (O₂.obj.obj U) (O₂'.obj.obj U) := ((α.hom.app U).hom).toAlgebra
    sectionConormalMap φ α U (Ideal.toCotangent (conormalIdeal α U) x) =
      (1 : O₂'.obj.obj U) ⊗ₜ[O₂.obj.obj U]
        KaehlerDifferential.D (O₁.obj.obj U) (O₂.obj.obj U) x := by
  let _ : Algebra (O₁.obj.obj U) (O₂.obj.obj U) := ((φ.hom.app U).hom).toAlgebra
  let _ : Algebra (O₂.obj.obj U) (O₂'.obj.obj U) := ((α.hom.app U).hom).toAlgebra
  let x' : RingHom.ker (algebraMap (O₂.obj.obj U) (O₂'.obj.obj U)) := x
  -- Proof comment: `conormalIdeal α U` is definitionally the kernel ideal of the section ring
  -- map, so the textbook formula is exactly the owner theorem on generators.
  change
    KaehlerDifferential.kerCotangentToTensor
        (O₁.obj.obj U) (O₂.obj.obj U) (O₂'.obj.obj U)
        (Ideal.toCotangent
          (RingHom.ker (algebraMap (O₂.obj.obj U) (O₂'.obj.obj U))) x') =
      (1 : O₂'.obj.obj U) ⊗ₜ[O₂.obj.obj U]
        KaehlerDifferential.D (O₁.obj.obj U) (O₂.obj.obj U) x'
  exact KaehlerDifferential.kerCotangentToTensor_toCotangent
    (O₁.obj.obj U) (O₂.obj.obj U) (O₂'.obj.obj U) x'

end SheafOfModules.RingedSite
