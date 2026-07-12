import Mathlib
import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap10.Lemma_10_134_4_Jacobi_Zariski_sequence
import StacksProject_2024.Chap10.Remark_10_134_5
import StacksProject_2024.Chap13.Lemma_13_9_3
import StacksProject_2024.Chap17.Lemma_17_28_8
import StacksProject_2024.Chap18.RingedSiteModuleCategory

open PresheafOfModules.DifferentialsConstruction
open CategoryTheory CategoryTheory.Limits TopCat ComplexShape
open SheafOfModules.RingedSite
open scoped SheafOfModules.RingedSite TensorProduct

noncomputable section

universe u

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J (Type u)]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasBinaryCoproducts (Sheaf J CommRingCat.{u})]

/-- Helper for Lemma 17.31.5: the underlying sheaf of sets of an `𝒜`-algebra sheaf. -/
abbrev presentationVariables
    {𝒜 : Sheaf J CommRingCat.{u}}
    (𝒝 : Under 𝒜) :
    Sheaf J (Type u) :=
  (sheafForget J).obj 𝒝.right

/-- Helper for Lemma 17.31.5: the free commutative ring sheaf on a sheaf of sets. -/
abbrev presentationFreeSheaf
    (E : Sheaf J (Type u)) :
    Sheaf J CommRingCat.{u} :=
  (Sheaf.composeAndSheafify J CommRingCat.free).obj E

/-- Helper for Lemma 17.31.5: the free `𝒜`-algebra sheaf on `E`. -/
abbrev presentationSheafOf
    (𝒜 : Sheaf J CommRingCat.{u})
    (E : Sheaf J (Type u)) :
    Sheaf J CommRingCat.{u} :=
  ((Under.costar 𝒜).obj (presentationFreeSheaf E)).right

scoped[SheafOfModules.RingedSite] notation:max 𝒜:max "[" E "]" =>
  presentationSheafOf 𝒜 E

open scoped SheafOfModules.RingedSite

/-- Helper for Lemma 17.31.5: the structure morphism `𝒜 ⟶ 𝒜[E]`. -/
abbrev presentationBaseOf
    (𝒜 : Sheaf J CommRingCat.{u})
    (E : Sheaf J (Type u)) :
    𝒜 ⟶ 𝒜[E] :=
  ((Under.costar 𝒜).obj (presentationFreeSheaf E)).hom

/-- Helper for Lemma 17.31.5: the free evaluation map induced by a map of generators. -/
private abbrev presentationFreeMap
    {𝒜 : Sheaf J CommRingCat.{u}}
    (𝒝 : Under 𝒜)
    (E : Sheaf J (Type u))
    (α : E ⟶ presentationVariables 𝒝) :
    presentationFreeSheaf E ⟶ 𝒝.right :=
  ((Sheaf.adjunction J CommRingCat.adj).homEquiv E 𝒝.right).symm α

/-- Helper for Lemma 17.31.5: the induced `𝒜`-algebra map `𝒜[E] ⟶ 𝒝`. -/
abbrev presentationMapOf
    (𝒜 : Sheaf J CommRingCat.{u})
    (𝒝 : Under 𝒜)
    (E : Sheaf J (Type u))
    (α : E ⟶ presentationVariables 𝒝) :
    𝒜[E] ⟶ 𝒝.right :=
  (((Under.costarAdjForget 𝒜).homEquiv
      (presentationFreeSheaf E) 𝒝).symm
      (presentationFreeMap 𝒝 E α)).right

/-- Helper for Lemma 17.31.5: the base map of an induced presentation morphism is the chosen
coefficient map. -/
theorem presentationBaseOf_comp_presentationMapOf
    {𝒜 : Sheaf J CommRingCat.{u}}
    (𝒝 : Under 𝒜)
    (E : Sheaf J (Type u))
    (α : E ⟶ presentationVariables 𝒝) :
    presentationBaseOf 𝒜 E ≫ presentationMapOf 𝒜 𝒝 E α = 𝒝.hom := by
  -- Proof comment: first rewrite the free map adjoint to `α` through the unit of
  -- `Under.costarAdjForget`, then project the resulting equality to the right component.
  let u := ((Sheaf.adjunction J CommRingCat.adj).homEquiv E 𝒝.right).symm α
  have hu :
      u = ((Under.costarAdjForget 𝒜).unit.app (presentationFreeSheaf E)) ≫
        (((Under.costarAdjForget 𝒜).homEquiv (presentationFreeSheaf E) 𝒝).symm u).right := by
    -- Proof comment: this is the unit identity for the adjunction `Under.costarAdjForget 𝒜`.
    simpa using
      (Adjunction.homEquiv_unit (adj := Under.costarAdjForget 𝒜)
        (X := presentationFreeSheaf E) (Y := 𝒝)
        (f := (((Under.costarAdjForget 𝒜).homEquiv (presentationFreeSheaf E) 𝒝).symm u)))
  -- Proof comment: unfold the two presentation maps and substitute the specialized unit formula.
  dsimp [presentationBaseOf, presentationMapOf, presentationFreeMap, u]
  exact hu

/-- Helper for Lemma 17.31.5: the canonical presentation sheaf `𝒜[𝒝]`. -/
abbrev presentationSheaf
    (𝒜 : Sheaf J CommRingCat.{u})
    (𝒝 : Under 𝒜) :
    Sheaf J CommRingCat.{u} :=
  presentationSheafOf 𝒜 (presentationVariables 𝒝)

scoped[SheafOfModules.RingedSite] notation:max 𝒜:max "[" 𝒝 "]" =>
  presentationSheaf 𝒜 𝒝

/-- Helper for Lemma 17.31.5: the base map of the canonical presentation. -/
abbrev presentationBase
    (𝒜 : Sheaf J CommRingCat.{u}) (𝒝 : Under 𝒜) :
    𝒜 ⟶ 𝒜[𝒝] :=
  presentationBaseOf 𝒜 (presentationVariables 𝒝)

/-- Helper for Lemma 17.31.5: the canonical presentation morphism `𝒜[𝒝] ⟶ 𝒝`. -/
abbrev presentationMap
    (𝒜 : Sheaf J CommRingCat.{u}) (𝒝 : Under 𝒜) :
    𝒜[𝒝] ⟶ 𝒝.right :=
  presentationMapOf 𝒜 𝒝 (presentationVariables 𝒝) (𝟙 _)

variable {O₁ O₂ O₃ : Sheaf J CommRingCat.{u}}

/-- Helper for Lemma 17.31.5: the scalar presheaf obtained from `O₃` by restricting scalars
along `α`. -/
private abbrev conormalScalarPresheaf
    (α : O₂ ⟶ O₃) :
    PresheafOfModules (ringSheaf J O₂).obj :=
  (PresheafOfModules.restrictScalars (ringSheafMap α).hom).obj
    (PresheafOfModules.unit (ringSheaf J O₃).obj)

/-- Helper for Lemma 17.31.5: the source-side tensor presheaf
`O₃ ⊗[O₂] Ω(O₂/O₁)` before sheafification. -/
private abbrev conormalTensorSpacePresheaf
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) :
    PresheafOfModules (ringSheaf J O₂).obj :=
  PresheafOfModules.Monoidal.tensorObj
    (conormalScalarPresheaf α)
    (relativeDifferentials' φ.hom)

/-- Helper for Lemma 17.31.5: the source-side tensor term before pulling back along `α`. -/
private abbrev conormalTensorTermOverSource
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) :
    SheafOfModules (ringSheaf J O₂) :=
  (PresheafOfModules.sheafification
      (𝟙 (ringSheaf J O₂).obj)).obj
    (conormalTensorSpacePresheaf φ α)

/-- Helper for Lemma 17.31.5: the kernel ideal of `α` on sections over `U`. -/
private abbrev conormalIdeal
    (α : O₂ ⟶ O₃) (U : Cᵒᵖ) :
    Ideal (O₂.obj.obj U) :=
  RingHom.ker ((α.hom.app U).hom)

/-- Helper for Lemma 17.31.5: restriction maps carry the kernel ideal of `α` into itself. -/
private theorem conormalIdeal_le_comap
    (α : O₂ ⟶ O₃) {U V : Cᵒᵖ} (i : U ⟶ V) :
    conormalIdeal α U ≤
      (conormalIdeal α V).comap ((O₂.obj.map i).hom) := by
  intro x hx
  -- Proof comment: kernel membership is preserved by naturality of the sheaf morphism `α`.
  change (α.hom.app V).hom ((O₂.obj.map i).hom x) = 0
  have hnat :=
    DFunLike.congr_fun
      (congrArg CommRingCat.Hom.hom (α.hom.naturality i)) x
  have hx' : (α.hom.app U).hom x = 0 := hx
  simpa [hx'] using hnat

/-- Helper for Lemma 17.31.5: the cotangent module `(Ker α)/(Ker α)^2` on sections over `U`. -/
private abbrev conormalObj
    (α : O₂ ⟶ O₃) (U : Cᵒᵖ) :
    ModuleCat (O₂.obj.obj U) :=
  ModuleCat.of (O₂.obj.obj U) (conormalIdeal α U).Cotangent

/-- Helper for Lemma 17.31.5: the restriction map on the source-side conormal cotangent modules. -/
private abbrev conormalRestriction
    (α : O₂ ⟶ O₃) {U V : Cᵒᵖ} (i : U ⟶ V) :
    conormalObj α U ⟶
      (ModuleCat.restrictScalars
        (((ringSheaf J O₂).obj.map i).hom)).obj
        (conormalObj α V) :=
  let _ : Algebra (O₂.obj.obj U) (O₂.obj.obj V) := (O₂.obj.map i).hom.toAlgebra
  ModuleCat.ofHom
    (Ideal.mapCotangent
      (conormalIdeal α U)
      (conormalIdeal α V)
      { toRingHom := (O₂.obj.map i).hom
        commutes' := by
          intro r
          rfl }
      (conormalIdeal_le_comap α i))

/-- Helper for Lemma 17.31.5: the conormal restriction sends a cotangent generator to the
generator induced by restricting its representative section. -/
private theorem conormalRestriction_toCotangent
    (α : O₂ ⟶ O₃) {U V : Cᵒᵖ} (i : U ⟶ V) (x : conormalIdeal α U) :
    conormalRestriction α i ((conormalIdeal α U).toCotangent x) =
      (conormalIdeal α V).toCotangent
        ⟨((O₂.obj.map i).hom) x, conormalIdeal_le_comap α i x.2⟩ := by
  let _ : Algebra (O₂.obj.obj U) (O₂.obj.obj V) := (O₂.obj.map i).hom.toAlgebra
  -- Proof comment: this is the defining generator formula for `Ideal.mapCotangent`.
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

/-- Helper for Lemma 17.31.5: the conormal restriction is functorial with respect to identity
maps. -/
private theorem conormalRestriction_id
    (α : O₂ ⟶ O₃) (U : Cᵒᵖ) :
    conormalRestriction α (𝟙 U) =
      (ModuleCat.restrictScalarsId'
        (((ringSheaf J O₂).obj.map (𝟙 U)).hom)
        (congrArg RingCat.Hom.hom
          ((ringSheaf J O₂).obj.map_id U))).inv.app _ := by
  -- Proof comment: compare both maps on cotangent generators and use the identity restriction.
  refine ModuleCat.hom_ext ?_
  ext z
  obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective (conormalIdeal α U) z
  have hmap :
      ((O₂.obj.map (𝟙 U)).hom) (x : O₂.obj.obj U) = x := by
    simpa using congrArg (fun h ↦ h (x : O₂.obj.obj U))
      (congrArg RingCat.Hom.hom ((ringSheaf J O₂).obj.map_id U))
  have hx :
      (conormalIdeal α U).toCotangent
          ⟨((O₂.obj.map (𝟙 U)).hom) x, conormalIdeal_le_comap α (𝟙 U) x.2⟩ =
        (conormalIdeal α U).toCotangent x := by
    exact congrArg (Ideal.toCotangent (conormalIdeal α U)) (Subtype.ext hmap)
  -- Proof comment: after rewriting by the identity restriction, both maps are definitionally
  -- the same cotangent generator.
  rw [conormalRestriction_toCotangent]
  rw [hx]
  symm
  exact ModuleCat.restrictScalarsId'App_inv_apply
    (((ringSheaf J O₂).obj.map (𝟙 U)).hom)
    (congrArg RingCat.Hom.hom ((ringSheaf J O₂).obj.map_id U))
    (conormalObj α U)
    ((conormalIdeal α U).toCotangent x)

/-- Helper for Lemma 17.31.5: the conormal restriction composition formula on cotangent
generators. -/
private theorem conormalRestriction_comp_on_toCotangent
    (α : O₂ ⟶ O₃) {U V W : Cᵒᵖ} (i : U ⟶ V) (j : V ⟶ W)
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
    simpa using congrArg (fun h ↦ h (x : O₂.obj.obj U))
      (congrArg RingCat.Hom.hom ((ringSheaf J O₂).obj.map_comp i j))
  -- Proof comment: both sides reduce to the same restricted cotangent generator.
  rw [conormalRestriction_toCotangent]
  simp only [conormalRestriction_toCotangent, ModuleCat.restrictScalarsComp'App_inv_apply]
  exact congrArg (Ideal.toCotangent (conormalIdeal α W)) (Subtype.ext hmap)

/-- Helper for Lemma 17.31.5: the conormal restriction maps satisfy the presheaf composition
law. -/
private theorem conormalRestriction_comp
    (α : O₂ ⟶ O₃) {U V W : Cᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) :
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
  -- Proof comment: equality of morphisms out of the cotangent module is determined on
  -- cotangent generators.
  apply ModuleCat.hom_ext
  ext z
  obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective (conormalIdeal α U) z
  simpa using conormalRestriction_comp_on_toCotangent α i j x

/-- Helper for Lemma 17.31.5: the source-side conormal presheaf. -/
private def conormalPresheaf
    (α : O₂ ⟶ O₃) :
    PresheafOfModules (ringSheaf J O₂).obj :=
  { obj := conormalObj α
    map := conormalRestriction α
    map_id := conormalRestriction_id α
    map_comp := conormalRestriction_comp α }

/-- Helper for Lemma 17.31.5: the conormal source sheaf before extending scalars to `O₃`. -/
private noncomputable def conormalSourceOverSource
    (α : O₂ ⟶ O₃) :
    SheafOfModules (ringSheaf J O₂) :=
  (PresheafOfModules.sheafification
      (𝟙 (ringSheaf J O₂).obj)).obj
    (conormalPresheaf α)

/-- Helper for Lemma 17.31.5: pullback of `O₂`-module sheaves along the structure map
`O₂ ⟶ O₃`. -/
private abbrev conormalPullback
    (α : O₂ ⟶ O₃) :
    SheafOfModules (ringSheaf J O₂) ⥤
      SheafOfModules (ringSheaf J O₃) :=
  SheafOfModules.pullback (ringedSiteStructureMap α)

/-- Helper for Lemma 17.31.5: the conormal source term of a presentation map. -/
abbrev conormalSource
    (α : O₂ ⟶ O₃) :
    SheafOfModules (ringSheaf J O₃) :=
  (conormalPullback α).obj (conormalSourceOverSource α)

/-- Helper for Lemma 17.31.5: the tensor term `O₃ ⊗[O₂] Ω(O₂/O₁)` attached to a presentation. -/
abbrev conormalTensorTerm
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) :
    SheafOfModules (ringSheaf J O₃) :=
  (conormalPullback α).obj (conormalTensorTermOverSource φ α)

/-- Helper for Lemma 17.31.5: the objectwise conormal map on sections over `U`. -/
private abbrev sectionConormalMap
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) (U : Cᵒᵖ) :
    let _ : Algebra (O₁.obj.obj U) (O₂.obj.obj U) := ((φ.hom.app U).hom).toAlgebra
    let _ : Algebra (O₂.obj.obj U) (O₃.obj.obj U) := ((α.hom.app U).hom).toAlgebra
    (RingHom.ker ((α.hom.app U).hom)).Cotangent →ₗ[O₂.obj.obj U]
      O₃.obj.obj U ⊗[O₂.obj.obj U] Ω[O₂.obj.obj U⁄O₁.obj.obj U] :=
  let _ : Algebra (O₁.obj.obj U) (O₂.obj.obj U) := ((φ.hom.app U).hom).toAlgebra
  let _ : Algebra (O₂.obj.obj U) (O₃.obj.obj U) := ((α.hom.app U).hom).toAlgebra
  KaehlerDifferential.kerCotangentToTensor
    (O₁.obj.obj U) (O₂.obj.obj U) (O₃.obj.obj U)

/-- Helper for Lemma 17.31.5: the wrapped sectionwise conormal map into the tensor presheaf. -/
private abbrev sectionConormalHom
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) (U : Cᵒᵖ) :
    conormalObj α U ⟶
      (conormalTensorSpacePresheaf φ α).obj U := by
  let _ : Algebra (O₁.obj.obj U) (O₂.obj.obj U) := ((φ.hom.app U).hom).toAlgebra
  let _ : Algebra (O₂.obj.obj U) (O₃.obj.obj U) := ((α.hom.app U).hom).toAlgebra
  change conormalObj α U ⟶
    ModuleCat.of (O₂.obj.obj U)
      (O₃.obj.obj U ⊗[O₂.obj.obj U] Ω[O₂.obj.obj U⁄O₁.obj.obj U])
  exact ModuleCat.ofHom (sectionConormalMap φ α U)

/-- Helper for Lemma 17.31.5: on cotangent generators, the wrapped conormal map sends `[x]` to
`1 ⊗ d x`. -/
private theorem sectionConormalHom_on_toCotangent
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) (U : Cᵒᵖ) (x : conormalIdeal α U) :
    let _ : Algebra (O₁.obj.obj U) (O₂.obj.obj U) := ((φ.hom.app U).hom).toAlgebra
    let _ : Algebra (O₂.obj.obj U) (O₃.obj.obj U) := ((α.hom.app U).hom).toAlgebra
    sectionConormalHom φ α U ((conormalIdeal α U).toCotangent x) =
      (1 : O₃.obj.obj U) ⊗ₜ[O₂.obj.obj U]
        KaehlerDifferential.D (O₁.obj.obj U) (O₂.obj.obj U) x := by
  let _ : Algebra (O₁.obj.obj U) (O₂.obj.obj U) := ((φ.hom.app U).hom).toAlgebra
  let _ : Algebra (O₂.obj.obj U) (O₃.obj.obj U) := ((α.hom.app U).hom).toAlgebra
  let x' : RingHom.ker (algebraMap (O₂.obj.obj U) (O₃.obj.obj U)) := x
  -- Proof comment: this is the ring-level generator formula for
  -- `KaehlerDifferential.kerCotangentToTensor`.
  change
    KaehlerDifferential.kerCotangentToTensor
        (O₁.obj.obj U) (O₂.obj.obj U) (O₃.obj.obj U)
        (Ideal.toCotangent
          (RingHom.ker (algebraMap (O₂.obj.obj U) (O₃.obj.obj U))) x') =
      (1 : O₃.obj.obj U) ⊗ₜ[O₂.obj.obj U]
        KaehlerDifferential.D (O₁.obj.obj U) (O₂.obj.obj U) x'
  exact KaehlerDifferential.kerCotangentToTensor_toCotangent
    (O₁.obj.obj U) (O₂.obj.obj U) (O₃.obj.obj U) x'

/-- Helper for Lemma 17.31.5: restricting scalars along `α` does not change the underlying
section restriction map on the `O₃`-factor. -/
private theorem conormalScalarPresheaf_map_apply
    (α : O₂ ⟶ O₃) {U V : Cᵒᵖ} (i : U ⟶ V) (b : O₃.obj.obj U) :
    (ConcreteCategory.hom ((conormalScalarPresheaf α).map i)) b =
      (O₃.obj.map i).hom b := by
  -- Proof comment: this is definitional because only the scalar structure changes.
  rfl

/-- Helper for Lemma 17.31.5: the tensor-presheaf restriction map sends pure tensors to the
restricted pure tensors. -/
private theorem conormalTensorSpacePresheaf_map_tmul
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) {U V : Cᵒᵖ} (i : U ⟶ V)
    (b : O₃.obj.obj U) (x : O₂.obj.obj U) :
    let _ : Algebra (O₁.obj.obj U) (O₂.obj.obj U) := ((φ.hom.app U).hom).toAlgebra
    let _ : Algebra (O₂.obj.obj U) (O₃.obj.obj U) := ((α.hom.app U).hom).toAlgebra
    let _ : Algebra (O₁.obj.obj V) (O₂.obj.obj V) := ((φ.hom.app V).hom).toAlgebra
    let _ : Algebra (O₂.obj.obj V) (O₃.obj.obj V) := ((α.hom.app V).hom).toAlgebra
    ((conormalTensorSpacePresheaf φ α).map i).hom
        (b ⊗ₜ[O₂.obj.obj U]
          KaehlerDifferential.D (O₁.obj.obj U) (O₂.obj.obj U) x) =
      ((O₃.obj.map i).hom b) ⊗ₜ[O₂.obj.obj V]
        KaehlerDifferential.D (O₁.obj.obj V) (O₂.obj.obj V) ((O₂.obj.map i).hom x) := by
  -- Proof comment: the tensor restriction is computed componentwise on pure tensors.
  rw [PresheafOfModules.Monoidal.tensorObj_map_tmul]
  rw [conormalScalarPresheaf_map_apply]
  simpa using relativeDifferentials'_map_d φ.hom i x

/-- Helper for Lemma 17.31.5: the wrapped sectionwise conormal maps are natural in the opens
variable. -/
private theorem sectionConormalHom_naturality
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) {U V : Cᵒᵖ} (i : U ⟶ V) :
    (conormalPresheaf α).map i ≫
        (ModuleCat.restrictScalars
          (((ringSheaf J O₂).obj.map i).hom)).map
          (sectionConormalHom φ α V) =
      sectionConormalHom φ α U ≫
        (conormalTensorSpacePresheaf φ α).map i := by
  apply ModuleCat.hom_ext
  ext z
  -- Proof comment: the conormal cotangent module is generated by kernel classes, so it is
  -- enough to compare the two branches on one generator.
  obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective (conormalIdeal α U) z
  rw [LinearMap.comp_apply]
  rw [conormalRestriction_toCotangent]
  rw [sectionConormalHom_on_toCotangent]
  rw [sectionConormalHom_on_toCotangent]
  simpa using
    conormalTensorSpacePresheaf_map_tmul φ α i (1 : O₃.obj.obj U) (x : O₂.obj.obj U)

/-- Helper for Lemma 17.31.5: the presheaf-level conormal morphism before sheafification. -/
private def conormalPresheafHom
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) :
    conormalPresheaf α ⟶ conormalTensorSpacePresheaf φ α where
  app U := sectionConormalHom φ α U
  naturality i := sectionConormalHom_naturality φ α i

/-- Helper for Lemma 17.31.5: the source-side conormal map before scalar extension to `O₃`. -/
private noncomputable def conormalMapOverSource
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) :
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

/-- Helper for Lemma 17.31.5: the left differential of the two-term naive cotangent complex. -/
noncomputable def conormalMap
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) :
    conormalSource α ⟶ conormalTensorTerm φ α :=
  -- Proof comment: first build the conormal morphism before scalar extension on the source side,
  -- then pull it back along `α` to the target-side module category.
  (conormalPullback α).map (conormalMapOverSource φ α)

/-- Helper for Lemma 17.31.5: the term function of the presentationwise naive cotangent complex. -/
private abbrev presentationNaiveCotangentTerm
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) :
    ℤ → SheafOfModules (ringSheaf J O₃)
  | Int.negSucc 0 => conormalSource α
  | Int.ofNat 0 => conormalTensorTerm φ α
  | _ => 0

/-- Helper for Lemma 17.31.5: the differential of the presentationwise naive cotangent complex. -/
private noncomputable def presentationNaiveCotangentDifferential
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) (n : ℤ) :
    presentationNaiveCotangentTerm φ α n ⟶
      presentationNaiveCotangentTerm φ α (n + 1) :=
  match n with
  | Int.negSucc 0 => by
      simpa [presentationNaiveCotangentTerm] using conormalMap φ α
  | Int.negSucc 1 => by
      change (0 : SheafOfModules (ringSheaf J O₃)) ⟶ conormalSource α
      exact 0
  | Int.negSucc (_ + 2) => by
      change (0 : SheafOfModules (ringSheaf J O₃)) ⟶ 0
      exact 0
  | Int.ofNat 0 => by
      change conormalTensorTerm φ α ⟶ (0 : SheafOfModules (ringSheaf J O₃))
      exact 0
  | Int.ofNat (_ + 1) => by
      change (0 : SheafOfModules (ringSheaf J O₃)) ⟶ 0
      exact 0

/-- Helper for Lemma 17.31.5: the differential squares to zero because the complex is
concentrated in degrees `-1` and `0`. -/
private theorem presentationNaiveCotangent_sq_zero
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) (n : ℤ) :
    presentationNaiveCotangentDifferential φ α n ≫
      presentationNaiveCotangentDifferential φ α (n + 1) = 0 :=
  match n with
  | Int.negSucc 0 => by
      change conormalMap φ α ≫
          (0 : conormalTensorTerm φ α ⟶ (0 : SheafOfModules (ringSheaf J O₃))) = 0
      exact comp_zero
  | Int.negSucc 1 => by
      change (0 : (0 : SheafOfModules (ringSheaf J O₃)) ⟶ conormalSource α) ≫
          conormalMap φ α = 0
      exact zero_comp
  | Int.negSucc 2 => by
      change (0 : (0 : SheafOfModules (ringSheaf J O₃)) ⟶ 0) ≫
          (0 : (0 : SheafOfModules (ringSheaf J O₃)) ⟶ conormalSource α) = 0
      rfl
  | Int.negSucc (_ + 3) => by
      change (0 : (0 : SheafOfModules (ringSheaf J O₃)) ⟶ 0) ≫
          (0 : (0 : SheafOfModules (ringSheaf J O₃)) ⟶ 0) = 0
      simp
  | Int.ofNat 0 => by
      change (0 : conormalTensorTerm φ α ⟶ (0 : SheafOfModules (ringSheaf J O₃))) ≫
          (0 : (0 : SheafOfModules (ringSheaf J O₃)) ⟶ 0) = 0
      rfl
  | Int.ofNat (_ + 1) => by
      change (0 : (0 : SheafOfModules (ringSheaf J O₃)) ⟶ 0) ≫
          (0 : (0 : SheafOfModules (ringSheaf J O₃)) ⟶ 0) = 0
      simp

/-- Helper for Lemma 17.31.5: the two-term naive cotangent complex attached to a presentation. -/
noncomputable abbrev presentationNaiveCotangent
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) :
    CochainComplex (SheafOfModules (ringSheaf J O₃)) ℤ :=
  CochainComplex.of
    (presentationNaiveCotangentTerm φ α)
    (presentationNaiveCotangentDifferential φ α)
    (presentationNaiveCotangent_sq_zero φ α)

variable (𝒜 : Sheaf J CommRingCat.{u}) (𝒝 : Under 𝒜)

/-- Helper for Lemma 17.31.5: the naive cotangent complex of `𝒝` over `𝒜`, built from the
canonical presentation. -/
noncomputable abbrev naiveCotangent :
    CochainComplex (SheafOfModules (ringSheaf J 𝒝.right)) ℤ :=
  presentationNaiveCotangent (presentationBase 𝒜 𝒝) (presentationMap 𝒜 𝒝)

/-- Helper for Lemma 17.31.5: the degree `-1` term of the naive cotangent complex is the
conormal source term of the canonical presentation. -/
theorem naiveCotangent_X_negOne :
    (naiveCotangent 𝒜 𝒝).X (-1) =
      conormalSource (presentationMap 𝒜 𝒝) := by
  rfl

/-- Helper for Lemma 17.31.5: the degree `0` term of the naive cotangent complex is the tensor
term of the canonical presentation. -/
theorem naiveCotangent_X_zero :
    (naiveCotangent 𝒜 𝒝).X 0 =
      conormalTensorTerm (presentationBase 𝒜 𝒝) (presentationMap 𝒜 𝒝) := by
  rfl

end SheafOfModules.RingedSite

namespace TopCat.Sheaf

variable {X : TopCat.{u}}
variable {O₁ O₂ O₃ : X.Sheaf CommRingCat.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) CommRingCat.{u}]
variable [(Opens.grothendieckTopology X).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [(Opens.grothendieckTopology X).HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasBinaryCoproducts (CategoryTheory.Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})]

private instance topCatSheaf_hasBinaryCoproducts :
    HasBinaryCoproducts (TopCat.Sheaf CommRingCat.{u} X) := by
  simpa [TopCat.Sheaf] using
    (inferInstance :
      HasBinaryCoproducts
        (CategoryTheory.Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}))

private instance pullback_preservesZeroMorphisms (α : O₂ ⟶ O₃) :
    (SheafOfModules.pullback (ringedSiteStructureMap α)).PreservesZeroMorphisms := by
  infer_instance

/-- Helper for Lemma 17.31.5: the opens-site point-stalk functor on `O`-modules is exact. -/
theorem opensPointSheafModuleStalkExact
    (O : X.Sheaf CommRingCat.{u}) (x : X) :
    exactFunctor
      (Mod (ringSheaf O))
      (ModuleCat ((Opens.pointGrothendieckTopology x).stalkRing (ringSheaf O)))
      ((Opens.pointGrothendieckTopology x).sheafModuleStalkFunctor (ringSheaf O)) := by
  let p : GrothendieckTopology.Point (Opens.grothendieckTopology X) :=
    Opens.pointGrothendieckTopology x
  let G :
      ModuleCat (p.stalkRing (ringSheaf O)) ⥤ AddCommGrpCat.{u} :=
    forget₂ _ _
  -- Proof comment: after forgetting the module structure over the stalk ring, this is the usual
  -- additive stalk functor on sheaves, whose exactness is already canonical.
  have hlim : PreservesFiniteLimits (p.sheafModuleStalkFunctor (ringSheaf O)) := by
    have :
        PreservesFiniteLimits
          (p.sheafModuleStalkFunctor (ringSheaf O) ⋙ G) := by
      have hToSheaf :
          exactFunctor
            (Mod (ringSheaf O))
            (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
            (SheafOfModules.toSheaf (ringSheaf O)) :=
        (ExactFunctor.of (SheafOfModules.toSheaf (ringSheaf O))).property
      have hFiber :
          exactFunctor
            (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
            AddCommGrpCat.{u}
            p.sheafFiber :=
        (ExactFunctor.of p.sheafFiber).property
      let _ : PreservesFiniteLimits (SheafOfModules.toSheaf (ringSheaf O)) :=
        ((exactFunctor_iff (SheafOfModules.toSheaf (ringSheaf O))).1 hToSheaf).1
      let _ : PreservesFiniteLimits p.sheafFiber :=
        ((exactFunctor_iff p.sheafFiber).1 hFiber).1
      change PreservesFiniteLimits (SheafOfModules.toSheaf (ringSheaf O) ⋙ p.sheafFiber)
      infer_instance
    exact preservesFiniteLimits_of_reflects_of_preserves
      (p.sheafModuleStalkFunctor (ringSheaf O)) G
  -- Proof comment: the same reflection argument upgrades finite-colimit preservation from the
  -- additive stalk functor to the module-valued stalk functor.
  have hcolim : PreservesFiniteColimits (p.sheafModuleStalkFunctor (ringSheaf O)) := by
    have :
        PreservesFiniteColimits
          (p.sheafModuleStalkFunctor (ringSheaf O) ⋙ G) := by
      have hToSheaf :
          exactFunctor
            (Mod (ringSheaf O))
            (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
            (SheafOfModules.toSheaf (ringSheaf O)) :=
        (ExactFunctor.of (SheafOfModules.toSheaf (ringSheaf O))).property
      have hFiber :
          exactFunctor
            (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
            AddCommGrpCat.{u}
            p.sheafFiber :=
        (ExactFunctor.of p.sheafFiber).property
      let _ : PreservesFiniteColimits (SheafOfModules.toSheaf (ringSheaf O)) :=
        ((exactFunctor_iff (SheafOfModules.toSheaf (ringSheaf O))).1 hToSheaf).2
      let _ : PreservesFiniteColimits p.sheafFiber :=
        ((exactFunctor_iff p.sheafFiber).1 hFiber).2
      change PreservesFiniteColimits (SheafOfModules.toSheaf (ringSheaf O) ⋙ p.sheafFiber)
      infer_instance
    exact preservesFiniteColimits_of_reflects_of_preserves
      (p.sheafModuleStalkFunctor (ringSheaf O)) G
  -- Proof comment: in the abelian module category, exactness is equivalent to preserving finite
  -- limits and finite colimits.
  exact (exactFunctor_iff (p.sheafModuleStalkFunctor (ringSheaf O))).2 ⟨hlim, hcolim⟩

/- Domain-style sampling for Lemma 17.31.5:
- primary domain: transitivity for naive cotangent complexes of a tower of sheaves of rings on the
  opens site of a topological space;
- sampled owner declarations:
  `SheafOfModules.RingedSite.naiveCotangent`,
  `SheafOfModules.pullback`,
  `SheafOfModules.RingedSite.ringedSiteStructureMap`,
  `TopCat.Sheaf.relativeDifferentialsMap`,
  `TopCat.Sheaf.naiveCotangent_six_term_segment_exact`,
  `AlgebraicGeometry.RingedSpace.relativeDifferentialsTransitivity`;
- best owner abstraction: as for the transitivity sequence for relative differentials, the
  source-facing owner in this file is the existence statement for a transitivity comparison
  `NL_{\mathcal O_3/\mathcal O_1} ⟶ NL_{\mathcal O_3/\mathcal O_2}` together with a transitivity
  map
  `\alpha^* NL_{\mathcal O_2/\mathcal O_1} ⟶ Cone(NL_{\mathcal O_3/\mathcal O_1} ⟶
    NL_{\mathcal O_3/\mathcal O_2})[-1]`;
- primitive data: only the tower `\mathcal O_1 ⟶ \mathcal O_2 ⟶ \mathcal O_3`;
- derived API: the `H^0` isomorphism, the `H^{-1}` epimorphism, and the six-term exact segment
  obtained from the Chapter 17 owner `TopCat.Sheaf.naiveCotangent_six_term_segment_exact`.

Source/core/bridge triage:
- `source-facing`: the existence of a transitivity comparison and a transitivity map to the
  mapping cocone for the tower `\mathcal O_1 ⟶ \mathcal O_2 ⟶ \mathcal O_3`;
- `core/canonical`: `naiveCotangent`, `SheafOfModules.pullback`,
  `ringedSiteStructureMap`, `relativeDifferentialsMap`, `mappingCocone`,
  `HomologicalComplex.homologyMap`, and `TopCat.Sheaf.naiveCotangent_six_term_segment_exact`;
- `bridge/view`: this file specializes the owner theorem `17.31.7` to the opens-site tower
  `\mathcal O_1 ⟶ \mathcal O_2 ⟶ \mathcal O_3`, so its public surface should keep the
  source-faithful existence and exactness statements and avoid exporting chosen witnesses as
  canonical named morphisms.
  -/

/-- Helper for Lemma 17.31.5: the pulled-back naive cotangent complex on the left-hand side of the
transitivity triangle. -/
abbrev naiveCotangentTransitivityPullback
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) :
    moduleComplex O₃ :=
  (((SheafOfModules.pullback (ringedSiteStructureMap α)).mapHomologicalComplex (up ℤ)).obj
    (naiveCotangent O₁ (Under.mk φ)))

/-- Helper for Lemma 17.31.5: the degree `-1` term of the pulled-back left complex is the
pullback of the conormal source term of `NL_{\mathcal O_2/\mathcal O_1}`. -/
theorem naiveCotangentTransitivityPullback_X_negOne
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) :
    (naiveCotangentTransitivityPullback φ α).X (-1) =
      (SheafOfModules.pullback (ringedSiteStructureMap α)).obj
        (conormalSource (presentationMap O₁ (Under.mk φ))) := by
  -- The pullback commutes with evaluation on the degree `-1` term of the two-term complex.
  simp [naiveCotangentTransitivityPullback, SheafOfModules.RingedSite.naiveCotangent_X_negOne]

/-- Helper for Lemma 17.31.5: the degree `0` term of the pulled-back left complex is the
pullback of the tensor term of `NL_{\mathcal O_2/\mathcal O_1}`. -/
theorem naiveCotangentTransitivityPullback_X_zero
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) :
    (naiveCotangentTransitivityPullback φ α).X 0 =
      (SheafOfModules.pullback (ringedSiteStructureMap α)).obj
        (conormalTensorTerm (presentationBase O₁ (Under.mk φ))
          (presentationMap O₁ (Under.mk φ))) := by
  -- The same evaluation step identifies the pulled-back degree `0` term.
  simp [naiveCotangentTransitivityPullback, SheafOfModules.RingedSite.naiveCotangent_X_zero]

/-- Helper for Lemma 17.31.5: the differential `-1 → 0` of the pulled-back left complex is the
pullback of the canonical conormal map of `NL_{\mathcal O_2/\mathcal O_1}`. -/
theorem naiveCotangentTransitivityPullback_d_negOne_zero
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) :
    (naiveCotangentTransitivityPullback φ α).d (-1) 0 =
      (SheafOfModules.pullback (ringedSiteStructureMap α)).map
        (conormalMap (presentationBase O₁ (Under.mk φ))
          (presentationMap O₁ (Under.mk φ))) := by
  -- The differential of a mapped cochain complex is obtained by mapping the source differential.
  rfl

/-- Helper for Lemma 17.31.5: the pulled-back left naive cotangent complex is concentrated in
degrees `-1` and `0`, so its degree `1` term is zero. -/
theorem naiveCotangentTransitivityPullback_X_one
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) :
    (naiveCotangentTransitivityPullback φ α).X 1 = 0 := by
  -- The pullback preserves the two-term shape of `NL_{\mathcal O_2/\mathcal O_1}`.
  simp [naiveCotangentTransitivityPullback, SheafOfModules.RingedSite.naiveCotangent]

/-- Helper for Lemma 17.31.5: the canonical map of polynomial presentations
`\mathcal O_1[\mathcal O_3] \to \mathcal O_2[\mathcal O_3]` induced by the coefficient map `φ`
and the identity on the `\mathcal O_3`-generators. -/
abbrev presentation_transitivity_map
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) :
    presentationSheaf O₁ (Under.mk (φ ≫ α)) ⟶
      presentationSheaf O₂ (Under.mk α) :=
  presentationMapOf O₁
    (Under.mk (φ ≫ presentationBase O₂ (Under.mk α)))
    (presentationVariables (Under.mk α))
    (𝟙 _)

/-- Helper for Lemma 17.31.5: the presentation transitivity map extends the coefficient map `φ`
on the base sheaf `\mathcal O_1`. -/
theorem presentationBase_comp_presentation_transitivity_map
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) :
    presentationBase O₁ (Under.mk (φ ≫ α)) ≫ presentation_transitivity_map φ α =
      φ ≫ presentationBase O₂ (Under.mk α) := by
  -- The universal presentation map is defined precisely so that it restricts to the prescribed
  -- coefficient map on the base sheaf.
  simpa [presentation_transitivity_map] using
    (presentationBaseOf_comp_presentationMapOf
      (𝒜 := O₁)
      (𝒝 := Under.mk (φ ≫ presentationBase O₂ (Under.mk α)))
      (E := presentationVariables (Under.mk α))
      (α := 𝟙 (presentationVariables (Under.mk α))))

/-- Helper for Lemma 17.31.5: the coefficient map `φ` and the presentation transitivity map form
the base square used to compare relative differentials of the two canonical presentations. -/
theorem presentationTransitivityBaseSq
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) :
    CommSq
      φ
      (presentationBase O₁ (Under.mk (φ ≫ α)))
      (presentationBase O₂ (Under.mk α))
      (presentation_transitivity_map φ α) := by
  -- The base compatibility is exactly the computation of `presentation_transitivity_map` on
  -- coefficients established just above.
  exact ⟨presentationBase_comp_presentation_transitivity_map φ α⟩

/-- Helper for Lemma 17.31.5: the presentation transitivity map still evaluates the canonical
presentation of `\mathcal O_3` over `\mathcal O_1` to the same target sheaf map
`\mathcal O_3`. -/
theorem presentationTransitivityMap_comp_presentationMap
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) :
    presentation_transitivity_map φ α ≫ presentationMap O₂ (Under.mk α) =
      presentationMap O₁ (Under.mk (φ ≫ α)) := by
  -- Proof comment: both composites are the canonical evaluation map from the polynomial
  -- presentation on the same generator sheaf `\mathcal O_3`.
  rfl

/-- Helper for Lemma 17.31.5: objectwise, the transitivity presentation map carries the kernel of
the source presentation map into the kernel of the target presentation map. -/
theorem presentationTransitivityMap_ker_le_comap
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) (U : (Opens X)ᵒᵖ) :
    RingHom.ker ((presentationMap O₁ (Under.mk (φ ≫ α))).hom.app U).hom ≤
      (RingHom.ker ((presentationMap O₂ (Under.mk α)).hom.app U).hom).comap
        ((presentation_transitivity_map φ α).hom.app U).hom := by
  intro x hx
  -- Proof comment: evaluate the sheaf-level identity
  -- `presentation_transitivity_map ≫ presentationMap = presentationMap` on the section `x`.
  change
    ((presentationMap O₂ (Under.mk α)).hom.app U).hom
        (((presentation_transitivity_map φ α).hom.app U).hom x) = 0
  have hcomp :=
    congrArg
      (fun f : presentationSheaf O₁ (Under.mk (φ ≫ α)) ⟶ O₃ =>
        CommRingCat.Hom.hom (f.hom.app U))
      (presentationTransitivityMap_comp_presentationMap φ α)
  simpa [RingHom.comp_apply] using congrArg (fun g => g x) hcomp

/-- Helper for Lemma 17.31.5: the presentation base square induces the degree `0` map on relative
differentials used in the transitivity comparison. -/
noncomputable def presentationTransitivityDifferentialsMap
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) :
    Ω (presentationBase O₁ (Under.mk (φ ≫ α))) ⟶
      (SheafOfModules.restrictScalars
        (ringSheafMap (presentation_transitivity_map φ α))).obj
        Ω (presentationBase O₂ (Under.mk α)) :=
  -- The Chapter 17 owner `relativeDifferentialsMap` supplies the canonical map attached to the
  -- commutative square of presentation bases.
  relativeDifferentialsMap
    (presentationBase O₁ (Under.mk (φ ≫ α)))
    (presentationBase O₂ (Under.mk α))
    φ
    (presentation_transitivity_map φ α)
    (presentationTransitivityBaseSq φ α)

/-- Helper for Lemma 17.31.5: the source-faithful comparison
`NL_{\mathcal O_3/\mathcal O_1} ⟶ NL_{\mathcal O_3/\mathcal O_2}` attached to the tower
`\mathcal O_1 ⟶ \mathcal O_2 ⟶ \mathcal O_3`. -/
noncomputable def naiveCotangent_transitivity_comparison
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) :
    naiveCotangent O₁ (Under.mk (φ ≫ α)) ⟶ naiveCotangent O₂ (Under.mk α) :=
  -- TODO: descend `presentation_transitivity_map φ α` to the conormal source term in degree `-1`
  -- and pair it with the corresponding `relativeDifferentialsMap` in degree `0`.
  sorry

/-- Helper for Lemma 17.31.5: the source complex `NL_{\mathcal O_3/\mathcal O_1}` is concentrated
in degrees `-1` and `0`, so its degree `1` term is zero. -/
theorem naiveCotangentTransitivitySource_X_one
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) :
    (naiveCotangent O₁ (Under.mk (φ ≫ α))).X 1 = 0 := by
  -- The naive cotangent complex is the standard two-term presentation complex.
  simp [SheafOfModules.RingedSite.naiveCotangent]

/-- Helper for Lemma 17.31.5: the target complex `NL_{\mathcal O_3/\mathcal O_2}` is concentrated
in degrees `-1` and `0`, so its degree `1` term is zero. -/
theorem naiveCotangentTransitivityTarget_X_one
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) :
    (naiveCotangent O₂ (Under.mk α)).X 1 = 0 := by
  -- The same two-term description applies to the target of the comparison map.
  simp [SheafOfModules.RingedSite.naiveCotangent]

/-- Helper for Lemma 17.31.5: the degree `0 → 1` differential of
`NL_{\mathcal O_3/\mathcal O_1}` is zero. -/
theorem naiveCotangentTransitivitySource_d_zero_one
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) :
    (naiveCotangent O₁ (Under.mk (φ ≫ α))).d 0 1 = 0 := by
  -- There is no nonzero differential leaving degree `0` in the two-term presentation model.
  simp [SheafOfModules.RingedSite.naiveCotangent]

/-- Helper for Lemma 17.31.5: the degree `0 → 1` differential of
`NL_{\mathcal O_3/\mathcal O_2}` is zero. -/
theorem naiveCotangentTransitivityTarget_d_zero_one
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) :
    (naiveCotangent O₂ (Under.mk α)).d 0 1 = 0 := by
  -- The target complex is again concentrated in degrees `-1` and `0`.
  simp [SheafOfModules.RingedSite.naiveCotangent]

/-- Helper for Lemma 17.31.5: the canonical map of polynomial presentations
`\mathcal O_1[\mathcal O_2] \to \mathcal O_1[\mathcal O_3]` induced by the identity on
`\mathcal O_1` and the generator map `α : \mathcal O_2 \to \mathcal O_3`. -/
abbrev presentationBaseChangeMap
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) :
    presentationSheaf O₁ (Under.mk φ) ⟶
      presentationSheaf O₁ (Under.mk (φ ≫ α)) :=
  presentationMapOf O₁
    (Under.mk (presentationBase O₁ (Under.mk (φ ≫ α))))
    (presentationVariables (Under.mk φ))
    α

/-- Helper for Lemma 17.31.5: the base-change presentation map restricts to the identity on the
base sheaf `\mathcal O_1`. -/
theorem presentationBase_comp_presentationBaseChangeMap
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) :
    presentationBase O₁ (Under.mk φ) ≫ presentationBaseChangeMap φ α =
      presentationBase O₁ (Under.mk (φ ≫ α)) := by
  -- The induced map on polynomial presentations is defined to preserve coefficients from
  -- `\mathcal O_1`.
  simpa [presentationBaseChangeMap] using
    (presentationBaseOf_comp_presentationMapOf
      (𝒜 := O₁)
      (𝒝 := Under.mk (presentationBase O₁ (Under.mk (φ ≫ α))))
      (E := presentationVariables (Under.mk φ))
      (α := α))

/-- Helper for Lemma 17.31.5: the base-change presentation map evaluates to the given target map
`α` on the canonical generators. -/
theorem presentationBaseChangeMap_comp_presentationMap
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) :
    presentationBaseChangeMap φ α ≫ presentationMap O₁ (Under.mk (φ ≫ α)) =
      presentationMap O₁ (Under.mk φ) ≫ α := by
  -- Proof comment: the base-change presentation map is defined by sending each generator of
  -- `\mathcal O_1[\mathcal O_2]` to its image under `α`.
  rfl

/-- Helper for Lemma 17.31.5: objectwise, the base-change presentation map carries the kernel of
the source presentation map into the kernel of the target presentation map. -/
theorem presentationBaseChangeMap_ker_le_comap
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) (U : (Opens X)ᵒᵖ) :
    RingHom.ker ((presentationMap O₁ (Under.mk φ)).hom.app U).hom ≤
      (RingHom.ker ((presentationMap O₁ (Under.mk (φ ≫ α))).hom.app U).hom).comap
        ((presentationBaseChangeMap φ α).hom.app U).hom := by
  intro x hx
  -- Proof comment: evaluate the generator formula for `presentationBaseChangeMap` on the section
  -- `x` and use that `x` already lies in the source kernel.
  change
    ((presentationMap O₁ (Under.mk (φ ≫ α))).hom.app U).hom
        (((presentationBaseChangeMap φ α).hom.app U).hom x) = 0
  have hcomp :=
    congrArg
      (fun f : presentationSheaf O₁ (Under.mk φ) ⟶ O₃ =>
        CommRingCat.Hom.hom (f.hom.app U))
      (presentationBaseChangeMap_comp_presentationMap φ α)
  simpa [RingHom.comp_apply] using congrArg (fun g => g x) hcomp

/-- Helper for Lemma 17.31.5: the base-change presentation map and the two presentation bases form
the commutative square used for the degree `0` part of the left transitivity map. -/
theorem presentationBaseChangeBaseSq
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) :
    CommSq
      (𝟙 O₁)
      (presentationBase O₁ (Under.mk φ))
      (presentationBase O₁ (Under.mk (φ ≫ α)))
      (presentationBaseChangeMap φ α) := by
  -- The coefficient comparison is exactly the base computation above.
  exact ⟨presentationBase_comp_presentationBaseChangeMap φ α⟩

/-- Helper for Lemma 17.31.5: the base-change square on polynomial presentations induces the
degree `0` morphism on relative differentials used in the left transitivity map. -/
noncomputable def presentationBaseChangeDifferentialsMap
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) :
    Ω (presentationBase O₁ (Under.mk φ)) ⟶
      (SheafOfModules.restrictScalars
        (ringSheafMap (presentationBaseChangeMap φ α))).obj
        Ω (presentationBase O₁ (Under.mk (φ ≫ α))) :=
  -- The left degree `0` map is the canonical functoriality map on relative differentials for the
  -- base-change square of polynomial presentations.
  relativeDifferentialsMap
    (presentationBase O₁ (Under.mk φ))
    (presentationBase O₁ (Under.mk (φ ≫ α)))
    (𝟙 O₁)
    (presentationBaseChangeMap φ α)
    (presentationBaseChangeBaseSq φ α)

/-- Helper for Lemma 17.31.5: the transitivity map from the pulled-back left complex into the
mapping cocone of the comparison map. -/
noncomputable def naiveCotangent_transitivity_left
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) :
    naiveCotangentTransitivityPullback φ α ⟶
      naiveCotangent O₁ (Under.mk (φ ≫ α)) :=
  -- Route correction: the source proof first builds the left map
  -- `α^*NL_{\mathcal O_2/\mathcal O_1} ⟶ NL_{\mathcal O_3/\mathcal O_1}` and only then factors it
  -- through the mapping cocone.
  -- TODO: the degree `0` component is now isolated as `presentationBaseChangeDifferentialsMap φ α`;
  -- the remaining blocker is the degree `-1` conormal-source transport needed to make the
  -- `(-1,0)` square commute and match Lemma `10.134.4` stalkwise.
  sorry

/-- Helper for Lemma 17.31.5: the composite of the left map with the comparison map is
null-homotopic by the explicit degree `(-1,0)` formula from Remark `10.134.5`. -/
noncomputable def naiveCotangent_transitivity_homotopy
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) :
    Homotopy
      (naiveCotangent_transitivity_left φ α ≫ naiveCotangent_transitivity_comparison φ α)
      0 :=
  -- Route correction: the source homotopy is the unique nonzero component sending `d[b] ⊗ 1` to
  -- `[φ(b)] - b[1]`. We isolate this owner before constructing the cocone map.
  -- TODO: package the degree `(-1,0)` component and verify stalkwise, via Remark `10.134.5`,
  -- that it gives a homotopy from the composite to zero.
  sorry

/-- Helper for Lemma 17.31.5: the transitivity map from the pulled-back left complex into the
mapping cocone of the comparison map. -/
noncomputable def naiveCotangent_transitivity_map
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) :
    naiveCotangentTransitivityPullback φ α ⟶
      CochainComplex.mappingCocone (naiveCotangent_transitivity_comparison φ α) :=
  -- Derived Categories, Lemma 13.9.3 factors the left map through the mapping cocone once the
  -- composite with the comparison map is equipped with the explicit null-homotopy above.
  Classical.choose
    (CochainComplex.comp_homotopic_to_zero_factors_through_mapping_cocone
      (naiveCotangent_transitivity_left φ α)
      (naiveCotangent_transitivity_comparison φ α)
      (naiveCotangent_transitivity_homotopy φ α))

/-- Helper for Lemma 17.31.5: the chosen cocone map really extends the left map when projected to
the first cocone summand. -/
theorem naiveCotangent_transitivity_map_fst
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) :
    naiveCotangent_transitivity_map φ α ≫
      CochainComplex.mappingCocone.fst (naiveCotangent_transitivity_comparison φ α) =
        naiveCotangent_transitivity_left φ α := by
  -- Unpack the specification of the factorization chosen from Derived Categories, Lemma `13.9.3`.
  exact Classical.choose_spec
    (CochainComplex.comp_homotopic_to_zero_factors_through_mapping_cocone
      (naiveCotangent_transitivity_left φ α)
      (naiveCotangent_transitivity_comparison φ α)
      (naiveCotangent_transitivity_homotopy φ α))

/-- Helper for Lemma 17.31.5: the transitivity map induces the Jacobi-Zariski `H^0/H^{-1}`
properties required for the six-term exact sequence. -/
theorem naiveCotangent_transitivity_homology
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) :
    IsIso (HomologicalComplex.homologyMap (naiveCotangent_transitivity_map φ α) 0) ∧
      Epi (HomologicalComplex.homologyMap (naiveCotangent_transitivity_map φ α) (-1)) := by
  -- TODO: after transporting to stalks via Lemma 17.31.4 and commuting homology with stalks via
  -- Lemma 18.36.3, use `naiveCotangent_transitivity_map_fst` to compare the left edge with the
  -- stalkwise Jacobi-Zariski sequence and identify the remaining maps with the algebraic owners.
  sorry

/-- Lemma 17.31.5 supplies a comparison
`NL_{\mathcal O_3/\mathcal O_1} ⟶ NL_{\mathcal O_3/\mathcal O_2}` together with a transitivity map
`\alpha^* NL_{\mathcal O_2/\mathcal O_1} ⟶
  Cone(NL_{\mathcal O_3/\mathcal O_1} ⟶ NL_{\mathcal O_3/\mathcal O_2})[-1]`
whose induced map on `H^0` is an isomorphism and on `H^{-1}` is an epimorphism. -/
@[stacks 0E1Y]
theorem exists_naiveCotangentTransitivity
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) :
    ∃ comparison :
        naiveCotangent O₁ (Under.mk (φ ≫ α)) ⟶ naiveCotangent O₂ (Under.mk α),
      ∃ transitivity :
          (((SheafOfModules.pullback (ringedSiteStructureMap α)).mapHomologicalComplex (up ℤ)).obj
            (naiveCotangent O₁ (Under.mk φ))) ⟶ CochainComplex.mappingCocone comparison,
        IsIso (HomologicalComplex.homologyMap transitivity 0) ∧
          Epi (HomologicalComplex.homologyMap transitivity (-1)) := by
  -- Route correction: isolate the proof into the source-faithful comparison map, the induced map
  -- to the mapping cocone, and the stalkwise `H^0/H^{-1}` identification.
  refine ⟨naiveCotangent_transitivity_comparison φ α, naiveCotangent_transitivity_map φ α, ?_⟩
  -- The remaining content is exactly the stalkwise Jacobi-Zariski comparison packaged above.
  exact naiveCotangent_transitivity_homology φ α

end TopCat.Sheaf
