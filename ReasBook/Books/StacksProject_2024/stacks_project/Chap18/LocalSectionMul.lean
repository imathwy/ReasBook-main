import StacksProject_2024.stacks_project.Chap18.Lemma_18_11_1

open CategoryTheory Opposite

noncomputable section

universe u v

namespace PresheafOfModules.LocalSectionMul

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable (𝒪 : Sheaf J CommRingCat.{max u v})

private abbrev underlyingRingSheaf : Sheaf J RingCat.{max u v} :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪

private abbrev overPresheafModule (ℱ : PresheafOfModules (underlyingRingSheaf 𝒪).obj)
    (U : C) : PresheafOfModules (((underlyingRingSheaf 𝒪).over U).obj) :=
  (PresheafOfModules.pushforward₀ (Over.forget U) (underlyingRingSheaf 𝒪).obj).obj ℱ

private def localSectionMulAppFun (ℳ : PresheafOfModules (underlyingRingSheaf 𝒪).obj)
    (U : C) (r : (underlyingRingSheaf 𝒪).obj.obj (op U)) (V : (Over U)ᵒᵖ) :
    (overPresheafModule 𝒪 ℳ U).obj V → (overPresheafModule 𝒪 ℳ U).obj V :=
  fun m ↦
    let rV : ((underlyingRingSheaf 𝒪).over U).obj.obj V :=
      show ((underlyingRingSheaf 𝒪).over U).obj.obj V from
        ((underlyingRingSheaf 𝒪).obj.map (op V.unop.hom) r)
    rV • m

private theorem localSectionMulAppFun_map_add
    (ℳ : PresheafOfModules (underlyingRingSheaf 𝒪).obj) (U : C)
    (r : (underlyingRingSheaf 𝒪).obj.obj (op U)) (V : (Over U)ᵒᵖ)
    (x y : (overPresheafModule 𝒪 ℳ U).obj V) :
    localSectionMulAppFun 𝒪 ℳ U r V (x + y) =
      localSectionMulAppFun 𝒪 ℳ U r V x + localSectionMulAppFun 𝒪 ℳ U r V y := by
  let rV : ((underlyingRingSheaf 𝒪).over U).obj.obj V :=
    ((underlyingRingSheaf 𝒪).obj.map (op V.unop.hom) r)
  change rV • (x + y) = rV • x + rV • y
  exact smul_add rV x y

private theorem localSectionMulAppFun_map_smul
    (ℳ : PresheafOfModules (underlyingRingSheaf 𝒪).obj) (U : C)
    (r : (underlyingRingSheaf 𝒪).obj.obj (op U)) (V : (Over U)ᵒᵖ)
    (a : ((underlyingRingSheaf 𝒪).over U).obj.obj V)
    (x : (overPresheafModule 𝒪 ℳ U).obj V) :
    localSectionMulAppFun 𝒪 ℳ U r V (a • x) =
      a • localSectionMulAppFun 𝒪 ℳ U r V x := by
  letI : CommRing (((underlyingRingSheaf 𝒪).over U).obj.obj V) := by
    change CommRing (𝒪.obj.obj (op V.unop.left))
    infer_instance
  let M : ModuleCat (((underlyingRingSheaf 𝒪).over U).obj.obj V) :=
    (overPresheafModule 𝒪 ℳ U).obj V
  letI : Module (((underlyingRingSheaf 𝒪).over U).obj.obj V) M := M.isModule
  let rV : ((underlyingRingSheaf 𝒪).over U).obj.obj V :=
    ((underlyingRingSheaf 𝒪).obj.map (op V.unop.hom) r)
  change rV • (a • x) = a • (rV • x)
  rw [smul_smul, smul_smul]
  congr 1
  exact mul_comm rV a

private def localSectionMulApp (ℳ : PresheafOfModules (underlyingRingSheaf 𝒪).obj)
    (U : C) (r : (underlyingRingSheaf 𝒪).obj.obj (op U)) (V : (Over U)ᵒᵖ) :
    (overPresheafModule 𝒪 ℳ U).obj V ⟶ (overPresheafModule 𝒪 ℳ U).obj V :=
  let X : ModuleCat (((underlyingRingSheaf 𝒪).over U).obj.obj V) :=
    (overPresheafModule 𝒪 ℳ U).obj V
  let f : X →ₗ[((underlyingRingSheaf 𝒪).over U).obj.obj V] X :=
    { toFun := localSectionMulAppFun 𝒪 ℳ U r V
      map_add' := localSectionMulAppFun_map_add 𝒪 ℳ U r V
      map_smul' := localSectionMulAppFun_map_smul 𝒪 ℳ U r V }
  ((ModuleCat.homEquiv :
      (X ⟶ X) ≃ (X →ₗ[((underlyingRingSheaf 𝒪).over U).obj.obj V] X)).symm f)

private theorem localSectionMulApp_apply
    (ℳ : PresheafOfModules (underlyingRingSheaf 𝒪).obj) (U : C)
    (r : (underlyingRingSheaf 𝒪).obj.obj (op U)) (V : (Over U)ᵒᵖ)
    (x : (overPresheafModule 𝒪 ℳ U).obj V) :
    localSectionMulApp 𝒪 ℳ U r V x =
      (show ((underlyingRingSheaf 𝒪).over U).obj.obj V from
        ((underlyingRingSheaf 𝒪).obj.map (op V.unop.hom) r)) • x := by
  rfl

private theorem underlying_ring_map_comp_apply
    {U X Y : C} (a : op U ⟶ op X) (b : op X ⟶ op Y)
    (r : (underlyingRingSheaf 𝒪).obj.obj (op U)) :
    (underlyingRingSheaf 𝒪).obj.map b ((underlyingRingSheaf 𝒪).obj.map a r) =
      (underlyingRingSheaf 𝒪).obj.map (a ≫ b) r := by
  change
    (ConcreteCategory.hom (((underlyingRingSheaf 𝒪).obj.map a) ≫
        ((underlyingRingSheaf 𝒪).obj.map b))) r =
      (ConcreteCategory.hom ((underlyingRingSheaf 𝒪).obj.map (a ≫ b))) r
  exact congrArg (fun f ↦ (ConcreteCategory.hom f) r)
    ((underlyingRingSheaf 𝒪).obj.map_comp a b).symm

private theorem slice_restrict_section_eq
    (U : C) (r : (underlyingRingSheaf 𝒪).obj.obj (op U)) {X Y : (Over U)ᵒᵖ}
    (f : X ⟶ Y) :
    ((((underlyingRingSheaf 𝒪).over U).obj.map f).hom)
        (show ((underlyingRingSheaf 𝒪).over U).obj.obj X from
          ((underlyingRingSheaf 𝒪).obj.map (op X.unop.hom) r)) =
      (show ((underlyingRingSheaf 𝒪).over U).obj.obj Y from
        ((underlyingRingSheaf 𝒪).obj.map (op Y.unop.hom) r)) := by
  change
    (underlyingRingSheaf 𝒪).obj.map
        (show op X.unop.left ⟶ op Y.unop.left from op f.unop.left)
        (((underlyingRingSheaf 𝒪).obj.map
          (show op U ⟶ op X.unop.left from op X.unop.hom)) r) =
      ((underlyingRingSheaf 𝒪).obj.map
        (show op U ⟶ op Y.unop.left from op Y.unop.hom)) r
  have hw :
      (show op U ⟶ op X.unop.left from op X.unop.hom) ≫
        (show op X.unop.left ⟶ op Y.unop.left from op f.unop.left) =
      (show op U ⟶ op Y.unop.left from op Y.unop.hom) := by
    simpa using congrArg Quiver.Hom.op (Over.w f.unop)
  rw [underlying_ring_map_comp_apply]
  rw [hw]

private theorem localSectionMul_naturality
    (ℳ : PresheafOfModules (underlyingRingSheaf 𝒪).obj) (U : C)
    (r : (underlyingRingSheaf 𝒪).obj.obj (op U)) {X Y : (Over U)ᵒᵖ} (f : X ⟶ Y) :
    (overPresheafModule 𝒪 ℳ U).map f ≫
      (ModuleCat.restrictScalars (((((underlyingRingSheaf 𝒪).over U).obj).map f).hom)).map
        (localSectionMulApp 𝒪 ℳ U r Y) =
      localSectionMulApp 𝒪 ℳ U r X ≫ (overPresheafModule 𝒪 ℳ U).map f := by
  ext x
  change
    localSectionMulApp 𝒪 ℳ U r Y ((overPresheafModule 𝒪 ℳ U).map f x) =
      (overPresheafModule 𝒪 ℳ U).map f (localSectionMulApp 𝒪 ℳ U r X x)
  rw [localSectionMulApp_apply, localSectionMulApp_apply]
  rw [← slice_restrict_section_eq (𝒪 := 𝒪) U r f]
  simpa using
    (((overPresheafModule 𝒪 ℳ U).map f).hom.map_smul
      (show ((underlyingRingSheaf 𝒪).over U).obj.obj X from
        ((underlyingRingSheaf 𝒪).obj.map (op X.unop.hom) r))
      x).symm

private def localSectionMul (ℳ : PresheafOfModules (underlyingRingSheaf 𝒪).obj)
    (U : C) (r : (underlyingRingSheaf 𝒪).obj.obj (op U)) :
    overPresheafModule 𝒪 ℳ U ⟶ overPresheafModule 𝒪 ℳ U where
  app V := localSectionMulApp 𝒪 ℳ U r V
  naturality f := localSectionMul_naturality 𝒪 ℳ U r f

end PresheafOfModules.LocalSectionMul

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable (𝒪 : Sheaf J CommRingCat.{max u v})

/-- Multiplication by a local section on the restriction of a sheaf of `\mathcal O`-modules to
the slice site `C / U`. -/
noncomputable abbrev localSectionMul
    (ℱ : SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪))
    (U : C) (r : ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).obj.obj (op U)) :
    ℱ.over U ⟶ ℱ.over U where
  val := PresheafOfModules.LocalSectionMul.localSectionMul 𝒪 ℱ.val U r

end SheafOfModules
