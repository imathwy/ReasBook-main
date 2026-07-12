import Mathlib
import StacksProject_2024.Chap07.Lemma_7_26_1
import StacksProject_2024.Chap18.Lemma_18_11_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

noncomputable section

universe u v

namespace PresheafOfModules

/- Domain-style sampling for Lemma 18.27.1:
- primary domain: local `𝒪`-linear Hom on slice sites for presheaves and sheaves of modules over a
  commutative ring sheaf;
- sampled owner declarations:
  `SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)`,
  `CategoryTheory.ihom`,
  `PresheafOfModules.pushforward₀`,
  `PresheafOfModules.ofPresheaf`,
  `SheafOfModules.toSheaf`;
- best owner abstraction: for a general presheaf source the source-facing owner is the Chapter 18
  local-Hom sheaf in `SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)`,
  while for a sheaf source the canonical owner is `ihom`;
- primitive data: a commutative ring sheaf `𝒪`, a presheaf of `𝒪`-modules `ℱ`, and a sheaf of
  `𝒪`-modules `𝒢`;
- derived API: restriction to slice sites via `pushforward₀`, multiplication by a local section on
  a restricted presheaf of modules, the local Hom presheaf, the resulting sheaf object, and the
  bridge from the sheaf-source specialization to `ihom`.

Source/core/bridge triage:
- `source-facing`: the local `\mathcal O`-module
  `\mathcal H\!\mathit{om}_{\mathcal O}(\mathcal F, \mathcal G)`;
- `core/canonical`: `SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)`,
  `ihom`, and `PresheafOfModules.pushforward₀` on the raw underlying ring sheaf for the presheaf
  input;
- `bridge/view`: the codomain sheaf `𝒢` is used through its underlying presheaf of modules
  `𝒢.val`, while the sheaf-source specialization is canonically compared with `ihom` and
  `SheafOfModules.toSheaf` remains only an underlying-abelian-sheaf forgetful view.

This rewrite targets the `source-facing` owner layer. It removes the previous duplicate
sheaf-level owner spelling and keeps the local Hom object as a genuine presheaf, hence sheaf, of
`𝒪`-modules in the chapter owner category, together with the canonical bridge to `ihom` when the
source is already a sheaf. -/

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable (𝒪 : Sheaf J CommRingCat.{max u v})

/-- The underlying `RingCat`-valued structure sheaf of the ringed site `(C, J, 𝒪)`. -/
private abbrev underlyingRingSheaf : Sheaf J RingCat.{max u v} :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪

/-- The restriction of a presheaf of `𝒪`-modules to the slice site `C / U`. -/
private abbrev overPresheafModule (ℱ : PresheafOfModules (underlyingRingSheaf 𝒪).obj)
    (U : C) : PresheafOfModules (((underlyingRingSheaf 𝒪).over U).obj) :=
  (pushforward₀ (Over.forget U) (underlyingRingSheaf 𝒪).obj).obj ℱ

/-- Multiplication by a local section on the restriction of a presheaf of `𝒪`-modules to
`C / U`, evaluated at an object of the slice. -/
private def localSectionMulAppFun (ℳ : PresheafOfModules (underlyingRingSheaf 𝒪).obj) (U : C)
    (r : (underlyingRingSheaf 𝒪).obj.obj (op U)) (V : (Over U)ᵒᵖ) :
    (overPresheafModule 𝒪 ℳ U).obj V → (overPresheafModule 𝒪 ℳ U).obj V :=
  fun m ↦
    let rV : ((underlyingRingSheaf 𝒪).over U).obj.obj V :=
      show ((underlyingRingSheaf 𝒪).over U).obj.obj V from
        ((underlyingRingSheaf 𝒪).obj.map (op V.unop.hom) r)
    rV • m

/-- Objectwise multiplication by a local section preserves addition. -/
private theorem localSectionMulAppFun_map_add
    (ℳ : PresheafOfModules (underlyingRingSheaf 𝒪).obj) (U : C)
    (r : (underlyingRingSheaf 𝒪).obj.obj (op U)) (V : (Over U)ᵒᵖ)
    (x y : (overPresheafModule 𝒪 ℳ U).obj V) :
    localSectionMulAppFun 𝒪 ℳ U r V (x + y) =
      localSectionMulAppFun 𝒪 ℳ U r V x + localSectionMulAppFun 𝒪 ℳ U r V y := by
  -- Unfold the localized scalar action and use distributivity of scalar multiplication.
  let rV : ((underlyingRingSheaf 𝒪).over U).obj.obj V :=
    ((underlyingRingSheaf 𝒪).obj.map (op V.unop.hom) r)
  change rV • (x + y) = rV • x + rV • y
  exact smul_add rV x y

/-- Objectwise multiplication by a local section is linear over the localized structure ring. -/
private theorem localSectionMulAppFun_map_smul
    (ℳ : PresheafOfModules (underlyingRingSheaf 𝒪).obj) (U : C)
    (r : (underlyingRingSheaf 𝒪).obj.obj (op U)) (V : (Over U)ᵒᵖ)
    (a : ((underlyingRingSheaf 𝒪).over U).obj.obj V) (x : (overPresheafModule 𝒪 ℳ U).obj V) :
    localSectionMulAppFun 𝒪 ℳ U r V (a • x) =
      a • localSectionMulAppFun 𝒪 ℳ U r V x := by
  -- Rewrite the localized action on both sides and commute the two scalars in the commutative
  -- structure ring of the slice site.
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

/-- Multiplication by a local section as an endomorphism of the restriction to `C / U`. -/
private def localSectionMulApp (ℳ : PresheafOfModules (underlyingRingSheaf 𝒪).obj) (U : C)
    (r : (underlyingRingSheaf 𝒪).obj.obj (op U)) (V : (Over U)ᵒᵖ) :
    (overPresheafModule 𝒪 ℳ U).obj V ⟶ (overPresheafModule 𝒪 ℳ U).obj V :=
  let X : ModuleCat (((underlyingRingSheaf 𝒪).over U).obj.obj V) :=
    (overPresheafModule 𝒪 ℳ U).obj V
  let f : X →ₗ[((underlyingRingSheaf 𝒪).over U).obj.obj V] X :=
    { toFun := localSectionMulAppFun 𝒪 ℳ U r V
      map_add' := localSectionMulAppFun_map_add 𝒪 ℳ U r V
      map_smul' := localSectionMulAppFun_map_smul 𝒪 ℳ U r V }
  ((ModuleCat.homEquiv :
      (X ⟶ X) ≃ (X →ₗ[((underlyingRingSheaf 𝒪).over U).obj.obj V] X)).symm f)

/-- Helper for Lemma 18.27.1: objectwise evaluation of the localized multiplication endomorphism
is scalar multiplication by the restricted section. -/
private theorem localSectionMulApp_apply
    (ℳ : PresheafOfModules (underlyingRingSheaf 𝒪).obj) (U : C)
    (r : (underlyingRingSheaf 𝒪).obj.obj (op U)) (V : (Over U)ᵒᵖ)
    (x : (overPresheafModule 𝒪 ℳ U).obj V) :
    localSectionMulApp 𝒪 ℳ U r V x =
      (show ((underlyingRingSheaf 𝒪).over U).obj.obj V from
        ((underlyingRingSheaf 𝒪).obj.map (op V.unop.hom) r)) • x := by
  rfl

/-- Helper for Lemma 18.27.1: restricting the zero section along a slice arrow still gives the
zero section. -/
private theorem localized_zero_section
    (U : C) (V : (Over U)ᵒᵖ) :
    (underlyingRingSheaf 𝒪).obj.map (op V.unop.hom) 0 = 0 := by
  simpa using
    (ConcreteCategory.hom ((underlyingRingSheaf 𝒪).obj.map (op V.unop.hom))).map_zero

/-- Helper for Lemma 18.27.1: the structure ring on the slice site restricts along a slice arrow
by the underlying restriction morphism of `𝒪`. -/
private theorem slice_ring_map_hom_eq
    (U : C) {X Y : (Over U)ᵒᵖ} (f : X ⟶ Y) :
    ((((underlyingRingSheaf 𝒪).over U).obj).map f).hom =
      ((underlyingRingSheaf 𝒪).obj.map
        (show op X.unop.left ⟶ op Y.unop.left from op f.unop.left)).hom := by
  -- The slice-site structure sheaf is defined by restricting `𝒪` along the forgetful functor.
  rfl

/-- Helper for Lemma 18.27.1: applying two successive restriction maps in the underlying ring
sheaf agrees with restricting along the composite arrow. -/
private theorem underlying_ring_map_comp_apply
    {U X Y : C} (a : op U ⟶ op X) (b : op X ⟶ op Y)
    (r : (underlyingRingSheaf 𝒪).obj.obj (op U)) :
    (underlyingRingSheaf 𝒪).obj.map b ((underlyingRingSheaf 𝒪).obj.map a r) =
      (underlyingRingSheaf 𝒪).obj.map (a ≫ b) r := by
  -- Evaluate the functoriality identity on the section `r`.
  change
    (ConcreteCategory.hom (((underlyingRingSheaf 𝒪).obj.map a) ≫
        ((underlyingRingSheaf 𝒪).obj.map b))) r =
      (ConcreteCategory.hom ((underlyingRingSheaf 𝒪).obj.map (a ≫ b))) r
  exact congrArg (fun f ↦ (ConcreteCategory.hom f) r)
    ((underlyingRingSheaf 𝒪).obj.map_comp a b).symm

/-- Helper for Lemma 18.27.1: restricting `r` to `X` and then along `f` agrees with restricting
`r` directly to `Y`. -/
private theorem slice_restrict_section_eq
    (U : C) (r : (underlyingRingSheaf 𝒪).obj.obj (op U)) {X Y : (Over U)ᵒᵖ} (f : X ⟶ Y) :
    ((((underlyingRingSheaf 𝒪).over U).obj.map f).hom)
        (show ((underlyingRingSheaf 𝒪).over U).obj.obj X from
          ((underlyingRingSheaf 𝒪).obj.map (op X.unop.hom) r)) =
      (show ((underlyingRingSheaf 𝒪).over U).obj.obj Y from
        ((underlyingRingSheaf 𝒪).obj.map (op Y.unop.hom) r)) := by
  -- Rewrite the slice-site map back to the underlying restriction map on `𝒪`.
  change
    (underlyingRingSheaf 𝒪).obj.map
        (show op X.unop.left ⟶ op Y.unop.left from op f.unop.left)
        (((underlyingRingSheaf 𝒪).obj.map
          (show op U ⟶ op X.unop.left from op X.unop.hom)) r) =
      ((underlyingRingSheaf 𝒪).obj.map
        (show op U ⟶ op Y.unop.left from op Y.unop.hom)) r
  -- The defining relation of `f.unop : Y.unop ⟶ X.unop` in `Over U` identifies the two routes.
  have hw :
      (show op U ⟶ op X.unop.left from op X.unop.hom) ≫
        (show op X.unop.left ⟶ op Y.unop.left from op f.unop.left) =
      (show op U ⟶ op Y.unop.left from op Y.unop.hom) := by
    simpa using congrArg Quiver.Hom.op (Over.w f.unop)
  -- First rewrite the left side as restriction along the composite route, then identify that
  -- route with the direct restriction by the defining relation in `Over U`.
  rw [underlying_ring_map_comp_apply]
  rw [hw]

/-- Multiplication by a local section is natural on the localized presheaf of modules. -/
private theorem localSectionMul_naturality
    (ℳ : PresheafOfModules (underlyingRingSheaf 𝒪).obj) (U : C)
    (r : (underlyingRingSheaf 𝒪).obj.obj (op U)) {X Y : (Over U)ᵒᵖ} (f : X ⟶ Y) :
    (overPresheafModule 𝒪 ℳ U).map f ≫
      (ModuleCat.restrictScalars (((((underlyingRingSheaf 𝒪).over U).obj).map f).hom)).map
        (localSectionMulApp 𝒪 ℳ U r Y) =
      localSectionMulApp 𝒪 ℳ U r X ≫ (overPresheafModule 𝒪 ℳ U).map f := by
  -- Route correction: evaluate both composites on an element and rewrite the slice-site ring map
  -- to the direct restriction map on `𝒪`.
  ext x
  -- The underlying linear maps of the two composites have the expected pointwise formulas.
  change
    localSectionMulApp 𝒪 ℳ U r Y ((overPresheafModule 𝒪 ℳ U).map f x) =
      (overPresheafModule 𝒪 ℳ U).map f (localSectionMulApp 𝒪 ℳ U r X x)
  -- The two localized multiplication morphisms are scalar multiplication by the restricted
  -- section on `X` and `Y`.
  rw [localSectionMulApp_apply, localSectionMulApp_apply]
  -- Naturality of the presheaf restriction map is exactly `map_smul`; the scalar rewrite comes
  -- from the slice-site restriction identity proved above.
  rw [← slice_restrict_section_eq (𝒪 := 𝒪) U r f]
  -- The localized restriction morphism is linear over the slice-site restriction map.
  simpa using
    (((overPresheafModule 𝒪 ℳ U).map f).hom.map_smul
      (show ((underlyingRingSheaf 𝒪).over U).obj.obj X from
        ((underlyingRingSheaf 𝒪).obj.map (op X.unop.hom) r))
      x).symm

/-- Multiplication by a local section as an endomorphism of the restriction to `C / U`. -/
private def localSectionMul (ℳ : PresheafOfModules (underlyingRingSheaf 𝒪).obj) (U : C)
    (r : (underlyingRingSheaf 𝒪).obj.obj (op U)) :
    overPresheafModule 𝒪 ℳ U ⟶ overPresheafModule 𝒪 ℳ U where
  app V := localSectionMulApp 𝒪 ℳ U r V
  naturality f := localSectionMul_naturality 𝒪 ℳ U r f

/-- The localized multiplication endomorphism for the zero section is zero. -/
private theorem localSectionMul_zero
    (ℳ : PresheafOfModules (underlyingRingSheaf 𝒪).obj) (U : C) :
    localSectionMul 𝒪 ℳ U 0 = 0 := by
  -- Evaluate the natural transformation objectwise; the restricted zero section acts by zero on
  -- every localized module.
  ext V x
  let M : ModuleCat (((underlyingRingSheaf 𝒪).over U).obj.obj V) := (overPresheafModule 𝒪 ℳ U).obj V
  letI : Module (((underlyingRingSheaf 𝒪).over U).obj.obj V) M := M.isModule
  -- The objectwise scalar is the restriction of the zero section, hence acts trivially.
  change
      (show ((underlyingRingSheaf 𝒪).over U).obj.obj V from
        ((underlyingRingSheaf 𝒪).obj.map (op V.unop.hom) 0)) • x =
        (0 : (overPresheafModule 𝒪 ℳ U).obj V)
  have hzero :
      (show ((underlyingRingSheaf 𝒪).over U).obj.obj V from
        ((underlyingRingSheaf 𝒪).obj.map (op V.unop.hom) 0)) = 0 := by
    simpa using
      (ConcreteCategory.hom ((underlyingRingSheaf 𝒪).obj.map (op V.unop.hom))).map_zero
  rw [hzero]
  simpa using (zero_smul (((underlyingRingSheaf 𝒪).over U).obj.obj V) x)

/-- The localized multiplication endomorphism is additive in the section. -/
private theorem localSectionMul_add
    (ℳ : PresheafOfModules (underlyingRingSheaf 𝒪).obj) (U : C)
    (r s : (underlyingRingSheaf 𝒪).obj.obj (op U)) :
    localSectionMul 𝒪 ℳ U (r + s) =
      localSectionMul 𝒪 ℳ U r + localSectionMul 𝒪 ℳ U s := by
  -- Compare the two endomorphisms at each object of the slice and push addition through the
  -- restricted section using `map_add`.
  ext V x
  -- Restricting `r + s` is additive, and scalar multiplication distributes over that sum.
  change
      (show ((underlyingRingSheaf 𝒪).over U).obj.obj V from
        ((underlyingRingSheaf 𝒪).obj.map (op V.unop.hom) (r + s))) • x =
      (show ((underlyingRingSheaf 𝒪).over U).obj.obj V from
        ((underlyingRingSheaf 𝒪).obj.map (op V.unop.hom) r)) • x +
        (show ((underlyingRingSheaf 𝒪).over U).obj.obj V from
          ((underlyingRingSheaf 𝒪).obj.map (op V.unop.hom) s)) • x
  have hmap :
      (show ((underlyingRingSheaf 𝒪).over U).obj.obj V from
        ((underlyingRingSheaf 𝒪).obj.map (op V.unop.hom) (r + s))) =
      (show ((underlyingRingSheaf 𝒪).over U).obj.obj V from
        ((underlyingRingSheaf 𝒪).obj.map (op V.unop.hom) r)) +
        (show ((underlyingRingSheaf 𝒪).over U).obj.obj V from
          ((underlyingRingSheaf 𝒪).obj.map (op V.unop.hom) s)) := by
    simpa using
      (ConcreteCategory.hom ((underlyingRingSheaf 𝒪).obj.map (op V.unop.hom))).map_add r s
  rw [hmap]
  exact add_smul _ _ x

/-- The localized multiplication endomorphism for the unit section is the identity. -/
private theorem localSectionMul_one
    (ℳ : PresheafOfModules (underlyingRingSheaf 𝒪).obj) (U : C) :
    localSectionMul 𝒪 ℳ U 1 = 𝟙 _ := by
  -- The restricted unit section acts as the identity on every localized module.
  ext V x
  let M : ModuleCat (((underlyingRingSheaf 𝒪).over U).obj.obj V) := (overPresheafModule 𝒪 ℳ U).obj V
  letI : Module (((underlyingRingSheaf 𝒪).over U).obj.obj V) M := M.isModule
  -- Restricting the unit section stays equal to the unit, so the action is the identity.
  change
      (show ((underlyingRingSheaf 𝒪).over U).obj.obj V from
        ((underlyingRingSheaf 𝒪).obj.map (op V.unop.hom) 1)) • x = x
  have hone :
      (show ((underlyingRingSheaf 𝒪).over U).obj.obj V from
        ((underlyingRingSheaf 𝒪).obj.map (op V.unop.hom) 1)) = 1 := by
    simpa using
      (ConcreteCategory.hom ((underlyingRingSheaf 𝒪).obj.map (op V.unop.hom))).map_one
  rw [hone]
  simpa using (one_smul (((underlyingRingSheaf 𝒪).over U).obj.obj V) x)

/-- Localized multiplication is multiplicative in the section. -/
private theorem localSectionMul_mul
    (ℳ : PresheafOfModules (underlyingRingSheaf 𝒪).obj) (U : C)
    (r s : (underlyingRingSheaf 𝒪).obj.obj (op U)) :
    localSectionMul 𝒪 ℳ U (r * s) =
      localSectionMul 𝒪 ℳ U s ≫ localSectionMul 𝒪 ℳ U r := by
  -- Objectwise, restricting a product of sections equals the product of the restricted sections,
  -- and composition of the two scalar-action endomorphisms is `smul_smul`.
  ext V x
  let M : ModuleCat (((underlyingRingSheaf 𝒪).over U).obj.obj V) := (overPresheafModule 𝒪 ℳ U).obj V
  letI : Module (((underlyingRingSheaf 𝒪).over U).obj.obj V) M := M.isModule
  -- The two successive localized multiplications act by the product of the restricted sections.
  change
      (show ((underlyingRingSheaf 𝒪).over U).obj.obj V from
        ((underlyingRingSheaf 𝒪).obj.map (op V.unop.hom) (r * s))) • x =
      (show ((underlyingRingSheaf 𝒪).over U).obj.obj V from
        ((underlyingRingSheaf 𝒪).obj.map (op V.unop.hom) r)) •
        ((show ((underlyingRingSheaf 𝒪).over U).obj.obj V from
          ((underlyingRingSheaf 𝒪).obj.map (op V.unop.hom) s)) • x)
  have hmap :
      (show ((underlyingRingSheaf 𝒪).over U).obj.obj V from
        ((underlyingRingSheaf 𝒪).obj.map (op V.unop.hom) (r * s))) =
      (show ((underlyingRingSheaf 𝒪).over U).obj.obj V from
        ((underlyingRingSheaf 𝒪).obj.map (op V.unop.hom) r)) *
        (show ((underlyingRingSheaf 𝒪).over U).obj.obj V from
          ((underlyingRingSheaf 𝒪).obj.map (op V.unop.hom) s)) := by
    simpa using
      (ConcreteCategory.hom ((underlyingRingSheaf 𝒪).obj.map (op V.unop.hom))).map_mul r s
  rw [hmap]
  simpa using
    (smul_smul
      (show ((underlyingRingSheaf 𝒪).over U).obj.obj V from
        ((underlyingRingSheaf 𝒪).obj.map (op V.unop.hom) r))
      (show ((underlyingRingSheaf 𝒪).over U).obj.obj V from
        ((underlyingRingSheaf 𝒪).obj.map (op V.unop.hom) s))
      x).symm

variable (ℱ : PresheafOfModules (underlyingRingSheaf 𝒪).obj)
variable (𝒢 : SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪))

private abbrev overHom (U : C) :=
  overPresheafModule 𝒪 ℱ U ⟶ overPresheafModule 𝒪 𝒢.val U

private abbrev localHomMap {U V : Cᵒᵖ} (f : U ⟶ V) :
    overHom 𝒪 ℱ 𝒢 U.unop → overHom 𝒪 ℱ 𝒢 V.unop :=
  (pushforward₀ (Over.map f.unop) (((underlyingRingSheaf 𝒪).over U.unop).obj)).map

/-- Helper for Lemma 18.27.1: relocalizing an object of a slice site along the identity map does
not change that object. -/
private theorem over_map_id_obj_eq
    (U : Cᵒᵖ) (X : Over U.unop) :
    ((Over.map (𝟙 U.unop)).obj X) = X := by
  -- Reduce the identity relocalization to the identity functor, then evaluate on `X`.
  simpa using congrArg (fun F ↦ F.obj X) (Over.mapId_eq U.unop)

/-- Helper for Lemma 18.27.1: relocalizing an object in two steps agrees with relocalizing along
the composite map. -/
private theorem over_map_comp_obj_eq
    {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) (X : Over W.unop) :
    ((Over.map (g.unop ≫ f.unop)).obj X) =
      ((Over.map f.unop).obj ((Over.map g.unop).obj X)) := by
  -- Reduce the composite relocalization functor to the composite of relocalizations.
  simpa using congrArg (fun F ↦ F.obj X) (Over.mapComp_eq g.unop f.unop)

/-- Helper for Lemma 18.27.1: the identity relocalization functor on a slice site is literally the
identity functor. -/
private theorem over_map_id_eq_functor
    (U : Cᵒᵖ) :
    Over.map (𝟙 U.unop) = 𝟭 (Over U.unop) := by
  -- This is the functor-level owner form of the identity relocalization statement.
  simpa using Over.mapId_eq U.unop

/-- Helper for Lemma 18.27.1: relocalizing along a composite arrow agrees with first relocalizing
along the right arrow and then along the left arrow. -/
private theorem over_map_comp_eq_functor
    {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) :
    Over.map (g.unop ≫ f.unop) = Over.map g.unop ⋙ Over.map f.unop := by
  -- This is the functor-level owner form of the composite relocalization statement.
  simpa using Over.mapComp_eq g.unop f.unop

/-- Helper for Lemma 18.27.1: the component of `localHomMap` on a slice object is obtained by
evaluating the original localized Hom on the relocalized slice object. -/
private theorem localHomMap_app
    {U V : Cᵒᵖ} (f : U ⟶ V) (φ : overHom 𝒪 ℱ 𝒢 U.unop) (X : (Over V.unop)ᵒᵖ) :
    (localHomMap 𝒪 ℱ 𝒢 f φ).app X =
      φ.app (op ((Over.map f.unop).obj X.unop)) := by
  -- `pushforward₀` acts on natural transformations by relocalizing the object index.
  rfl

/-- Helper for Lemma 18.27.1: transporting the `app` field of a localized Hom along an equality
of slice objects is definitionally trivial after case-splitting on that equality. -/
private theorem hom_app_transport
    {U : C} (φ : overHom 𝒪 ℱ 𝒢 U) {X Y : (Over U)ᵒᵖ} (h : X = Y) :
    Eq.ndrec (motive := fun Z ↦
      (overPresheafModule 𝒪 ℱ U).obj Z ⟶ (overPresheafModule 𝒪 𝒢.val U).obj Z)
      (φ.app X) h = φ.app Y := by
  -- The transport only changes the slice-object index.
  cases h
  rfl

/-- Helper for Lemma 18.27.1: transporting the evaluation of a localized Hom along an equality of
slice objects is definitionally the same as evaluating after transport. -/
private theorem hom_app_transport_apply
    {U : C} (φ : overHom 𝒪 ℱ 𝒢 U) {X Y : (Over U)ᵒᵖ} (h : X = Y)
    (x : (overPresheafModule 𝒪 ℱ U).obj X) :
    h ▸ ModuleCat.Hom.hom (φ.app X) x =
      ModuleCat.Hom.hom (φ.app Y) (h ▸ x) := by
  -- Once the slice-object equality is reflexive, both sides are literally the same term.
  cases h
  rfl

/-- Helper for Lemma 18.27.1: the whole pushed-forward component of a localized Hom is unchanged
under identity relocalization. -/
private theorem localHomMap_id_app_eq
    (U : Cᵒᵖ) (φ : overHom 𝒪 ℱ 𝒢 U.unop) (X : (Over U.unop)ᵒᵖ) :
    (localHomMap 𝒪 ℱ 𝒢 (𝟙 U) φ).app X = φ.app X := by
  -- Route correction: normalize the entire pushed-forward component before evaluating it.
  rw [localHomMap_app]
  -- The relocalized slice object is the original object because the relocalization arrow is the
  -- identity.
  have hX : op ((Over.map (𝟙 U.unop)).obj X.unop) = X := by
    simpa using congrArg op (over_map_id_obj_eq (U := U) X.unop)
  simpa [hX] using (hom_app_transport (𝒪 := 𝒪) (ℱ := ℱ) (𝒢 := 𝒢) φ hX)

/-- Helper for Lemma 18.27.1: the whole pushed-forward component of a localized Hom along a
composite relocalization agrees with the iterated pushed-forward component. -/
private theorem localHomMap_comp_app_eq
    {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W)
    (φ : overHom 𝒪 ℱ 𝒢 U.unop) (X : (Over W.unop)ᵒᵖ) :
    (localHomMap 𝒪 ℱ 𝒢 (f ≫ g) φ).app X =
      (localHomMap 𝒪 ℱ 𝒢 g (localHomMap 𝒪 ℱ 𝒢 f φ)).app X := by
  -- Route correction: normalize both sides to `φ.app` at the corresponding relocalized slice
  -- object, then compare those slice objects directly.
  rw [localHomMap_app, localHomMap_app, localHomMap_app]
  -- Composite relocalization and iterated relocalization produce the same slice object.
  have hX :
      op ((Over.map (g.unop ≫ f.unop)).obj X.unop) =
        op ((Over.map f.unop).obj ((Over.map g.unop).obj X.unop)) := by
    simpa using congrArg op
      (over_map_comp_obj_eq (f := f) (g := g) X.unop)
  simpa [hX] using (hom_app_transport (𝒪 := 𝒪) (ℱ := ℱ) (𝒢 := 𝒢) φ hX)

/-- Helper for Lemma 18.27.1: if two slice-object indices agree, evaluating on the first index
with the input transported back to it agrees with evaluation on the second index. -/
private theorem hom_app_eq_of_eq
    {U : C} (φ : overHom 𝒪 ℱ 𝒢 U) {X Y : (Over U)ᵒᵖ} (h : X = Y)
    (x : (overPresheafModule 𝒪 ℱ U).obj Y) :
    ModuleCat.Hom.hom (φ.app X) (h.symm ▸ x) =
      h.symm ▸ ModuleCat.Hom.hom (φ.app Y) x := by
  -- Once the slice-object equality is reflexive, the transported input is just `x`.
  cases h
  rfl

/-- Helper for Lemma 18.27.1: the exact evaluation-level transport left after rewriting
`localHomMap_app` is definitionally trivial once the slice-object equality is reflexive. -/
private theorem hom_app_eval_transport_ndrec
    {U : C} (φ : overHom 𝒪 ℱ 𝒢 U) {X Y : (Over U)ᵒᵖ} (h : X = Y)
    (x : (overPresheafModule 𝒪 ℱ U).obj Y) :
    Eq.ndrec
        (motive := fun Z ↦ (overPresheafModule 𝒪 𝒢.val U).obj Z)
        (ModuleCat.Hom.hom (φ.app X) (h.symm ▸ x)) h =
      ModuleCat.Hom.hom (φ.app Y) x := by
  -- The dependent transport disappears after reducing to the reflexive equality case.
  cases h
  rfl

/-- Helper for Lemma 18.27.1: pushing a localized Hom along the identity arrow is the identity. -/
private theorem localHomMap_id_apply
    (U : Cᵒᵖ) (φ : overHom 𝒪 ℱ 𝒢 U.unop) :
    localHomMap 𝒪 ℱ 𝒢 (𝟙 U) φ = φ := by
  -- Evaluate both natural transformations at each slice object and use the owner-level component
  -- normalization for identity relocalization.
  ext X x
  rw [localHomMap_id_app_eq]

/-- Helper for Lemma 18.27.1: pushing a localized Hom along a composite is the composite of the
two pushforwards. -/
private theorem localHomMap_comp_apply
    {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) (φ : overHom 𝒪 ℱ 𝒢 U.unop) :
    localHomMap 𝒪 ℱ 𝒢 (f ≫ g) φ =
      localHomMap 𝒪 ℱ 𝒢 g (localHomMap 𝒪 ℱ 𝒢 f φ) := by
  -- Evaluate both natural transformations at each slice object and compare the normalized
  -- pushed-forward components.
  ext X x
  rw [localHomMap_comp_app_eq]

/-- Helper for Lemma 18.27.1: pushing a localized Hom past restriction commutes with
postcomposition by localized scalar multiplication. -/
private theorem localHomMap_postcompose_localSectionMul
    {U V : Cᵒᵖ} (f : U ⟶ V) (r : (underlyingRingSheaf 𝒪).obj.obj U)
    (φ : overHom 𝒪 ℱ 𝒢 U.unop) :
    localHomMap 𝒪 ℱ 𝒢 f (φ ≫ localSectionMul 𝒪 𝒢.val U.unop r) =
      localHomMap 𝒪 ℱ 𝒢 f φ ≫
        localSectionMul 𝒪 𝒢.val V.unop ((underlyingRingSheaf 𝒪).obj.map f r) := by
  -- Compare both sides objectwise on the target slice.
  ext X x
  let Y : (Over U.unop)ᵒᵖ := op ((Over.map f.unop).obj X.unop)
  -- Both sides evaluate the same localized map `φ.app Y` followed by scalar multiplication by the
  -- restricted section on the relocalized object.
  change
    localSectionMulApp 𝒪 𝒢.val U.unop r Y ((φ.app Y) x) =
      localSectionMulApp 𝒪 𝒢.val V.unop ((underlyingRingSheaf 𝒪).obj.map f r) X
        ((φ.app Y) x)
  rw [localSectionMulApp_apply, localSectionMulApp_apply]
  have hrestrict :
      (show ((underlyingRingSheaf 𝒪).over U.unop).obj.obj Y from
        ((underlyingRingSheaf 𝒪).obj.map (op Y.unop.hom) r)) =
      (show ((underlyingRingSheaf 𝒪).over V.unop).obj.obj X from
        ((underlyingRingSheaf 𝒪).obj.map (op X.unop.hom)
          (((underlyingRingSheaf 𝒪).obj.map f) r))) := by
    change
      (underlyingRingSheaf 𝒪).obj.map
          (f ≫ (show op V.unop ⟶ op X.unop.left from op X.unop.hom)) r =
        (underlyingRingSheaf 𝒪).obj.map (show op V.unop ⟶ op X.unop.left from op X.unop.hom)
          (((underlyingRingSheaf 𝒪).obj.map f) r)
    -- The relocalized object has structure map `X.unop.hom ≫ f.unop`.
    simpa using
      (underlying_ring_map_comp_apply (𝒪 := 𝒪) (a := f)
        (b := (show op V.unop ⟶ op X.unop.left from op X.unop.hom)) r).symm
  rw [hrestrict]
  rfl

private instance overHomSMul (U : C) :
    SMul ((underlyingRingSheaf 𝒪).obj.obj (op U)) (overHom 𝒪 ℱ 𝒢 U) where
  smul r φ := φ ≫ localSectionMul 𝒪 𝒢.val U r

private instance overHomModule (U : C) :
    Module ((underlyingRingSheaf 𝒪).obj.obj (op U)) (overHom 𝒪 ℱ 𝒢 U) where
  one_smul φ := by
    -- Scalar multiplication is postcomposition with the localized multiplication endomorphism.
    change φ ≫ localSectionMul 𝒪 𝒢.val U 1 = φ
    rw [localSectionMul_one]
    simp
  mul_smul r s φ := by
    -- Multiplication of scalars becomes composition of the corresponding endomorphisms.
    change φ ≫ localSectionMul 𝒪 𝒢.val U (r * s) =
        (φ ≫ localSectionMul 𝒪 𝒢.val U s) ≫ localSectionMul 𝒪 𝒢.val U r
    rw [localSectionMul_mul]
    simp [Category.assoc]
  smul_add r φ ψ := by
    -- Postcomposition is additive in the morphism being postcomposed.
    change (φ + ψ) ≫ localSectionMul 𝒪 𝒢.val U r =
        φ ≫ localSectionMul 𝒪 𝒢.val U r + ψ ≫ localSectionMul 𝒪 𝒢.val U r
    simp
  smul_zero r := by
    -- Postcomposing the zero morphism remains zero.
    change (0 : overHom 𝒪 ℱ 𝒢 U) ≫ localSectionMul 𝒪 𝒢.val U r = 0
    simp
  add_smul r s φ := by
    -- Addition of scalars is computed by addition of the corresponding endomorphisms.
    change φ ≫ localSectionMul 𝒪 𝒢.val U (r + s) =
        φ ≫ localSectionMul 𝒪 𝒢.val U r + φ ≫ localSectionMul 𝒪 𝒢.val U s
    rw [localSectionMul_add]
    simp
  zero_smul φ := by
    -- The zero section acts by the zero endomorphism.
    change φ ≫ localSectionMul 𝒪 𝒢.val U 0 = 0
    rw [localSectionMul_zero]
    simp

/-- The underlying abelian-group-valued presheaf of the local `𝒪`-module Hom object. -/
private def localHomToPresheaf
    (ℱ : PresheafOfModules (underlyingRingSheaf 𝒪).obj)
    (𝒢 : SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)) :
    Cᵒᵖ ⥤ AddCommGrpCat.{max u v} where
  obj U := AddCommGrpCat.of (overHom 𝒪 ℱ 𝒢 U.unop)
  map {U V} f := AddCommGrpCat.ofHom
    { toFun := localHomMap 𝒪 ℱ 𝒢 f
      map_zero' := by
        -- Pushforward along `Over.map f.unop` sends the zero natural transformation to zero
        -- objectwise.
        ext X x
        rfl
      map_add' := by
        intro φ ψ
        -- Addition of localized Homs is computed objectwise after pushforward.
        ext X x
        rfl }
  map_id := by
    -- Restricting along the identity arrow does not change a localized Hom.
    intro U
    ext φ X x
    exact congrArg (fun ψ ↦ ModuleCat.Hom.hom (ψ.app X) x) (localHomMap_id_apply 𝒪 ℱ 𝒢 U φ)
  map_comp := by
    -- Successive restrictions agree definitionally with restriction along the composite.
    intro U V W f g
    ext φ X x
    exact congrArg (fun ψ ↦ ModuleCat.Hom.hom (ψ.app X) x)
      (localHomMap_comp_apply 𝒪 ℱ 𝒢 f g φ)

private instance localHomToPresheaf_objModule (U : Cᵒᵖ) :
    Module ((underlyingRingSheaf 𝒪).obj.obj U) ((localHomToPresheaf 𝒪 ℱ 𝒢).obj U) :=
  overHomModule 𝒪 ℱ 𝒢 U.unop

/-- The local `𝒪`-linear Hom presheaf. -/
def localHomPresheaf
    (ℱ : PresheafOfModules (underlyingRingSheaf 𝒪).obj)
    (𝒢 : SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)) :
    PresheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).obj :=
  ofPresheaf (localHomToPresheaf 𝒪 ℱ 𝒢)
    (fun {U V} f r φ ↦ by
      -- Expand scalar multiplication on `overHom` to postcomposition with localized scalar
      -- multiplication, then invoke the pointwise commutation lemma above.
      change
        localHomMap 𝒪 ℱ 𝒢 f (φ ≫ localSectionMul 𝒪 𝒢.val U.unop r) =
          localHomMap 𝒪 ℱ 𝒢 f φ ≫
            localSectionMul 𝒪 𝒢.val V.unop ((underlyingRingSheaf 𝒪).obj.map f r)
      simpa using
        localHomMap_postcompose_localSectionMul (𝒪 := 𝒪) (ℱ := ℱ) (𝒢 := 𝒢) f r φ)

/- Lemma 18.27.1: for a site `(\mathcal C, J)`, a sheaf of commutative rings
`\mathcal O`, a presheaf of `\mathcal O`-modules `\mathcal F`, and a sheaf of
`\mathcal O`-modules `\mathcal G`, the local Hom object
`\mathcal H\!\mathit{om}_{\mathcal O}(\mathcal F, \mathcal G)` is a sheaf of
`\mathcal O`-modules. Its underlying presheaf owner is `localHomPresheaf 𝒪 ℱ 𝒢`. -/
/-- Helper for Lemma 18.27.1: on the slice site over `U`, local morphisms from `ℱ` to `𝒢`
identify with local morphisms from the sheafification of `ℱ|_U` to `𝒢|_U`. -/
private noncomputable def localizedHomEquivSheafifiedSource
    (U : C) :
    overHom 𝒪 ℱ 𝒢 U ≃
      ((PresheafOfModules.sheafification
          (𝟙 (((underlyingRingSheaf 𝒪).over U).obj))).obj
        (overPresheafModule 𝒪 ℱ U) ⟶ 𝒢.over U) := by
  -- Proof comment: this is the slice-site specialization of the module-sheafification adjunction
  -- along the identity ring map on the localized structure sheaf.
  simpa [overHom] using
    (((PresheafOfModules.sheafificationAdjunction
        (𝟙 (((underlyingRingSheaf 𝒪).over U).obj))).homEquiv
      (overPresheafModule 𝒪 ℱ U) (𝒢.over U)).symm)

theorem internalHom_isSheaf :
    Presheaf.IsSheaf J (localHomPresheaf 𝒪 ℱ 𝒢).presheaf := by
  -- TODO: route correction. The remaining blocker is not the cover-based sheaf skeleton itself but
  -- the missing bridge from module-valued local Homs to the set-valued slice-site gluing API of
  -- `Lemma_7_26_1`. The next pass should either add the module-valued cover-arrow restriction
  -- formula for `localizedHomEquivSheafifiedSource` and recover linearity after gluing, or expose
  -- a canonical module-level prestack lemma for slice restrictions.
  sorry

/-- The sheaf of `\mathcal O`-modules `\mathcal H\!\mathit{om}_{\mathcal O}(\mathcal F,
\mathcal G)` from Lemma 18.27.1. -/
def localHomSheaf
    (ℱ : PresheafOfModules (underlyingRingSheaf 𝒪).obj)
    (𝒢 : SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)) :
    SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪) where
  val := localHomPresheaf 𝒪 ℱ 𝒢
  isSheaf := internalHom_isSheaf 𝒪 ℱ 𝒢

section IHomBridge

open CategoryTheory

variable [MonoidalCategory (SheafOfModules ((sheafCompose J
  (forget₂ CommRingCat RingCat)).obj 𝒪))]
variable [MonoidalClosed (SheafOfModules ((sheafCompose J
  (forget₂ CommRingCat RingCat)).obj 𝒪))]

/-- Helper for Lemma 18.27.1: sections of a module sheaf on the slice site `C / U` are recovered
by evaluation at the terminal object `U → U`. -/
private noncomputable def overSectionsEquivEvaluation
    {U : C} (M : SheafOfModules ((underlyingRingSheaf 𝒪).over U)) :
    M.sections ≃ M.val.obj (op (Over.mk (𝟙 U))) where
  toFun s := s.1 (op (Over.mk (𝟙 U)))
  invFun m :=
    M.val.sectionsMk
      (fun W ↦ M.val.map ((Over.mkIdTerminal.from W.unop).op) m)
      (fun W Y f ↦ by
        -- Proof comment: every object of the slice has a unique map to the terminal object.
        have h :
            (Over.mkIdTerminal.from W.unop).op ≫ f = (Over.mkIdTerminal.from Y.unop).op := by
          apply Quiver.Hom.unop_inj
          simp only [Quiver.Hom.unop_op]
          exact Over.mkIdTerminal.hom_ext
            (f.unop ≫ Over.mkIdTerminal.from W.unop)
            (Over.mkIdTerminal.from Y.unop)
        rw [← PresheafOfModules.map_comp_apply, h])
  left_inv s := by
    -- Proof comment: a section is determined by its restrictions from the terminal object.
    ext W
    simpa using PresheafOfModules.sections_property s ((Over.mkIdTerminal.from W.unop).op)
  right_inv m := by
    -- Proof comment: the reconstructed section evaluates back to `m` at the terminal object.
    change M.val.map ((Over.mkIdTerminal.from (Over.mk (𝟙 U))).op) m = m
    have h :
        Over.mkIdTerminal.from (Over.mk (𝟙 U)) = 𝟙 (Over.mk (𝟙 U)) :=
      Over.mkIdTerminal.hom_ext _ _
    simpa using M.val.congr_map_apply (congrArg Quiver.Hom.op h) m

/-- Helper for Lemma 18.27.1: under terminal evaluation, a section map is the terminal component
of the corresponding sheaf morphism. -/
private theorem overSectionsEquivEvaluation_sectionsMap
    {U : C} {M N : SheafOfModules ((underlyingRingSheaf 𝒪).over U)}
    (ψ : M ⟶ N) (s : M.sections) :
    (overSectionsEquivEvaluation N) (SheafOfModules.sectionsMap ψ s) =
      (ψ.val.app (op (Over.mk (𝟙 U)))) ((overSectionsEquivEvaluation M) s) := by
  -- Proof comment: both sides are definitionally evaluation of the mapped section at `U → U`.
  rfl

/-- Helper for Lemma 18.27.1: the inverse of terminal evaluation is natural in the sheaf
morphism. -/
private theorem sectionsMap_overSectionsEquivEvaluation_symm
    {U : C} {M N : SheafOfModules ((underlyingRingSheaf 𝒪).over U)}
    (ψ : M ⟶ N) (m : M.val.obj (op (Over.mk (𝟙 U)))) :
    SheafOfModules.sectionsMap ψ ((overSectionsEquivEvaluation M).symm m) =
      (overSectionsEquivEvaluation N).symm
        ((ψ.val.app (op (Over.mk (𝟙 U)))) m) := by
  -- Proof comment: evaluate both sections at the terminal object and compare their terminal
  -- components.
  apply (overSectionsEquivEvaluation N).injective
  rw [overSectionsEquivEvaluation_sectionsMap]
  simp

/-- Helper for Lemma 18.27.1: a value of the canonical internal-Hom sheaf at `U` is the same
thing as a local morphism `ℱ|_U ⟶ 𝒢|_U`. -/
private noncomputable def siteInternalHomObjEquivOverHom_e₁
    (ℱ 𝒢 : SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪))
    (U : C) :
    (((ihom ℱ).obj 𝒢).val.obj (op U)) ≃ ((((ihom ℱ).obj 𝒢).over U).sections) := by
  -- Proof comment: terminal evaluation identifies a section on the slice with its value at
  -- `U ⟶ U`.
  simpa using (overSectionsEquivEvaluation (((ihom ℱ).obj 𝒢).over U)).symm

/-- Helper for Lemma 18.27.1: sections of the restricted internal-Hom sheaf correspond to
unit-object morphisms on the slice site. -/
private noncomputable def siteInternalHomObjEquivOverHom_e₂
    (ℱ 𝒢 : SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪))
    (U : C) :
    ((((ihom ℱ).obj 𝒢).over U).sections) ≃
      (SheafOfModules.unit ((underlyingRingSheaf 𝒪).over U) ⟶ (((ihom ℱ).obj 𝒢).over U)) :=
  ((((ihom ℱ).obj 𝒢).over U).unitHomEquiv).symm

/-- Helper for Lemma 18.27.1: the adjunction/unitor step identifies a unit morphism into the
restricted internal-Hom sheaf with a local morphism `ℱ|_U ⟶ 𝒢|_U`. -/
private noncomputable def siteInternalHomObjEquivOverHom_e₃
    (ℱ 𝒢 : SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪))
    (U : C) :
    (SheafOfModules.unit ((underlyingRingSheaf 𝒪).over U) ⟶ (((ihom ℱ).obj 𝒢).over U)) ≃
      (ℱ.over U ⟶ 𝒢.over U) := by
  -- Proof comment: uncurry across the closed structure on the slice category and then remove the
  -- left tensor unit.
  simpa using
    ((((ihom.adjunction (ℱ.over U)).homEquiv
        (SheafOfModules.unit ((underlyingRingSheaf 𝒪).over U))
        (𝒢.over U)).symm).trans
      (((λ_ (ℱ.over U)).symm.homCongr (Iso.refl (𝒢.over U)))))

/-- Helper for Lemma 18.27.1: the inverse of the adjunction/unitor factor is the adjunction image
of the left-unitor composite. -/
private theorem siteInternalHomObjEquivOverHom_e₃_symm_formula
    (ℱ 𝒢 : SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪))
    (U : C) (φ : ℱ.over U ⟶ 𝒢.over U) :
    (siteInternalHomObjEquivOverHom_e₃ (𝒪 := 𝒪) ℱ 𝒢 U).symm φ =
      (ihom.adjunction (ℱ.over U)).homEquiv
        (SheafOfModules.unit ((underlyingRingSheaf 𝒪).over U))
        (𝒢.over U) ((λ_ (ℱ.over U)).hom ≫ φ) := by
  -- Proof comment: apply the third factor again and simplify the transport hidden in
  -- `Iso.homCongr`.
  apply (siteInternalHomObjEquivOverHom_e₃ (𝒪 := 𝒪) ℱ 𝒢 U).injective
  simpa [siteInternalHomObjEquivOverHom_e₃]

/-- Helper for Lemma 18.27.1: a value of the canonical internal-Hom sheaf at `U` is the same
thing as a local morphism `ℱ|_U ⟶ 𝒢|_U`. -/
private noncomputable def siteInternalHomObjEquivOverHom
    (ℱ 𝒢 : SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪))
    (U : C) :
    (((ihom ℱ).obj 𝒢).val.obj (op U)) ≃ (ℱ.over U ⟶ 𝒢.over U) := by
  -- Proof comment: evaluate the restricted internal-Hom sheaf at the terminal slice object, turn
  -- the resulting section into a unit morphism, and finally uncurry across the closed structure.
  exact (siteInternalHomObjEquivOverHom_e₁ (𝒪 := 𝒪) ℱ 𝒢 U).trans
    ((siteInternalHomObjEquivOverHom_e₂ (𝒪 := 𝒪) ℱ 𝒢 U).trans
      (siteInternalHomObjEquivOverHom_e₃ (𝒪 := 𝒪) ℱ 𝒢 U))

/-- When the source presheaf actually comes from a sheaf of `\mathcal O`-modules, the
source-facing local Hom sheaf from Lemma 18.27.1 is canonically isomorphic to the chapter's
internal-Hom owner `ihom`. -/
theorem localHomSheaf_isomorphic_ihom
    (ℱ 𝒢 : SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)) :
    IsIsomorphic (localHomSheaf 𝒪 ℱ.val 𝒢) ((ihom ℱ).obj 𝒢) := by
  -- TODO: once `internalHom_isSheaf` is finished, the remaining work is a presheaf-of-modules
  -- comparison. The blocked step is the naturality/linearity package for
  -- `siteInternalHomObjEquivOverHom`; after that, `NatIso.ofComponents` plus
  -- `SheafOfModules.forget ... .preimageIso` should finish the theorem.
  sorry

end IHomBridge

end PresheafOfModules

namespace SheafOfModules

open CategoryTheory Opposite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable (𝒪 : Sheaf J CommRingCat.{max u v})

/-- Multiplication by a local section on the restriction of a sheaf of `\mathcal O`-modules to
the slice site `C / U`. This is the sheaf-level owner induced by the Chapter 18 presheaf
construction. -/
noncomputable abbrev localSectionMul
    (ℱ : SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪))
    (U : C) (r : ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).obj.obj (op U)) :
    ℱ.over U ⟶ ℱ.over U where
  val := PresheafOfModules.localSectionMul 𝒪 ℱ.val U r

end SheafOfModules
