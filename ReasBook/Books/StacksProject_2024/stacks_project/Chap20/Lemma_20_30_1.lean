import StacksProject_2024.Chap06.Definition_6_27_1
import StacksProject_2024.Chap14.Example_14_33_1
import StacksProject_2024.Chap14.Lemma_14_33_2
import StacksProject_2024.Chap14.Lemma_14_28_5
import StacksProject_2024.Chap14.Lemma_14_28_7
import StacksProject_2024.Chap17.Definition_17_20_1
import StacksProject_2024.Chap17.ModuleRestrictionAndStalks
import StacksProject_2024.Chap20.«20_11_0_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicTopology
open AlgebraicGeometry
open scoped RingedSpace.Hom
open scoped AlgebraicGeometry
open scoped IteratedEndofunctor
open scoped BigOperators

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.30.1:
- primary domain: sheaves of modules on a ringed space, their pointwise pullback/pushforward along
  the one-point inclusions `i_x : ({x}, 𝒪_{X,x}) ⟶ X`, and the resulting homotopy and
  quasi-isomorphism statements for cochain complexes;
- sampled owner declarations:
  `RingedSpace.Hom.pullback`,
  `RingedSpace.Hom.pushforward`,
  `SheafOfModules.pullbackPushforwardAdjunction`,
  `RingedSpace.stalkModuleFunctor`,
  `iteratedEndofunctor`,
  `moduleUnderlyingSheaf`,
  `HomologicalComplex.homotopyEquivalences`;
  endofunctor `godementStep X` and its unit `godementUnit X`. The explicit pointwise
  pullback/pushforward product remains bridge data for the step endofunctor, while flasqueness,
  quasi-isomorphism, and stalkwise homotopy are exported only through the source-facing existence
  theorem `exists_functorial_godement_resolution`, with the pointwise clause expressed through the
  canonical stalk functor rather than through a public pullback-to-`pointRingedSpace x` bridge;
- primitive data: the one-point inclusion `pointInclusion x` for each `x : X` and the resulting
  pointwise pullback/pushforward endofunctors, together with the canonical unit
  `𝟭 ⟶ godementStep X`;
- derived API: the source-facing existence theorem for a functorial Godement resolution together
  with its quasi-isomorphism / flasqueness / stalkwise homotopy clauses.

Source/core/bridge triage:
- `source-facing`: existence of a functorial Godement resolution with its source-level
  quasi-isomorphism, flasqueness, and stalkwise homotopy properties;
- `core/canonical`: `i_x^*`, `i_{x,*}`, `RingedSpace.stalkModuleFunctor`,
  `QuasiIso`, and `homotopyEquivalences`;
- `bridge/view`: the dependent family/product realization of the Godement step and the inserted-unit
  maps built from the Chapter 14 endofunctor owner.

The old private family functors were only bridge data duplicating the canonical pullback/pushforward
owners. The public surface should therefore keep the Godement step and its unit as reusable bridge
data, but expose the actual resolution only through theorem-level API. -/

private abbrev pointGodementStep (X : RingedSpace.{u}) (x : X) :
    X.Modules ⥤ X.Modules :=
  ((pointInclusion x)^*) ⋙ ((pointInclusion x) _*)

/-- The canonical pullback/pushforward adjunction attached to the point inclusion `i_x`. -/
private abbrev pointGodementAdjunction (X : RingedSpace.{u}) (x : X) :=
  SheafOfModules.pullbackPushforwardAdjunction
    (RingedSpace.Hom.toRingCatSheafHom (pointInclusion x))

/-- The Godement step endofunctor on `𝒪_X`-modules, obtained by pulling back to each
one-point ringed space `({x}, 𝒪_{X, x})`, pushing forward again along `i_x`, and taking
the product over all `x : X`. -/
def godementStep (X : RingedSpace.{u}) :
    X.Modules ⥤ X.Modules where
  obj ℱ := ∏ᶜ fun x : X ↦ (pointGodementStep X x).obj ℱ
  map φ := Limits.Pi.map (fun x : X ↦ (pointGodementStep X x).map φ)
  map_id ℱ := by
    apply Pi.hom_ext
    intro x
    simp
  map_comp φ ψ := by
    apply Pi.hom_ext
    intro x
    simp [Category.assoc]

/-- The Godement step functor preserves zero morphisms. -/
instance godementStep_preservesZeroMorphisms (X : RingedSpace.{u}) :
    (godementStep X).PreservesZeroMorphisms where
  map_zero ℱ 𝒢 := by
    apply Pi.hom_ext
    intro x
    have hx : (pointGodementStep X x).map (0 : ℱ ⟶ 𝒢) = 0 := by
      simpa using (Functor.map_zero (pointGodementStep X x) ℱ 𝒢)
    simp only [godementStep, Limits.Pi.map_π]
    rw [hx, comp_zero]
    exact (zero_comp : (0 : (∏ᶜ fun y : X ↦ (pointGodementStep X y).obj ℱ) ⟶
      ∏ᶜ fun y : X ↦ (pointGodementStep X y).obj 𝒢) ≫
        Pi.π (fun y : X ↦ (pointGodementStep X y).obj 𝒢) x = 0).symm

/-- Every iterated Godement step also sends the zero map to zero. -/
theorem iterated_godementStep_map_zero
    (X : RingedSpace.{u}) (ℱ 𝒢 : X.Modules) (n : ℕ) :
    (CategoryTheory.iteratedEndofunctor (godementStep X) n).map (0 : ℱ ⟶ 𝒢) = 0 := by
  let _ := godementStep_preservesZeroMorphisms X
  induction n with
  | zero =>
      rw [CategoryTheory.iteratedEndofunctor]
      exact Functor.map_zero (godementStep X) ℱ 𝒢
  | succ n ih =>
      rw [CategoryTheory.iteratedEndofunctor]
      simp [ih, Functor.map_zero]
      rfl

/-- The canonical unit `ℱ ⟶ ∏ x, i_{x,*} i_x^* ℱ` of the Godement step. -/
def godementUnit (X : RingedSpace.{u}) :
    𝟭 X.Modules ⟶ godementStep X where
  app ℱ :=
    Pi.lift fun x : X ↦
      (pointGodementAdjunction X x).unit.app ℱ
  naturality := by
    intro ℱ 𝒢 φ
    apply Pi.hom_ext
    intro x
    change
      (φ ≫
          Pi.lift fun x : X ↦ (pointGodementAdjunction X x).unit.app 𝒢) ≫
        Pi.π (fun x : X ↦ (pointGodementStep X x).obj 𝒢) x =
      ((Pi.lift fun x : X ↦ (pointGodementAdjunction X x).unit.app ℱ) ≫
          Limits.Pi.map (fun x : X ↦ (pointGodementStep X x).map φ)) ≫
        Pi.π (fun x : X ↦ (pointGodementStep X x).obj 𝒢) x
    rw [Category.assoc, Pi.lift_π, Category.assoc, Limits.Pi.map_π, ← Category.assoc, Pi.lift_π]
    simpa [Category.assoc] using
      (pointGodementAdjunction X x).unit.naturality φ

@[simp] theorem godementUnit_app_π
    (X : RingedSpace.{u}) (ℱ : X.Modules) (x : X) :
    (godementUnit X).app ℱ ≫
        Pi.π (fun y : X ↦ (((pointInclusion y)^*) ⋙ ((pointInclusion y) _*)).obj ℱ) x =
      (SheafOfModules.pullbackPushforwardAdjunction
        (RingedSpace.Hom.toRingCatSheafHom (pointInclusion x))).unit.app ℱ := by
  simpa [godementUnit, pointGodementAdjunction, pointGodementStep] using
    (Pi.lift_π (fun y : X ↦ (pointGodementAdjunction X y).unit.app ℱ) x)

/-- Helper for Lemma 20.30.1: the Godement unit packaged functorially as an arrow in
`RingedSpace.Modules X`. -/
private def godementUnitArrowFunctor (X : RingedSpace.{u}) :
    X.Modules ⥤ Arrow X.Modules where
  obj ℱ := Arrow.mk ((godementUnit X).app ℱ)
  map φ := Arrow.homMk φ ((godementStep X).map φ) (by
    -- Proof comment: the square for the arrow map is exactly the naturality square of the unit.
    simpa using (godementUnit X).naturality φ)
  map_id ℱ := by
    -- Proof comment: both arrow components are identities after functoriality of `godementStep`.
    ext <;> simp
  map_comp φ ψ := by
    -- Proof comment: composition is degreewise composition of the two arrow components.
    ext <;> simp

/-- Helper for Lemma 20.30.1: the module-sheaf category on a ringed space has the wide pushouts
needed to form Čech conerves of the Godement unit arrows. -/
private instance godementResolution_hasWidePushout (X : RingedSpace.{u}) :
    ∀ (n : ℕ) (f : Arrow X.Modules), HasWidePushout f.left
      (fun _ : Fin (n + 1) ↦ f.right) (fun _ ↦ f.hom) := by
  intro n f
  infer_instance

/-- Helper for Lemma 20.30.1: the ordinary Godement complex obtained from the Čech conerve of the
Godement unit. -/
private noncomputable abbrev godementResolutionFunctor (X : RingedSpace.{u}) :
    X.Modules ⥤ CochainComplex X.Modules ℕ :=
  godementUnitArrowFunctor X ⋙
    (CategoryTheory.CosimplicialObject.cechConerve :
      Arrow X.Modules ⥤ CosimplicialObject X.Modules) ⋙
    alternatingCofaceMapComplex X.Modules

/-- Helper for Lemma 20.30.1: the Godement complex attached to a fixed module `ℱ`. -/
private noncomputable abbrev godementResolutionObj
    (X : RingedSpace.{u}) (ℱ : X.Modules) :
    CochainComplex X.Modules ℕ :=
  (godementResolutionFunctor X).obj ℱ

/-- Helper for Lemma 20.30.1: the degree-zero augmentation map into the ordinary Godement
complex. -/
private noncomputable abbrev godementResolutionAugmentationMap
    (X : RingedSpace.{u}) (ℱ : X.Modules) :
    ℱ ⟶ (godementResolutionObj X ℱ).X 0 := by
  -- Proof comment: this is the degree-zero component of the augmented Čech-conerve
  -- coaugmentation, transported into the Godement complex notation.
  simpa [godementResolutionObj, godementResolutionFunctor, godementUnitArrowFunctor] using
    (Arrow.mk ((godementUnit X).app ℱ)).augmentedCechConerve.hom.app (SimplexCategory.mk 0)

/-- Helper for Lemma 20.30.1: the degree-zero augmentation is a cocycle for the ordinary
Godement complex. -/
private theorem godementResolution_d_zero_one_eq
    (X : RingedSpace.{u}) (ℱ : X.Modules) :
    (godementResolutionObj X ℱ).d 0 1 =
      ((Arrow.mk ((godementUnit X).app ℱ)).cechConerve).δ 0 -
        ((Arrow.mk ((godementUnit X).app ℱ)).cechConerve).δ 1 := by
  let δ₀ : (godementResolutionObj X ℱ).X 0 ⟶ (godementResolutionObj X ℱ).X 1 :=
    ((Arrow.mk ((godementUnit X).app ℱ)).cechConerve).δ 0
  let δ₁ : (godementResolutionObj X ℱ).X 0 ⟶ (godementResolutionObj X ℱ).X 1 :=
    ((Arrow.mk ((godementUnit X).app ℱ)).cechConerve).δ 1
  -- Proof comment: degree `0 → 1` in an alternating coface complex is the two-term alternating
  -- sum of the first two cofaces.
  rw [show (godementResolutionObj X ℱ).d 0 1 =
      AlgebraicTopology.AlternatingCofaceMapComplex.objD
        ((Arrow.mk ((godementUnit X).app ℱ)).cechConerve) 0 by
      rfl]
  rw [AlgebraicTopology.AlternatingCofaceMapComplex.objD, Fin.sum_univ_two]
  change (-1 : ℤ) ^ (0 : ℕ) • δ₀ + (-1 : ℤ) ^ (1 : ℕ) • δ₁ = δ₀ - δ₁
  norm_num
  rw [sub_eq_add_neg]

/-- Helper for Lemma 20.30.1: composing the degree-zero Godement augmentation with the first
coface yields the degree-one Čech coaugmentation component. -/
private theorem godementResolutionAugmentationMap_comp_coface_zero
    (X : RingedSpace.{u}) (ℱ : X.Modules) :
    godementResolutionAugmentationMap X ℱ ≫
      ((Arrow.mk ((godementUnit X).app ℱ)).cechConerve).δ 0 =
        (Arrow.mk ((godementUnit X).app ℱ)).augmentedCechConerve.hom.app
          (SimplexCategory.mk 1) := by
  -- Proof comment: this is the `δ₀` naturality square of the Čech coaugmentation.
  simpa [godementResolutionAugmentationMap, godementResolutionObj, godementResolutionFunctor,
    godementUnitArrowFunctor] using
    ((Arrow.mk ((godementUnit X).app ℱ)).augmentedCechConerve.hom.naturality
      (SimplexCategory.δ 0)).symm

/-- Helper for Lemma 20.30.1: composing the degree-zero Godement augmentation with the second
coface also yields the degree-one Čech coaugmentation component. -/
private theorem godementResolutionAugmentationMap_comp_coface_one
    (X : RingedSpace.{u}) (ℱ : X.Modules) :
    godementResolutionAugmentationMap X ℱ ≫
      ((Arrow.mk ((godementUnit X).app ℱ)).cechConerve).δ 1 =
        (Arrow.mk ((godementUnit X).app ℱ)).augmentedCechConerve.hom.app
          (SimplexCategory.mk 1) := by
  -- Proof comment: the same Čech naturality argument applies to `δ₁`.
  simpa [godementResolutionAugmentationMap, godementResolutionObj, godementResolutionFunctor,
    godementUnitArrowFunctor] using
    ((Arrow.mk ((godementUnit X).app ℱ)).augmentedCechConerve.hom.naturality
      (SimplexCategory.δ 1)).symm

/-- Helper for Lemma 20.30.1: the degree-zero augmentation is a cocycle for the ordinary
Godement complex. -/
private theorem godementResolutionAugmentationMap_comp_d_zero_one
    (X : RingedSpace.{u}) (ℱ : X.Modules) :
    godementResolutionAugmentationMap X ℱ ≫ (godementResolutionObj X ℱ).d 0 1 = 0 := by
  let α : ℱ ⟶ (godementResolutionObj X ℱ).X 0 := godementResolutionAugmentationMap X ℱ
  let δ₀ : (godementResolutionObj X ℱ).X 0 ⟶ (godementResolutionObj X ℱ).X 1 :=
    ((Arrow.mk ((godementUnit X).app ℱ)).cechConerve).δ 0
  let δ₁ : (godementResolutionObj X ℱ).X 0 ⟶ (godementResolutionObj X ℱ).X 1 :=
    ((Arrow.mk ((godementUnit X).app ℱ)).cechConerve).δ 1
  -- Proof comment: rewrite the first differential as `δ₀ - δ₁` and identify both composites with
  -- the same degree-one Čech coaugmentation component.
  rw [godementResolution_d_zero_one_eq]
  change α ≫ (δ₀ - δ₁) = 0
  calc
    α ≫ (δ₀ - δ₁) = α ≫ δ₀ - α ≫ δ₁ := by
      exact CategoryTheory.Preadditive.comp_sub _ _ _
    _ = 0 := by
      rw [show α ≫ δ₀ =
          (Arrow.mk ((godementUnit X).app ℱ)).augmentedCechConerve.hom.app
            (SimplexCategory.mk 1) by
          simpa [α, δ₀] using godementResolutionAugmentationMap_comp_coface_zero X ℱ]
      rw [show α ≫ δ₁ =
          (Arrow.mk ((godementUnit X).app ℱ)).augmentedCechConerve.hom.app
            (SimplexCategory.mk 1) by
          simpa [α, δ₁] using godementResolutionAugmentationMap_comp_coface_one X ℱ]
      simpa using sub_self
        ((Arrow.mk ((godementUnit X).app ℱ)).augmentedCechConerve.hom.app
          (SimplexCategory.mk 1))

/-- Helper for Lemma 20.30.1: the augmentation from `single₀ ℱ` into the ordinary Godement
complex of `ℱ`. -/
private noncomputable abbrev godementResolutionAugmentationApp
    (X : RingedSpace.{u}) (ℱ : X.Modules) :
    (CochainComplex.single₀ X.Modules).obj ℱ ⟶ godementResolutionObj X ℱ :=
  (CochainComplex.fromSingle₀Equiv (godementResolutionObj X ℱ) ℱ).symm
    ⟨godementResolutionAugmentationMap X ℱ,
      godementResolutionAugmentationMap_comp_d_zero_one X ℱ⟩

/-- Helper for Lemma 20.30.1: the degree-zero component of the augmentation cochain map is the
Čech-conerve coaugmentation in simplicial degree `0`. -/
@[simp] private theorem godementResolutionAugmentationApp_f_zero
    (X : RingedSpace.{u}) (ℱ : X.Modules) :
    (godementResolutionAugmentationApp X ℱ).f 0 =
      godementResolutionAugmentationMap X ℱ := by
  -- Proof comment: `fromSingle₀Equiv` records a map out of `single₀` exactly by its degree-zero
  -- component together with the cocycle condition proved just above.
  simpa [godementResolutionAugmentationApp] using
    (CochainComplex.fromSingle₀Equiv_symm_apply_f_zero
      (C := godementResolutionObj X ℱ)
      (X := ℱ)
      (f := godementResolutionAugmentationMap X ℱ)
      (hf := godementResolutionAugmentationMap_comp_d_zero_one X ℱ))

/-- Helper for Lemma 20.30.1: any cochain map out of `single₀ ℱ` vanishes in positive degrees. -/
private theorem single₀_to_complex_f_succ
    (X : RingedSpace.{u}) {C : CochainComplex X.Modules ℕ} {ℱ : X.Modules}
    (ψ : (CochainComplex.single₀ X.Modules).obj ℱ ⟶ C) (n : ℕ) :
    ψ.f (n + 1) = 0 := by
  -- Proof comment: the source object in positive degree is zero, so every component there
  -- vanishes automatically.
  exact
    (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 ℱ (n + 1) (by simp)).eq_of_src
      _ _

/-- Helper for Lemma 20.30.1: the objectwise Godement augmentations satisfy the expected
naturality square. -/
private theorem godementResolutionAugmentation_naturality
    (X : RingedSpace.{u}) {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢) :
    (CochainComplex.single₀ X.Modules).map φ ≫ godementResolutionAugmentationApp X 𝒢 =
      godementResolutionAugmentationApp X ℱ ≫ (godementResolutionFunctor X).map φ := by
  -- Proof comment: maps out of `single₀ ℱ` are determined by degree `0`, where the square is just
  -- the Godement-unit naturality square.
  apply HomologicalComplex.from_single_hom_ext
  change (((CochainComplex.single₀ X.Modules).map φ ≫
      godementResolutionAugmentationApp X 𝒢).f 0) =
    ((godementResolutionAugmentationApp X ℱ ≫
      (godementResolutionFunctor X).map φ).f 0)
  simp only [HomologicalComplex.comp_f, godementResolutionAugmentationApp_f_zero,
    godementResolutionAugmentationMap, godementResolutionObj, godementResolutionFunctor,
    godementUnitArrowFunctor]
  simpa using
    (WidePushout.head_desc
      (arrows := fun _ : Fin 1 ↦ (godementUnit X).app ℱ)
      (f := φ ≫ WidePushout.head (fun _ : Fin 1 ↦ (godementUnit X).app 𝒢))
      (fs := fun x ↦
        (godementStep X).map φ ≫ WidePushout.ι (fun _ : Fin 1 ↦ (godementUnit X).app 𝒢) x)
      (w := fun x ↦ by
        fin_cases x
        calc
          (godementUnit X).app ℱ ≫
              ((godementStep X).map φ ≫
                WidePushout.ι (fun _ : Fin 1 ↦ (godementUnit X).app 𝒢) 0)
              =
            ((godementUnit X).app ℱ ≫ (godementStep X).map φ) ≫
              WidePushout.ι (fun _ : Fin 1 ↦ (godementUnit X).app 𝒢) 0 := by
                simp [Category.assoc]
          _ = (φ ≫ (godementUnit X).app 𝒢) ≫
              WidePushout.ι (fun _ : Fin 1 ↦ (godementUnit X).app 𝒢) 0 := by
                simpa [Category.assoc] using congrArg
                  (fun k ↦ k ≫ WidePushout.ι (fun _ : Fin 1 ↦ (godementUnit X).app 𝒢) 0)
                  ((godementUnit X).naturality φ).symm
          _ = φ ≫ WidePushout.head (fun _ : Fin 1 ↦ (godementUnit X).app 𝒢) := by
                simpa [Category.assoc] using
                  congrArg (fun k ↦ φ ≫ k)
                    (WidePushout.arrow_ι (fun _ : Fin 1 ↦ (godementUnit X).app 𝒢) 0))).symm

/-- Helper for Lemma 20.30.1: the objectwise Godement augmentations assemble into a natural
transformation from `single₀` to the ordinary Godement complex functor. -/
private noncomputable def godementResolutionAugmentation
    (X : RingedSpace.{u}) :
    CochainComplex.single₀ X.Modules ⟶ godementResolutionFunctor X where
  app ℱ := godementResolutionAugmentationApp X ℱ
  naturality := fun _ _ φ ↦ godementResolutionAugmentation_naturality X φ

/-- Helper for Lemma 20.30.1: the object notation `godementResolutionObj X ℱ` is definitionally
the value of the Godement resolution functor on `ℱ`. -/
@[simp] private theorem godementResolutionFunctor_obj
    (X : RingedSpace.{u}) (ℱ : X.Modules) :
    (godementResolutionFunctor X).obj ℱ = godementResolutionObj X ℱ := by
  -- Proof comment: this is just the abbreviation expansion used repeatedly in later rewrites.
  rfl

/-- Helper for Lemma 20.30.1: the degree-`i` short-complex model computes the ordinary homology
map of a cochain-map morphism. -/
private theorem shortComplexFunctor_homologyMap_eq
    {C : Type*} [Category C] [Preadditive C]
    {K L : CochainComplex C ℕ} (φ : K ⟶ L) (i : ℕ) [K.HasHomology i] [L.HasHomology i] :
    ShortComplex.homologyMap
        ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℕ) i).map φ) =
      HomologicalComplex.homologyMap φ i := by
  -- Proof comment: the short-complex model of degree-`i` homology is definitionally the usual
  -- cochain-complex homology map.
  rfl

/-- Helper for Lemma 20.30.1: forgetting module structure commutes definitionally with the
degree-`i` short-complex functor on cochain complexes. -/
private theorem moduleUnderlyingSheaf_shortComplexFunctor_map_eq
    (X : RingedSpace.{u}) {K L : CochainComplex X.Modules ℕ} (φ : K ⟶ L) (i : ℕ) :
    (((moduleUnderlyingSheaf X).mapShortComplex).map
        ((HomologicalComplex.shortComplexFunctor X.Modules (ComplexShape.up ℕ) i).map φ)) =
      ((HomologicalComplex.shortComplexFunctor
          (X.carrier.Sheaf AddCommGrpCat.{u}) (ComplexShape.up ℕ) i).map
        (((moduleUnderlyingSheaf X).mapHomologicalComplex (ComplexShape.up ℕ)).map φ)) := by
  -- Proof comment: both sides are literally the same short-complex morphism after unfolding the
  -- functorial definitions.
  rfl

/-- Helper for Lemma 20.30.1: applying `moduleUnderlyingSheaf X` conjugates the homology map of a
cochain map with the homology map of the forgotten cochain map via `mapHomologyIso`. -/
private theorem moduleUnderlyingSheaf_homologyMap_formula
    (X : RingedSpace.{u}) {K L : CochainComplex X.Modules ℕ} (φ : K ⟶ L) (i : ℕ) :
    (moduleUnderlyingSheaf X).map (HomologicalComplex.homologyMap φ i) =
      ((K.sc i).mapHomologyIso (moduleUnderlyingSheaf X)).inv ≫
        HomologicalComplex.homologyMap
          (((moduleUnderlyingSheaf X).mapHomologicalComplex (ComplexShape.up ℕ)).map φ) i ≫
        ((L.sc i).mapHomologyIso (moduleUnderlyingSheaf X)).hom := by
  -- Proof comment: this is exactly the `mapHomologyIso` naturality square after rewriting the
  -- short-complex morphism of `φ` into the ordinary homology map on cochain complexes.
  simpa [Category.assoc, shortComplexFunctor_homologyMap_eq,
    moduleUnderlyingSheaf_shortComplexFunctor_map_eq] using
    congrArg
      (fun k ↦ k ≫ ((L.sc i).mapHomologyIso (moduleUnderlyingSheaf X)).hom)
      (ShortComplex.mapHomologyIso_inv_naturality
        (F := moduleUnderlyingSheaf X)
        (φ := ((HomologicalComplex.shortComplexFunctor X.Modules
          (ComplexShape.up ℕ) i).map φ)))

/-- Helper for Lemma 20.30.1: the underlying additive-sheaf functor reflects quasi-isomorphisms of
cochain complexes of `𝒪_X`-modules. -/
private theorem moduleUnderlyingSheaf_reflectsQuasiIso
    (X : RingedSpace.{u}) {K L : CochainComplex X.Modules ℕ} (φ : K ⟶ L)
    (hφ :
      QuasiIso
        (((moduleUnderlyingSheaf X).mapHomologicalComplex (ComplexShape.up ℕ)).map φ)) :
    QuasiIso φ := by
  -- Proof comment: check the quasi-isomorphism degreewise after transporting homology through
  -- `moduleUnderlyingSheaf X`; then reflect the resulting homology isomorphism.
  rw [quasiIso_iff] at hφ ⊢
  intro i
  have hφi :
      IsIso
        (HomologicalComplex.homologyMap
          (((moduleUnderlyingSheaf X).mapHomologicalComplex (ComplexShape.up ℕ)).map φ) i) := by
    have hq : QuasiIsoAt
        (((moduleUnderlyingSheaf X).mapHomologicalComplex (ComplexShape.up ℕ)).map φ) i := hφ i
    rw [quasiIsoAt_iff_isIso_homologyMap] at hq
    exact hq
  rw [quasiIsoAt_iff_isIso_homologyMap]
  letI :
      IsIso
        (HomologicalComplex.homologyMap
          (((moduleUnderlyingSheaf X).mapHomologicalComplex (ComplexShape.up ℕ)).map φ) i) := hφi
  let eMid :
      (((moduleUnderlyingSheaf X).mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homology i ≅
        (((moduleUnderlyingSheaf X).mapHomologicalComplex (ComplexShape.up ℕ)).obj L).homology i :=
    asIso (HomologicalComplex.homologyMap
      (((moduleUnderlyingSheaf X).mapHomologicalComplex (ComplexShape.up ℕ)).map φ) i)
  letI :
      IsIso
        ((moduleUnderlyingSheaf X).map (HomologicalComplex.homologyMap φ i)) := by
    let e :
        (moduleUnderlyingSheaf X).obj (K.homology i) ≅
          (moduleUnderlyingSheaf X).obj (L.homology i) :=
      ((K.sc i).mapHomologyIso (moduleUnderlyingSheaf X)).symm ≪≫
        eMid ≪≫
        ((L.sc i).mapHomologyIso (moduleUnderlyingSheaf X))
    rw [moduleUnderlyingSheaf_homologyMap_formula (X := X) (φ := φ) (i := i)]
    have he :
        e.hom =
          ((K.sc i).mapHomologyIso (moduleUnderlyingSheaf X)).inv ≫
            HomologicalComplex.homologyMap
              (((moduleUnderlyingSheaf X).mapHomologicalComplex (ComplexShape.up ℕ)).map φ) i ≫
                ((L.sc i).mapHomologyIso (moduleUnderlyingSheaf X)).hom := by
      simp [e, eMid]
      rfl
    rw [← he]
    infer_instance
  exact isIso_of_reflects_iso (HomologicalComplex.homologyMap φ i) (moduleUnderlyingSheaf X)

/-- Helper for Lemma 20.30.1: the stalk map of `pointInclusion x` at the unique point of the
one-point space is the inverse of the canonical one-point stalk identification. -/
private theorem pointInclusion_stalkMap_eq_pointRingedSpaceStalkIso_inv
    (X : RingedSpace.{u}) (x : X)
    [hX : (U : TopologicalSpace.Opens ↑↑X.toPresheafedSpace) → Decidable (x ∈ U)]
    [hP : (U : TopologicalSpace.Opens (TopCat.of PUnit)) → Decidable (PUnit.unit ∈ U)] :
    ((pointInclusion x).hom.stalkMap PUnit.unit) = (pointRingedSpaceStalkIso (x := x)).inv := by
  have hfrom :
      StalkSkyscraperPresheafAdjunctionAuxs.fromStalk x
          (((stalkSkyscraperSheafAdjunction x).unit.app X.sheaf).hom) =
        𝟙 (X.presheaf.stalk x) := by
    -- Proof comment: the stalk/skyscraper unit specializes to the identity on the stalk ring.
    simpa [StalkSkyscraperPresheafAdjunctionAuxs.unit_app] using
      (StalkSkyscraperPresheafAdjunctionAuxs.fromStalk_to_skyscraper
        (p₀ := x) (f := 𝟙 (X.presheaf.stalk x)))
  -- Proof comment: compare both sides after postcomposing with the canonical stalk isomorphism.
  apply (cancel_mono (pointRingedSpaceStalkIso (x := x)).hom).1
  rw [pointInclusionStalkMap_comp_pointRingedSpaceStalkIso_hom (x := x), hfrom,
    ← Iso.inv_hom_id (pointRingedSpaceStalkIso (x := x))]
  rfl

/-- Helper for Lemma 20.30.1: a split monomorphism yields a cosimplicial homotopy equivalence on
its augmented Čech conerve coaugmentation. -/
private theorem cechConerveCoaugmentation_isHomotopyEquivalence_of_section
    {C : Type*} [Category C] {A B : C} (f : A ⟶ B)
    [∀ n : ℕ, HasWidePushout (Arrow.mk f).left
      (fun _ : Fin (n + 1) ↦ (Arrow.mk f).right) (fun _ ↦ (Arrow.mk f).hom)]
    (s : B ⟶ A) (hs : f ≫ s = 𝟙 A) :
    CategoryTheory.CosimplicialObject.IsHomotopyEquivalence
      (Arrow.mk f).augmentedCechConerve.hom := by
  refine ⟨{
    hom := (Arrow.mk f).augmentedCechConerve.hom
    inv := CategoryTheory.cechConerveRetraction f s hs
    homotopyHomInvId := ?_
    homotopyInvHomId := ?_
  }, rfl⟩
  · -- Proof comment: the coaugmentation followed by the retraction is strictly the identity.
    have hcoaug :
        (Arrow.mk f).augmentedCechConerve.hom ≫
            CategoryTheory.cechConerveRetraction f s hs =
          𝟙 ((CosimplicialObject.const C).obj A) := by
      simpa using CategoryTheory.cechConerveCoaugmentation_comp_retraction f s hs
    exact hcoaug ▸ CategoryTheory.CosimplicialObject.DeltaOneHomotopic.refl _
  · -- Proof comment: Chapter 14 packages the reverse composite as a `Δ[1]`-homotopy.
    exact CategoryTheory.cechConerveRetraction_comp_coaugmentation_deltaOneHomotopic_id f s hs

/-- Helper for Lemma 20.30.1: after applying the alternating coface map complex functor, the
Čech-conerve coaugmentation of a split monomorphism remains a homotopy equivalence. -/
private theorem alternatingCofaceMapComplex_map_isHomotopyEquivalence_of_section
    {C : Type*} [Category C] [Preadditive C] {A B : C} (f : A ⟶ B)
    [∀ n : ℕ, HasWidePushout (Arrow.mk f).left
      (fun _ : Fin (n + 1) ↦ (Arrow.mk f).right) (fun _ ↦ (Arrow.mk f).hom)]
    (s : B ⟶ A) (hs : f ≫ s = 𝟙 A) :
    HomologicalComplex.homotopyEquivalences C (ComplexShape.up ℕ)
      ((alternatingCofaceMapComplex C).map (Arrow.mk f).augmentedCechConerve.hom) := by
  -- Proof comment: transport the split-Čech homotopy equivalence through Lemma `14.28.7`.
  exact
    CategoryTheory.CosimplicialObject.alternatingCofaceMapComplex_map_isHomotopyEquivalence
      (cechConerveCoaugmentation_isHomotopyEquivalence_of_section f s hs)

/-- Helper for Lemma 20.30.1: the top-open component of the point-space counit is retracted by
the top-open component of the pulled-back point-space unit. -/
private theorem pointPullbackPushforwardCounit_topSection
    (X : RingedSpace.{u}) (ℱ : X.Modules) (x : X) :
    ∃ s :
        ((((pointInclusion x)^*) ⋙ ((pointInclusion x) _*) ⋙ ((pointInclusion x)^*)).obj ℱ).val.obj
          (Opposite.op (⊤ : TopologicalSpace.Opens (TopCat.of PUnit))) ⟶
          (((pointInclusion x)^*).obj ℱ).val.obj
            (Opposite.op (⊤ : TopologicalSpace.Opens (TopCat.of PUnit))),
      ((((pointInclusion x)^*).map
            ((godementUnit X).app ℱ ≫
              Pi.π (fun y : X ↦ (((pointInclusion y)^*) ⋙ ((pointInclusion y) _*)).obj ℱ) x)).val.app
          (Opposite.op (⊤ : TopologicalSpace.Opens (TopCat.of PUnit)))) ≫ s = 𝟙 _ := by
  let adj :=
    SheafOfModules.pullbackPushforwardAdjunction
      (RingedSpace.Hom.toRingCatSheafHom (pointInclusion x))
  let s :
      ((((pointInclusion x)^*) ⋙ ((pointInclusion x) _*) ⋙ ((pointInclusion x)^*)).obj ℱ).val.obj
        (Opposite.op (⊤ : TopologicalSpace.Opens (TopCat.of PUnit))) ⟶
        (((pointInclusion x)^*).obj ℱ).val.obj
          (Opposite.op (⊤ : TopologicalSpace.Opens (TopCat.of PUnit))) :=
    (adj.counit.app (((pointInclusion x)^*).obj ℱ)).val.app
      (Opposite.op (⊤ : TopologicalSpace.Opens (TopCat.of PUnit)))
  refine ⟨s, ?_⟩
  have htriangle :=
    congrArg
      (fun α ↦ α.val.app (Opposite.op (⊤ : TopologicalSpace.Opens (TopCat.of PUnit))))
      (adj.left_triangle_components ℱ)
  -- Proof comment: evaluate the adjunction left triangle on the unique nonempty open of the
  -- one-point space to obtain the required top-open retraction.
  rw [show
      (godementUnit X).app ℱ ≫
          Pi.π (fun y : X ↦ (((pointInclusion y)^*) ⋙ ((pointInclusion y) _*)).obj ℱ) x =
        (adj.unit.app ℱ) by
        simpa [adj, pointGodementAdjunction] using godementUnit_app_π X ℱ x]
  exact htriangle

/-- Helper for Lemma 20.30.1: at a fixed point `x`, the stalked Godement unit should admit a
section. This is the remaining transport-heavy bridge from the point-space adjunction to the
target stalk category. -/
private theorem stalkedGodementUnit_hasSection
    (X : RingedSpace.{u}) (ℱ : X.Modules) (x : X) :
    ∃ s : (stalkModuleFunctor x).obj ((godementStep X).obj ℱ) ⟶ (stalkModuleFunctor x).obj ℱ,
      (stalkModuleFunctor x).map ((godementUnit X).app ℱ) ≫ s = 𝟙 _ := by
  -- TODO: compose the stalk of the `x`-projection `godementUnit_app_π` with the point-space stalk
  -- identification for `pointInclusion x`, then use the pullback/pushforward counit at the unique
  -- point to build the required section entirely inside `stalkModuleFunctor x`.
  sorry

/-- Helper for Lemma 20.30.1: once the stalked Godement unit has a section, the split Čech
augmentation built from that stalked unit is a homotopy equivalence after applying
`alternatingCofaceMapComplex`. -/
private theorem stalkedSplitCechAugmentation_homotopyEquivalence
    (X : RingedSpace.{u}) (ℱ : X.Modules) (x : X) :
    HomologicalComplex.homotopyEquivalences
      (ModuleCat (X.presheaf.stalk x))
      (ComplexShape.up ℕ)
      ((alternatingCofaceMapComplex (ModuleCat (X.presheaf.stalk x))).map
        (Arrow.mk ((stalkModuleFunctor x).map ((godementUnit X).app ℱ))).augmentedCechConerve.hom) := by
  rcases stalkedGodementUnit_hasSection X ℱ x with ⟨s, hs⟩
  -- Proof comment: the section lemma puts us exactly in the split-Čech situation handled by the
  -- generic Chapter 14 homotopy-equivalence theorem.
  simpa using
    alternatingCofaceMapComplex_map_isHomotopyEquivalence_of_section
      ((stalkModuleFunctor x).map ((godementUnit X).app ℱ))
      s
      hs

/-- Helper for Lemma 20.30.1: after applying the stalk functor, the degree-zero component of the
`single₀` Godement augmentation is just the stalked degree-zero augmentation map. -/
private theorem stalkedGodementAugmentationApp_f_zero
    (X : RingedSpace.{u}) (ℱ : X.Modules) (x : X) :
    ((((stalkModuleFunctor x).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (godementResolutionAugmentationApp X ℱ)).f 0) =
      (stalkModuleFunctor x).map (godementResolutionAugmentationMap X ℱ) := by
  -- Proof comment: `mapHomologicalComplex` computes components degreewise, so after specializing
  -- the `single₀` augmentation at degree `0` we are simply applying the stalk functor to the
  -- underlying degree-zero augmentation map.
  simp [Functor.mapHomologicalComplex_map_f]

/-- Helper for Lemma 20.30.1: the first differential of the alternating coface-map complex of a
constant cosimplicial object vanishes. -/
private theorem constantAlternating_d_zero_one_eq_zero
    {R : CommRingCat.{u}} (M : ModuleCat R) :
    ((alternatingCofaceMapComplex (ModuleCat R)).obj
        ((CosimplicialObject.const (ModuleCat R)).obj M)).d 0 1 = 0 := by
  -- Proof comment: in degree `0`, the alternating sum is `𝟙 - 𝟙`.
  rw [show
      ((alternatingCofaceMapComplex (ModuleCat R)).obj
          ((CosimplicialObject.const (ModuleCat R)).obj M)).d 0 1 =
        AlgebraicTopology.AlternatingCofaceMapComplex.objD
          ((CosimplicialObject.const (ModuleCat R)).obj M) 0 by
        rfl]
  rw [AlgebraicTopology.AlternatingCofaceMapComplex.objD, Fin.sum_univ_two]
  change (1 : ℤ) • (𝟙 M) + (-1 : ℤ) • (𝟙 M) = 0
  simp

/-- Helper for Lemma 20.30.1: the canonical map from `single₀ M` into the alternating coface-map
complex of the constant cosimplicial object on `M` is determined by the identity in degree `0`. -/
private noncomputable abbrev single₀ToConstantAlternatingApp
    {R : CommRingCat.{u}} (M : ModuleCat R) :
    (CochainComplex.single₀ (ModuleCat R)).obj M ⟶
      (alternatingCofaceMapComplex (ModuleCat R)).obj
        ((CosimplicialObject.const (ModuleCat R)).obj M) :=
  (CochainComplex.fromSingle₀Equiv
      ((alternatingCofaceMapComplex (ModuleCat R)).obj
        ((CosimplicialObject.const (ModuleCat R)).obj M))
      M).symm
    ⟨𝟙 M, by
      -- Proof comment: in simplicial degree `0`, the constant cosimplicial differential is
      -- `𝟙 - 𝟙`, so the identity morphism satisfies the required cocycle condition.
      rw [constantAlternating_d_zero_one_eq_zero]
      exact Category.id_comp
        (0 :
          M ⟶
            ((alternatingCofaceMapComplex (ModuleCat R)).obj
              ((CosimplicialObject.const (ModuleCat R)).obj M)).X 1)⟩

/-- Helper for Lemma 20.30.1: the degree-zero component of the canonical
`single₀ → alternating(const)` bridge is the identity on `M`. -/
@[simp] private theorem single₀ToConstantAlternatingApp_f_zero
    {R : CommRingCat.{u}} (M : ModuleCat R) :
    (single₀ToConstantAlternatingApp M).f 0 = 𝟙 M := by
  -- Proof comment: this is exactly the defining degree-zero component recorded by
  -- `fromSingle₀Equiv`.
  simpa [single₀ToConstantAlternatingApp] using
    (CochainComplex.fromSingle₀Equiv_symm_apply_f_zero
      (C := (alternatingCofaceMapComplex (ModuleCat R)).obj
        ((CosimplicialObject.const (ModuleCat R)).obj M))
      (X := M)
      (f := 𝟙 M)
      (hf := by
        rw [constantAlternating_d_zero_one_eq_zero]
        exact Category.id_comp
          (0 :
            M ⟶
              ((alternatingCofaceMapComplex (ModuleCat R)).obj
                ((CosimplicialObject.const (ModuleCat R)).obj M)).X 1)))

/-- Helper for Lemma 20.30.1: the split Čech augmentation of the identity map is a homotopy
equivalence after applying `alternatingCofaceMapComplex`. -/
private theorem identitySplitCechAugmentation_homotopyEquivalence
    {R : CommRingCat.{u}} (M : ModuleCat R) :
    HomologicalComplex.homotopyEquivalences (ModuleCat R) (ComplexShape.up ℕ)
      ((alternatingCofaceMapComplex (ModuleCat R)).map
        ((Arrow.mk (𝟙 M)).augmentedCechConerve.hom)) := by
  -- Proof comment: apply the generic split-Čech homotopy-equivalence theorem with the section
  -- `𝟙 M`.
  simpa using
    alternatingCofaceMapComplex_map_isHomotopyEquivalence_of_section
      (𝟙 M) (𝟙 M) (by simp)

/-- Helper for Lemma 20.30.1: the stalked Godement augmentation should be identified with the
split Čech augmentation of the stalked Godement unit. -/
private theorem stalkedGodementAugmentation_homotopyEquivalence
    (X : RingedSpace.{u}) (ℱ : X.Modules) (x : X) :
    HomologicalComplex.homotopyEquivalences
      (ModuleCat (X.presheaf.stalk x))
      (ComplexShape.up ℕ)
      (((stalkModuleFunctor x).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (godementResolutionAugmentationApp X ℱ)) := by
  -- Route correction: the direct whole-map comparison was the wrong normal form. The split Čech
  -- owner produced by `augmentedCechConerve.hom` lives on the alternating complex of the constant
  -- cosimplicial source, while the theorem here starts from the `single₀` augmentation
  -- `godementResolutionAugmentationApp`.
  -- TODO: the current source-side bridge `single₀ToConstantAlternatingApp` lands in the
  -- alternating complex of the constant cosimplicial object, while the split Čech owner theorem
  -- is phrased for a map between alternating complexes. The next step is a bridge from
  -- `single₀ToConstantAlternatingApp` to the correct augmented-constant owner, together with a
  -- degree-zero identification of the actual stalked augmentation against that normalized source.
  sorry

/-- Lemma 20.30.1: there is a functorial Godement resolution of `𝒪_X`-modules. Concretely, one
gets a functor `G` from `X.Modules` to `ℕ`-indexed cochain complexes, an augmentation
`η : CochainComplex.single₀ X.Modules ⟶ G`, and the standard source-facing properties:
`η.app ℱ` is a quasi-isomorphism for every `ℱ`, every term `(G.obj ℱ).X n` is flasque, and after
applying the stalk functor at any point `x`, the augmented complex becomes a homotopy
equivalence. The reusable bridge data in this file are the pointwise Godement step `godementStep X`
and its unit `godementUnit X`; the theorem itself keeps the source-facing existence claim as the
exported public surface. -/
@[stacks 0FKS]
theorem exists_functorial_godement_resolution (X : RingedSpace.{u}) :
    ∃ (G : X.Modules ⥤ CochainComplex X.Modules ℕ)
      (η : CochainComplex.single₀ X.Modules ⟶ G),
      (∀ ℱ : X.Modules, QuasiIso (η.app ℱ)) ∧
      (∀ (n : ℕ) (ℱ : X.Modules),
        TopCat.Sheaf.IsFlasque ((moduleUnderlyingSheaf X).obj ((G.obj ℱ).X n))) ∧
      ∀ (ℱ : X.Modules) (x : X),
        HomologicalComplex.homotopyEquivalences
          (ModuleCat (X.presheaf.stalk x))
          (ComplexShape.up ℕ)
          (((stalkModuleFunctor x).mapHomologicalComplex (ComplexShape.up ℕ)).map (η.app ℱ)) := by
  -- Route correction: the current file no longer forces the Chapter 14.33 comonad-style route.
  -- The verified prefix here is the actual Godement Čech complex and its degree-zero augmentation;
  -- the remaining work is to assemble these objectwise constructions into a natural augmentation,
  -- prove flasqueness of the iterated terms, and transport the point-pullback homotopy
  -- equivalence to the stated stalkwise complex.
  let G := godementResolutionFunctor X
  let η := godementResolutionAugmentation X
  refine ⟨G, η, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro ℱ
    -- TODO: prove the underlying additive-sheaf augmentation is a quasi-isomorphism by reducing to
    -- the discrete-space Godement resolution and then reflect it back through
    -- `moduleUnderlyingSheaf_reflectsQuasiIso`.
    have hUnderlying :
        QuasiIso
          (((moduleUnderlyingSheaf X).mapHomologicalComplex (ComplexShape.up ℕ)).map (η.app ℱ)) :=
      sorry
    exact moduleUnderlyingSheaf_reflectsQuasiIso X (η.app ℱ) hUnderlying
  · intro n ℱ
    -- TODO: identify degree `n` with the `(n + 1)`-fold Godement step, prove one-step flasqueness
    -- on the underlying additive sheaf, and transport that property across the degreewise
    -- identification.
    sorry
  · intro ℱ x
    -- Proof comment: the stalkwise branch is now reduced to the single section lemma above.
    exact stalkedGodementAugmentation_homotopyEquivalence X ℱ x

end AlgebraicGeometry.RingedSpace
