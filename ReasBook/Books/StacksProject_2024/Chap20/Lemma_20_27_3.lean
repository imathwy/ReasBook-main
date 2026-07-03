import Mathlib
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import StacksProject_2024.Chap13.Remark_13_10_9
import StacksProject_2024.Chap20.Definition_20_26_14

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape
open AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

/- The structure sheaf of a ringed space is viewed below as a sheaf of not-necessarily-commutative
rings, and the induced module category is `RingedSpace.Modules X`. -/
/-- The structure-sheaf morphism `\mathcal O_Y \to f_*\mathcal O_X` attached to a morphism of
ringed spaces. -/
noncomputable abbrev commRingSheafPushforwardMap {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    Y.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).obj X.sheaf :=
  ⟨f.hom.c⟩

/-- The structure-sheaf morphism of a ringed-space morphism after forgetting commutativity. -/
noncomputable abbrev pushforwardStructureSheafHom {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    (RingedSpace.ringCatSheaf Y) ⟶
      (TopCat.Sheaf.pushforward RingCat.{u} f.hom.base).obj (RingedSpace.ringCatSheaf X) :=
  (sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat RingCat.{u})).map
    (commRingSheafPushforwardMap f)

/-- The pullback functor on module sheaves induced by a morphism of ringed spaces. -/
noncomputable abbrev modulePullback {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    (RingedSpace.Modules Y) ⥤ (RingedSpace.Modules X) :=
  SheafOfModules.pullback (pushforwardStructureSheafHom f)

/-- The quasi-isomorphisms in the homotopy category of cochain complexes of `\mathcal O_X`-modules.
-/
abbrev ModuleQis (X : RingedSpace.{u}) :=
  HomotopyCategory.quasiIso (RingedSpace.Modules X) (up ℤ)

/-- The unbounded derived category `D(\mathcal O_X)` of `\mathcal O_X`-module sheaves. -/
abbrev ModuleDerived (X : RingedSpace.{u}) :=
  DerivedCategory (RingedSpace.Modules X)

/-- The functor on homotopy categories induced by module pullback. -/
abbrev modulePullbackToDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(modulePullback f).Additive] :
    HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ DerivedCategory (RingedSpace.Modules X) :=
  (modulePullback f).mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh

-- Proof sketch: choose K-flat resolutions on `Y`, use the preservation of K-flatness by pullback,
-- and apply the universal property of total left derived functors.
/-- Pullback on homotopy categories admits a total left derived functor. -/
theorem modulePullbackToDerived_hasLeftDerivedFunctor
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    [(modulePullback f).Additive] :
    Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y) := sorry

/-- The canonical left-derived-functor instance for module pullback. -/
instance instHasLeftDerivedFunctorModulePullbackToDerived
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    [(modulePullback f).Additive] :
    Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y) :=
  modulePullbackToDerived_hasLeftDerivedFunctor f

/-- The derived pullback functor `Lf^* : D(\mathcal O_Y) \to D(\mathcal O_X)`. -/
abbrev modulePullbackDerived
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    [(modulePullback f).Additive] :
    DerivedCategory (RingedSpace.Modules Y) ⥤ DerivedCategory (RingedSpace.Modules X) :=
  Functor.totalLeftDerived (modulePullbackToDerived f)
    (DerivedCategory.Qh : HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ DerivedCategory (RingedSpace.Modules Y))
    (ModuleQis Y)

variable {X Y : RingedSpace.{u}}

variable [CategoryWithHomology (RingedSpace.Modules X)]
variable [HasCountableCoproducts (RingedSpace.Modules X)]
variable [MonoidalCategory (RingedSpace.Modules X)]
variable [MonoidalPreadditive (RingedSpace.Modules X)]
variable [HasColimits (RingedSpace.Modules X)]
variable [(curriedTensor ((RingedSpace.Modules X))).Additive]
variable [∀ ℱ : (RingedSpace.Modules X), ((curriedTensor ((RingedSpace.Modules X))).obj ℱ).Additive]
variable [∀ (ℱ 𝒢 : CochainComplex (RingedSpace.Modules X) ℤ),
  CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor ((RingedSpace.Modules X)))]

/-- The category of `\mathcal O_X`-modules is preadditive. -/
local instance instPreadditiveSheafModules : Preadditive (RingedSpace.Modules X) :=
  (inferInstance : Abelian (RingedSpace.Modules X)).toPreadditive

/-- The category of `\mathcal O_X`-modules has binary biproducts. -/
local instance instHasBinaryBiproductsSheafModules :
    HasBinaryBiproducts (RingedSpace.Modules X) :=
  Abelian.hasBinaryBiproducts

variable [CategoryWithHomology (RingedSpace.Modules Y)]
variable [HasCountableCoproducts (RingedSpace.Modules Y)]
variable [MonoidalCategory (RingedSpace.Modules Y)]
variable [MonoidalPreadditive (RingedSpace.Modules Y)]
variable [HasColimits (RingedSpace.Modules Y)]
variable [(curriedTensor ((RingedSpace.Modules Y))).Additive]
variable [∀ ℱ : (RingedSpace.Modules Y), ((curriedTensor ((RingedSpace.Modules Y))).obj ℱ).Additive]
variable [∀ (ℱ 𝒢 : CochainComplex (RingedSpace.Modules Y) ℤ),
  CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor ((RingedSpace.Modules Y)))]

/-- A chosen homotopy-category representative of a derived `\mathcal O_X`-module. -/
private noncomputable abbrev derivedTensorRepresentative
    (ℱ : DerivedCategory (RingedSpace.Modules X)) :
    HomotopyCategory (RingedSpace.Modules X) (up ℤ) :=
  DerivedCategory.Qh.objPreimage ℱ

/-- The cochain complex underlying the chosen representative of a derived `\mathcal O_X`-module.
-/
private noncomputable abbrev derivedTensorRepresentativeComplex
    (ℱ : DerivedCategory (RingedSpace.Modules X)) :
    CochainComplex (RingedSpace.Modules X) ℤ :=
  (derivedTensorRepresentative ℱ).as

/-- Tensor-totalization on the homotopy category with a fixed right complex. -/
private noncomputable abbrev tensorLeftHomotopyFunctorOfComplex
    (K : CochainComplex (RingedSpace.Modules X) ℤ) :
    HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤
      HomotopyCategory (RingedSpace.Modules X) (up ℤ) :=
  CategoryTheory.Quotient.lift (homotopic (RingedSpace.Modules X) (up ℤ))
    ((((curriedTensor (RingedSpace.Modules X)).map₂CochainComplex).flip.obj K) ⋙
      HomotopyCategory.quotient (RingedSpace.Modules X) (up ℤ))
    (fun _ _ _ _ ⟨h⟩ ↦
      HomotopyCategory.eq_of_homotopy _ _
        (HomologicalComplex.mapBifunctorMapHomotopy₁ h (𝟙 K)
          (curriedTensor (RingedSpace.Modules X)) (up ℤ)))

/-- The homotopy-category tensor functor whose left derived functor defines derived tensoring with
a fixed right factor. -/
private noncomputable abbrev derivedTensorSourceFunctor
    (ℱ : DerivedCategory (RingedSpace.Modules X)) :
    HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤ DerivedCategory (RingedSpace.Modules X) :=
  tensorLeftHomotopyFunctorOfComplex (derivedTensorRepresentativeComplex ℱ) ⋙
    DerivedCategory.Qh

-- Proof sketch: replace the chosen representative of the fixed right factor by a K-flat one and
-- use invariance of tensoring with a K-flat complex under quasi-isomorphism.
/-- Tensoring on the homotopy category with a fixed right factor admits a total left derived
functor. -/
private theorem derivedTensorSourceFunctor_hasLeftDerivedFunctor
    (ℱ : DerivedCategory (RingedSpace.Modules X)) :
    (derivedTensorSourceFunctor ℱ).HasLeftDerivedFunctor (ModuleQis X) := sorry

local notation "DModX" => DerivedCategory (RingedSpace.Modules X)
local notation "DModY" => DerivedCategory (RingedSpace.Modules Y)

private noncomputable abbrev derivedTensorProductX
    (ℱ : DModX) :
    DModX ⥤ DModX :=
  AlgebraicGeometry.RingedSpace.derivedTensorProduct ℱ

private noncomputable abbrev derivedTensorProductY
    (ℱ : DModY) :
    DModY ⥤ DModY :=
  AlgebraicGeometry.RingedSpace.derivedTensorProduct ℱ

/-- The canonical counit exhibiting derived tensoring with a fixed right factor as a left derived
functor. -/
private abbrev derivedTensorProductCounit
    (ℱ : DerivedCategory (RingedSpace.Modules X)) :
    (DerivedCategory.Qh :
        HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤ DerivedCategory (RingedSpace.Modules X)) ⋙
      derivedTensorProductX ℱ ⟶
        derivedTensorSourceFunctor ℱ :=
  letI := derivedTensorSourceFunctor_hasLeftDerivedFunctor ℱ
  (derivedTensorSourceFunctor ℱ).totalLeftDerivedCounit
    DerivedCategory.Qh
    (ModuleQis X)

-- Proof sketch: this is the defining `IsLeftDerivedFunctor` instance for the total left derived
-- functor attached to `derivedTensorSourceFunctor ℱ`.
/-- Derived tensoring with a fixed right factor is the left derived functor of the corresponding
homotopy-category tensor functor. -/
private theorem derivedTensorProduct_isLeftDerivedFunctor
    (ℱ : DerivedCategory (RingedSpace.Modules X)) :
    (derivedTensorProductX ℱ).IsLeftDerivedFunctor
      (derivedTensorProductCounit ℱ)
      (ModuleQis X) := by
  sorry

/-- The counit exhibiting
`(- \otimes_{\mathcal O_Y}^{\mathbf L} \mathcal G^\bullet) \circ Lf^*`
as a left derived functor after postcomposing with `Lf^*`. -/
private abbrev derivedTensorThenPullbackCounit
    (f : X ⟶ Y) [(modulePullback f).Additive] (𝒢 : DModY) :
    (DerivedCategory.Qh :
        HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ DerivedCategory (RingedSpace.Modules Y)) ⋙
      (derivedTensorProductY 𝒢 ⋙ modulePullbackDerived f) ⟶
        derivedTensorSourceFunctor 𝒢 ⋙ modulePullbackDerived f :=
  (Functor.associator
      (DerivedCategory.Qh :
        HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ DerivedCategory (RingedSpace.Modules Y))
      (derivedTensorProductY 𝒢)
      (modulePullbackDerived f)).hom ≫
    Functor.whiskerRight
      (derivedTensorProductCounit 𝒢)
      (modulePullbackDerived f)

-- Proof sketch: postcompose the left derived functor `derivedTensorProduct 𝒢` with `Lf^*`; the
-- universal property of left derived functors is preserved under this fixed postcomposition.
/-- Postcomposing derived tensoring with derived pullback again yields a left derived functor. -/
private theorem derivedTensorThenPullback_isLeftDerivedFunctor
    (f : X ⟶ Y) [(modulePullback f).Additive] (𝒢 : DModY) :
    (derivedTensorProductY 𝒢 ⋙ modulePullbackDerived f).IsLeftDerivedFunctor
      (derivedTensorThenPullbackCounit f 𝒢)
      (ModuleQis Y) := by
  sorry

/-- The counit exhibiting
`Lf^* \circ (- \otimes_{\mathcal O_X}^{\mathbf L} Lf^*\mathcal G^\bullet)` as a left derived
functor of the underived pullback-to-derived functor followed by derived tensoring on `X`. -/
private abbrev pullbackThenDerivedTensorCounit
    (f : X ⟶ Y) [(modulePullback f).Additive] (𝒢 : DModY) :
    (DerivedCategory.Qh :
        HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ DerivedCategory (RingedSpace.Modules Y)) ⋙
      (modulePullbackDerived f ⋙ derivedTensorProductX ((modulePullbackDerived f).obj 𝒢)) ⟶
        modulePullbackToDerived f ⋙
          derivedTensorProductX ((modulePullbackDerived f).obj 𝒢) :=
  (Functor.associator
      (DerivedCategory.Qh :
        HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ DerivedCategory (RingedSpace.Modules Y))
      (modulePullbackDerived f)
      (derivedTensorProductX ((modulePullbackDerived f).obj 𝒢))).hom ≫
    Functor.whiskerRight
      ((modulePullbackToDerived f).totalLeftDerivedCounit
        (DerivedCategory.Qh :
          HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ DerivedCategory (RingedSpace.Modules Y))
        (ModuleQis Y))
      (derivedTensorProductX ((modulePullbackDerived f).obj 𝒢))

-- Proof sketch: derive `modulePullbackToDerived f` first and then postcompose with the fixed
-- derived tensor functor on `X`.
/-- Pullback followed by derived tensoring with the pulled-back right factor is a left derived
functor of the underived pullback-to-derived functor followed by tensoring on `X`. -/
private theorem pullbackThenDerivedTensor_isLeftDerivedFunctor
    (f : X ⟶ Y) [(modulePullback f).Additive] (𝒢 : DModY) :
    ((modulePullbackDerived f ⋙ derivedTensorProductX ((modulePullbackDerived f).obj 𝒢))
      ).IsLeftDerivedFunctor
        (pullbackThenDerivedTensorCounit f 𝒢)
        (ModuleQis Y) := by
  sorry

-- Proof sketch: on K-flat representatives this is the underived pullback-tensor comparison from
-- Lemma `17.16.4`, descended through the homotopy category and then localized to
-- `D(\mathcal O_X)`.
/-- The underived comparison natural transformation whose left derived transform is the pullback
comparison of Lemma `20.27.3`. -/
private theorem modulePullbackDerivedTensorUnderivedComparison_nonempty
    (f : X ⟶ Y) [(modulePullback f).Additive] (𝒢 : DModY) :
    Nonempty
      (derivedTensorSourceFunctor 𝒢 ⋙ modulePullbackDerived f ⟶
        modulePullbackToDerived f ⋙
          derivedTensorProductX ((modulePullbackDerived f).obj 𝒢)) := by
  sorry

/-- The canonical pullback-tensor comparison morphism. -/
noncomputable def modulePullbackDerivedTensorComparison
    (f : X ⟶ Y) [(modulePullback f).Additive] (𝒢 : DModY) :
    derivedTensorProductY 𝒢 ⋙ modulePullbackDerived f ⟶
      modulePullbackDerived f ⋙ derivedTensorProductX ((modulePullbackDerived f).obj 𝒢) :=
  let τ :
      derivedTensorSourceFunctor 𝒢 ⋙ modulePullbackDerived f ⟶
        modulePullbackToDerived f ⋙
          derivedTensorProductX ((modulePullbackDerived f).obj 𝒢) :=
    Classical.choice (modulePullbackDerivedTensorUnderivedComparison_nonempty f 𝒢)
  let _ :
      (derivedTensorProductY 𝒢 ⋙ modulePullbackDerived f)
        .IsLeftDerivedFunctor
        (derivedTensorThenPullbackCounit f 𝒢)
        (ModuleQis Y) :=
    derivedTensorThenPullback_isLeftDerivedFunctor f 𝒢
  let _ :
      ((modulePullbackDerived f ⋙ derivedTensorProductX ((modulePullbackDerived f).obj 𝒢))
        ).IsLeftDerivedFunctor
          (pullbackThenDerivedTensorCounit f 𝒢)
          (ModuleQis Y) :=
    pullbackThenDerivedTensor_isLeftDerivedFunctor f 𝒢
  Functor.leftDerivedNatTrans
    (derivedTensorProductY 𝒢 ⋙ modulePullbackDerived f)
    (modulePullbackDerived f ⋙ derivedTensorProductX ((modulePullbackDerived f).obj 𝒢))
    (derivedTensorThenPullbackCounit f 𝒢)
    (pullbackThenDerivedTensorCounit f 𝒢)
    (ModuleQis Y)
    τ

-- Proof sketch: represent the fixed right factor and the varying left factor by K-flat complexes.
-- By Lemma `20.26.5`, their total tensor product is again K-flat, so `Lf^*` can be computed by
-- ordinary pullback on that total tensor complex. The termwise pullback-tensor comparison from
-- Lemma `17.16.4` then identifies the pulled-back tensor totalization with the tensor totalization
-- of the pulled-back representatives, and passing to the derived category yields the comparison
-- natural isomorphism.
/-- The canonical pullback-tensor comparison morphism is an isomorphism. -/
theorem modulePullbackDerivedTensorComparison_isIso
    (f : X ⟶ Y) [(modulePullback f).Additive] (𝒢 : DModY) :
    IsIso (modulePullbackDerivedTensorComparison f 𝒢) := by
  sorry

/-- Lemma 20.27.3: for a morphism of ringed spaces `f : (X, \mathcal O_X) \to
(Y, \mathcal O_Y)` and a fixed object `\mathcal G^\bullet` of `D(\mathcal O_Y)`, the derived
pullback functor carries `- \otimes_{\mathcal O_Y}^{\mathbf L} \mathcal G^\bullet` to the
derived tensor product with the pulled-back right factor `Lf^* \mathcal G^\bullet`. Evaluating
this natural isomorphism at `\mathcal F^\bullet` gives the canonical comparison
`Lf^*(\mathcal F^\bullet \otimes_{\mathcal O_Y}^{\mathbf L} \mathcal G^\bullet) \cong
Lf^*\mathcal F^\bullet \otimes_{\mathcal O_X}^{\mathbf L} Lf^*\mathcal G^\bullet`. -/
noncomputable abbrev modulePullbackDerived_derivedTensorProduct_iso
    (f : X ⟶ Y) [(modulePullback f).Additive] (𝒢 : DModY) :
    derivedTensorProductY 𝒢 ⋙ modulePullbackDerived f ≅
      modulePullbackDerived f ⋙ derivedTensorProductX ((modulePullbackDerived f).obj 𝒢) :=
  letI := modulePullbackDerivedTensorComparison_isIso f 𝒢
  asIso (modulePullbackDerivedTensorComparison f 𝒢)

end AlgebraicGeometry.RingedSpace
