import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.Tactic.Recall
import stacks_proof.stacks_project.Chap12.Remark_12_29_2
import stacks_proof.stacks_project.Chap13.Lemma_13_30_2
import stacks_proof.stacks_project.Chap15.«15_60_1_1»

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open ComplexShape

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

local notation "CpxR" => CochainComplex (ModuleCat R) ℤ
local notation "CpxA" => CochainComplex (ModuleCat A) ℤ
local notation "KModR" => HomotopyCategory (ModuleCat R) (up ℤ)
local notation "KModA" => HomotopyCategory (ModuleCat A) (up ℤ)
local notation "DModR" => DerivedCategory (ModuleCat R)
local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "QR" => (DerivedCategory.Q : CpxR ⥤ DModR)
local notation "QA" => (DerivedCategory.Q : CpxA ⥤ DModA)
local notation "QhR" => (DerivedCategory.Qh : KModR ⥤ DModR)
local notation "QhA" => (DerivedCategory.Qh : KModA ⥤ DModA)
local notation "HR" => DerivedCategory.homologyFunctor (ModuleCat R)
local notation "HA" => DerivedCategory.homologyFunctor (ModuleCat A)
local notation "σ" => (algebraMap R A)

/- Domain-style sampling for Lemma 15.60.3:
- primary domain: derived change of rings for module categories and the adjunction between derived
  scalar extension and derived restriction of scalars;
- sampled owner declarations:
  `derivedTensorWithAlgebra`,
  `(ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory`,
  `Adjunction.mapHomologicalComplex`,
  `Adjunction.derived`,
  `Adjunction.homEquiv_unit`;
- best owner abstraction: the source-facing item is the derived adjunction itself, with
  `derivedTensorWithAlgebra σ` as left adjoint and the exact owner
  `(ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory` as right adjoint;
- primitive data: the underived module-category adjunction
  `ModuleCat.extendRestrictScalarsAdj (algebraMap R A)`, its canonical cochain-complex lift
  `(ModuleCat.extendRestrictScalarsAdj (algebraMap R A)).mapHomologicalComplex (up ℤ)`, and the
  left/right derived comparison morphisms required by `Adjunction.derived`;
- derived API: the generic adjunction consequences such as `Adjunction.homEquiv_unit` and
  `Adjunction.isLeftAdjoint`, which should be used directly rather than reintroduced as parallel
  local wrappers.

Source/core/bridge triage:
- `source-facing`: the adjunction
  `derivedTensorWithAlgebra σ ⊣ (ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory`;
- `core/canonical`: `Adjunction.derived` and exact `mapDerivedCategory`;
- `bridge/view`: `Adjunction.mapHomologicalComplex` together with the derived comparison natural
  transformations used to instantiate `Adjunction.derived`. -/

/-- Extension of scalars along `R → A` is additive for the homotopy-category model of derived
change of rings. -/
local instance extendScalars_additive_forDerivedAdjunction :
    (ModuleCat.extendScalars.{u, u, u} (algebraMap R A)).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap R A)).left_adjoint_additive

private abbrev extendScalarsComplex : CpxR ⥤ CpxA :=
  (ModuleCat.extendScalars.{u, u, u} (algebraMap R A)).mapHomologicalComplex (up ℤ)

private abbrev extendScalarsHomotopy : KModR ⥤ KModA :=
  (ModuleCat.extendScalars.{u, u, u} (algebraMap R A)).mapHomotopyCategory (up ℤ)

/-- The derived-category restriction-of-scalars functor along `R → A`. -/
private abbrev restrictScalarsDerived : DModA ⥤ DModR :=
  (ModuleCat.restrictScalars.{u} (algebraMap R A)).mapDerivedCategory

/-- The homotopy-category scalar-extension functor to the derived category admits a total left
derived functor. -/
local instance extendScalarsHomotopyToDerived_hasLeftDerivedFunctor :
    (extendScalarsHomotopy ⋙ QhA).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (ModuleCat R) (up ℤ)) :=
  extendScalarsToDerived_hasLeftDerivedFunctor σ

/-- The comparison morphism exhibiting `- ⊗_R^{\mathbf L} A` as a left derived functor of
cochain-level extension of scalars. -/
private abbrev derivedTensorWithAlgebraComplexCounit :
    QR ⋙ derivedTensorWithAlgebra (algebraMap R A) ⟶ extendScalarsComplex ⋙ QA :=
  Functor.whiskerRight
      (DerivedCategory.quotientCompQhIso (ModuleCat R)).hom
      (derivedTensorWithAlgebra (algebraMap R A)) ≫
    Functor.whiskerLeft (HomotopyCategory.quotient (ModuleCat R) (up ℤ))
      ((extendScalarsHomotopy ⋙ QhA).totalLeftDerivedCounit
        QhR
        (HomotopyCategory.quasiIso (ModuleCat R) (up ℤ))) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (Functor.mapHomotopyCategoryFactors (ModuleCat.extendScalars (algebraMap R A)) (up ℤ)).hom
      QhA ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft extendScalarsComplex
      (DerivedCategory.quotientCompQhIso (ModuleCat A)).inv

-- Proof sketch: rewrite the cochain-level scalar-extension functor through the homotopy-category
-- quotient, then compare with the defining total left derived functor from Lemma `15.60.1`.
/-- The derived tensor functor with `A` is the left derived functor of cochain-level scalar
extension along `R → A`. -/
private theorem derivedTensorWithAlgebra_isLeftDerivedFunctor :
    Functor.IsLeftDerivedFunctor
      (derivedTensorWithAlgebra (algebraMap R A))
      derivedTensorWithAlgebraComplexCounit
      (HomologicalComplex.quasiIso (ModuleCat R) (up ℤ)) := by
  -- TODO: transport the `Qh`-level total-left-derived counit from `15.60.1.1` across
  -- `DerivedCategory.quotientCompQhIso` and `Functor.mapHomotopyCategoryFactors`, then apply
  -- `Functor.isLeftDerivedFunctor_iff_of_iso`.
  sorry

attribute [local instance] derivedTensorWithAlgebra_isLeftDerivedFunctor

-- Proof sketch: restriction of scalars is exact, so the induced functor on derived categories is
-- its total right derived functor, with comparison map given by
-- `mapDerivedCategoryFactors.inv`.
/-- Restriction of scalars on derived categories is the right derived functor of cochain-level
restriction of scalars. -/
private theorem restrictScalarsDerived_isRightDerivedFunctor :
    Functor.IsRightDerivedFunctor
      restrictScalarsDerived
      ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategoryFactors.inv)
      (HomologicalComplex.quasiIso (ModuleCat A) (up ℤ)) := by
  let F : ModuleCat.{u} A ⥤ ModuleCat.{u} R :=
    ModuleCat.restrictScalars.{u} (algebraMap R A)
  letI : Limits.PreservesFiniteLimits F := ((exactFunctor_iff F).1 (restrictScalars_exact σ)).1
  letI : Limits.PreservesFiniteColimits F := ((exactFunctor_iff F).1 (restrictScalars_exact σ)).2
  -- Exact restriction already inverts quasi-isomorphisms, so its derived lift is canonical.
  simpa [restrictScalarsDerived, F] using
    (Functor.isRightDerivedFunctor_of_inverts
      (HomologicalComplex.quasiIso (ModuleCat A) (up ℤ))
      F.mapDerivedCategory
      F.mapDerivedCategoryFactors)

attribute [local instance] restrictScalarsDerived_isRightDerivedFunctor

-- Proof sketch: once the left and right derived functor structures are fixed, postcompose the
-- left-derived comparison for `- ⊗_R^{\mathbf L} A` with derived restriction and use the
-- universal property of left derived functors.
/-- The composite of derived extension with derived restriction is the left derived functor
required by `Adjunction.derived`. -/
private theorem derivedTensorWithAlgebra_restrictScalars_comp_isLeftDerivedFunctor :
    ((derivedTensorWithAlgebra (algebraMap R A)) ⋙
      (ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory).IsLeftDerivedFunctor
      ((Functor.associator QR
          (derivedTensorWithAlgebra (algebraMap R A))
          (ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory).inv ≫
        Functor.whiskerRight
          derivedTensorWithAlgebraComplexCounit
          ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory))
      (HomologicalComplex.quasiIso (ModuleCat R) (up ℤ)) := by
  -- TODO: once the previous counit-transport lemma is explicit, postcompose it with exact
  -- restriction and compare the result with the displayed comparison via
  -- `Functor.leftDerivedCompComparison`.
  sorry

attribute [local instance] derivedTensorWithAlgebra_restrictScalars_comp_isLeftDerivedFunctor

-- Proof sketch: dually, whisker the right-derived comparison for restriction of scalars with
-- derived extension and apply the universal property of right derived functors.
/-- The composite of derived restriction with derived extension is the right derived functor
required by `Adjunction.derived`. -/
private theorem restrictScalars_derivedTensorWithAlgebra_comp_isRightDerivedFunctor :
    (((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory) ⋙
      derivedTensorWithAlgebra (algebraMap R A)).IsRightDerivedFunctor
      (Functor.whiskerRight
          ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategoryFactors.inv)
          (derivedTensorWithAlgebra (algebraMap R A)) ≫
        (Functor.associator QA
          ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory)
          (derivedTensorWithAlgebra (algebraMap R A))).hom)
      (HomologicalComplex.quasiIso (ModuleCat A) (up ℤ)) := by
  -- TODO: whisker the exact right-derived comparison for restriction with derived tensor and
  -- transport the result to the displayed map via the canonical right-derived composition API.
  sorry

attribute [local instance] restrictScalars_derivedTensorWithAlgebra_comp_isRightDerivedFunctor

/-- Lemma 15.60.3: the derived scalar-extension functor `- \otimes_R^{\mathbf L} A : D(R) ⥤
`D(A)` is left adjoint to the restriction functor on derived categories. In canonical mathlib
form, this is the specialization of `CategoryTheory.Adjunction.derived` to the canonical
cochain-complex lift
`(ModuleCat.extendRestrictScalarsAdj (algebraMap R A)).mapHomologicalComplex (up ℤ)` together
with the derived comparison morphisms constructed above.
-/
@[stacks 0GMT]
noncomputable def derivedTensorWithAlgebraAdjunction :
    derivedTensorWithAlgebra (algebraMap R A) ⊣
      (ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory :=
  Adjunction.derived
    ((ModuleCat.extendRestrictScalarsAdj (algebraMap R A)).mapHomologicalComplex (up ℤ))
    (HomologicalComplex.quasiIso (ModuleCat R) (up ℤ))
    (HomologicalComplex.quasiIso (ModuleCat A) (up ℤ))
    derivedTensorWithAlgebraComplexCounit
    (ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategoryFactors.inv

variable (A)

private noncomputable def restrictScalarsDerivedHomologyIso
    (L : DModA) (i : ℤ) :
    (HR i).obj (restrictScalarsDerived.obj L) ≅
      (ModuleCat.restrictScalars (algebraMap R A)).obj ((HA i).obj L) :=
  let K := DerivedCategory.Q.objPreimage L
  let FK := ((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex (up ℤ)).obj K
  let eA : (HA i).obj L ≅ K.homology i :=
    ((HA i).mapIso (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat A) i).app K
  (HR i).mapIso
      ((((restrictScalarsDerived.mapIso (DerivedCategory.Q.objObjPreimageIso L)).symm) ≪≫
        ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategoryFactors.app K))) ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat R) i).app FK ≪≫
    (K.sc i).mapHomologyIso (ModuleCat.restrictScalars (algebraMap R A)) ≪≫
      (ModuleCat.restrictScalars (algebraMap R A)).mapIso eA.symm

/-- The canonical homology base-change morphism attached to `R → A`, obtained from the unit of
the derived extension/restriction adjunction by taking degree-`i` homology and transposing along
the ordinary module adjunction. -/
private noncomputable abbrev derivedTensorWithAlgebraHomologyComparisonAdjoint
    (K : DModR) (i : ℤ) :
    (HR i).obj K ⟶
      (ModuleCat.restrictScalars (algebraMap R A)).obj
        ((HA i).obj ((derivedTensorWithAlgebra (algebraMap R A)).obj K)) :=
  (HR i).map (derivedTensorWithAlgebraAdjunction.unit.app K) ≫
    (restrictScalarsDerivedHomologyIso A
      ((derivedTensorWithAlgebra (algebraMap R A)).obj K) i).hom

noncomputable def derivedTensorWithAlgebraHomologyComparison
    (K : DModR) (i : ℤ) :
    (ModuleCat.extendScalars (algebraMap R A)).obj ((HR i).obj K) ⟶
      (HA i).obj ((derivedTensorWithAlgebra (algebraMap R A)).obj K) :=
  ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap R A)).homEquiv _ _).symm <|
    derivedTensorWithAlgebraHomologyComparisonAdjoint A K i

variable {A}

/- The hom-set description attached to Lemma 15.60.3 is exactly the generic owner theorem
`CategoryTheory.Adjunction.homEquiv_unit`, specialized to the adjunction displayed just above. -/
recall CategoryTheory.Adjunction.homEquiv_unit

/- The textbook left-adjoint conclusion of Lemma 15.60.3 is the generic owner theorem
`CategoryTheory.Adjunction.isLeftAdjoint`, specialized to the derived adjunction displayed above. -/
#check
  ((derivedTensorWithAlgebraAdjunction.isLeftAdjoint :
    Functor.IsLeftAdjoint (derivedTensorWithAlgebra (algebraMap R A))))

end

end CategoryTheory
