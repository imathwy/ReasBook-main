import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_60_1 (from Chap15) -/
noncomputable section

open CategoryTheory
open ComplexShape
open CategoryTheory.MonoidalCategory
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R A : Type u} [CommRing R] [CommRing A]

/- Domain-style sampling for Lemma 15.60.1:
- primary domain: derived change of rings for module categories over a commutative ring map and a
  fixed derived target complex over the target ring;
- sampled owner declarations:
  `derivedTensorWithAlgebra`,
  `derivedTensorProduct`,
  `Functor.totalLeftDerived`,
  `Functor.totalLeftDerivedCounit`;
- best owner abstraction: the source-facing owner is the general change-of-rings functor
  `derivedTensorChangeOfRings σ N : D(R) ⥤ D(A)` for an explicit ring map `σ : R →+* A`, built
  from the canonical derived scalar-extension owner `derivedTensorWithAlgebra σ` and the derived
  tensor-product owner `derivedTensorProduct N` on `D(A)`;
- primitive vs. derived:
  primitive data are the explicit ring map `σ`, the fixed object `N : D(A)`, and the two owner
  functors `derivedTensorWithAlgebra σ` and `derivedTensorProduct N`;
  the change-of-rings functor and its notation are derived API over those owners;
- source/core/bridge triage:
  `source-facing`: `derivedTensorChangeOfRings σ N`;
  `core/canonical`: `derivedTensorWithAlgebra σ` and `derivedTensorProduct N`;
  `bridge/view`: the textbook object notation `K ⊗[R]^L[A] N`. -/

local notation "DModA" => DerivedCategory (ModuleCat A)

local instance :
    ∀ (K₁ K₂ : CochainComplex (ModuleCat A) ℤ),
      CochainComplex.HasMapBifunctor K₁ K₂ (curriedTensor (ModuleCat A)) :=
  inferInstance

/-- Lemma 15.60.1: for a fixed derived `A`-complex `N^•`, the change-of-rings derived tensor
functor `- \otimes_R^{\mathbf L} N^• : D(R) ⟶ D(A)` is defined as the composite of derived
scalar extension `- \otimes_R^{\mathbf L} A` with the derived tensor product functor
`- \otimes_A^{\mathbf L} N^•` on `D(A)`. -/
noncomputable def derivedTensorChangeOfRings
    (σ : R →+* A) (N : DModA) :
    DerivedCategory (ModuleCat R) ⥤ DModA :=
  derivedTensorWithAlgebra σ ⋙ derivedTensorProduct N

namespace DerivedTensorChangeOfRings

/- Textbook notation for the derived change-of-rings object
`K \otimes_R^{\mathbf L} N` in `D(A)`. -/
scoped notation:70 K:70 " ⊗[" R:70 "]^L[" A:70 "] " N:71 =>
  Functor.obj (CategoryTheory.derivedTensorChangeOfRings (algebraMap R A) N) K

end DerivedTensorChangeOfRings

open scoped DerivedTensorChangeOfRings

/-- The change-of-rings derived tensor functor commutes with the triangulated shift. -/
noncomputable instance derivedTensorChangeOfRings_commShift (σ : R →+* A) (N : DModA) :
    (derivedTensorChangeOfRings σ N).CommShift ℤ := by
  dsimp [derivedTensorChangeOfRings]
  infer_instance

-- Proof sketch: this is the composition of the exact functors `- \otimes_R^{\mathbf L} A` and
-- `- \otimes_A^{\mathbf L} N^•`, so the result is exact by functoriality of triangulated
-- structure under composition.
/-- The change-of-rings derived tensor functor is exact in the triangulated sense. -/
theorem derivedTensorChangeOfRings_isTriangulated (σ : R →+* A) (N : DModA) :
    (derivedTensorChangeOfRings σ N).IsTriangulated := by
  let F := derivedTensorWithAlgebra σ
  let G := derivedTensorProduct N
  letI : F.CommShift ℤ := by
    simpa [F] using (inferInstance : (derivedTensorWithAlgebra σ).CommShift ℤ)
  letI : G.CommShift ℤ := by
    simpa [G] using (derivedTensorProduct_commShift N)
  letI : F.IsTriangulated := by
    simpa [F] using derivedTensorWithAlgebra_isTriangulated σ
  letI : G.IsTriangulated := by
    simpa [G] using derivedTensorProduct_isTriangulated N
  change (F ⋙ G).IsTriangulated
  exact
    { map_distinguished := fun T hT ↦
        Pretriangulated.isomorphic_distinguished _
          (G.map_distinguished _ (F.map_distinguished T hT)) _
          ((Functor.mapTriangleCompIso F G).app T) }

end

end CategoryTheory

/-! ### Lemma_15_60_2 (from Chap15) -/
noncomputable section

open CategoryTheory
open ComplexShape
open CategoryTheory.MonoidalCategory
open scoped DerivedTensorChangeOfRings
open scoped DerivedTensorProduct
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

local notation "CpxA" => CochainComplex (ModuleCat A) ℤ
local notation "DModR" => DerivedCategory (ModuleCat R)
local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "σ" => (algebraMap R A)

local instance :
    ∀ (K₁ K₂ : CpxA), CochainComplex.HasMapBifunctor K₁ K₂ (curriedTensor (ModuleCat A)) :=
  inferInstance

/- Domain-style sampling for Lemma 15.60.2:
- primary domain: derived change of rings `D(R) ⥤ D(A)` together with the right-variable
  functoriality of the derived tensor product on `D(A)`;
- sampled owner declarations:
  `derivedTensorChangeOfRings`,
  `derivedTensorWithAlgebra`,
  `derivedTensorProduct`,
  `tensoringRight`,
  `DerivedCategory.Q`;
- best owner abstraction: the source-facing owner is the chapter-local change-of-rings functor
  `derivedTensorChangeOfRings σ N : D(R) ⥤ D(A)`, while right-variable functoriality in `N`
  is implemented by the tensoring-right owner `(tensoringRight DModA).obj N` on `D(A)`;
- primitive vs. derived:
  primitive data are the complex map `f : L ⟶ N` and its image `DerivedCategory.Q.map f` in
  `D(A)`;
  the induced natural transformation between change-of-rings functors is derived API;
- source/core/bridge triage:
  `source-facing`: the map `1 \otimes f` on change-of-rings derived tensor functors;
  `core/canonical`: `derivedTensorChangeOfRings` together with the tensoring-right owner on
    `D(A)`;
  `bridge/view`: passing from a cochain complex to a derived object via `Q.obj`.
- layer: this file is a `bridge/view`, so its public entry should live over
  `derivedTensorChangeOfRings`, with the cochain-level map kept as a thin bridge via `Q.map`. -/

variable (R)

private noncomputable def derivedTensorChangeOfRingsIso
    (N : DModA) :
    derivedTensorWithAlgebra σ ⋙ (tensoringRight DModA).obj N ≅
      derivedTensorChangeOfRings σ N :=
  Functor.isoWhiskerLeft (derivedTensorWithAlgebra σ)
    (tensoringRightIsoDerivedTensorProduct N)

/-- The morphism on change-of-rings derived tensor functors induced by a morphism in the right
factor on `D(A)`. -/
noncomputable def derivedTensorChangeOfRingsMap
    {L N : DModA} (f : L ⟶ N) :
    derivedTensorChangeOfRings σ L ⟶ derivedTensorChangeOfRings σ N :=
  let eL := derivedTensorChangeOfRingsIso R L
  let eN := derivedTensorChangeOfRingsIso R N
  eL.inv ≫ Functor.whiskerLeft (derivedTensorWithAlgebra σ) ((tensoringRight DModA).map f) ≫ eN.hom

/-- The component of the map induced by `f : L ⟶ N` on change-of-rings derived tensor functors is
obtained by tensoring with `f` over `A`, transported through the canonical comparison between the
owner tensor and the source-facing derived tensor product. -/
@[simp]
theorem derivedTensorChangeOfRingsMap_app
    {L N : DModA} (f : L ⟶ N) (K : DModR) :
    (derivedTensorChangeOfRingsMap R f).app K =
      ((derivedCategory_tensorObj_iso_derivedTensorProduct
            (K ⊗[R]^L[A]) L).inv ≫
        ((K ⊗[R]^L[A]) ◁ f) ≫
        (derivedCategory_tensorObj_iso_derivedTensorProduct
            (K ⊗[R]^L[A]) N).hom :
          K ⊗[R]^L[A] L ⟶ K ⊗[R]^L[A] N) := by
  simp [derivedTensorChangeOfRingsMap, derivedTensorChangeOfRingsIso, derivedTensorChangeOfRings]

/-- The component of `1 \otimes f` at `K : D(R)` is obtained by tensoring the scalar-extended
object `K \otimes_R^{\mathbf L} A` with `Q.map f` over `A`, transported through the canonical
identifications with the right tensor functors on `D(A)`. -/
@[simp]
theorem derivedTensorChangeOfRingsMap_app_of_complexMap
    {L N : CpxA} (f : L ⟶ N) (K : DModR) :
    (derivedTensorChangeOfRingsMap R (DerivedCategory.Q.map f)).app K =
      ((derivedCategory_tensorObj_iso_derivedTensorProduct
            (K ⊗[R]^L[A]) (DerivedCategory.Q.obj L)).inv ≫
        ((K ⊗[R]^L[A]) ◁ DerivedCategory.Q.map f) ≫
        (derivedCategory_tensorObj_iso_derivedTensorProduct
            (K ⊗[R]^L[A]) (DerivedCategory.Q.obj N)).hom :
          K ⊗[R]^L[A] (DerivedCategory.Q.obj L) ⟶
            K ⊗[R]^L[A] (DerivedCategory.Q.obj N)) := by
  simpa using
    derivedTensorChangeOfRingsMap_app R (DerivedCategory.Q.map f) K

/-- If a morphism `f` in `D(A)` is an isomorphism, then the induced change-of-rings tensor map is
an isomorphism of functors `D(R) ⥤ D(A)`. -/
theorem derivedTensorChangeOfRingsMap_isIso
    {L N : DModA} (f : L ⟶ N) [IsIso f] :
    IsIso (derivedTensorChangeOfRingsMap R f) := by
  let eL := derivedTensorChangeOfRingsIso R L
  let eN := derivedTensorChangeOfRingsIso R N
  letI : IsIso ((tensoringRight DModA).map f) := by
    infer_instance
  letI (K : DModR) :
      IsIso
        ((Functor.whiskerLeft (derivedTensorWithAlgebra σ) ((tensoringRight DModA).map f)).app
          K) := by
    change IsIso (((tensoringRight DModA).map f).app ((derivedTensorWithAlgebra σ).obj K))
    infer_instance
  letI :
      IsIso (Functor.whiskerLeft (derivedTensorWithAlgebra σ) ((tensoringRight DModA).map f)) :=
    NatIso.isIso_of_isIso_app _
  letI : IsIso eL.inv := by
    infer_instance
  letI : IsIso eN.hom := by
    infer_instance
  change
    IsIso
      (eL.inv ≫
        Functor.whiskerLeft (derivedTensorWithAlgebra σ) ((tensoringRight DModA).map f) ≫
        eN.hom)
  infer_instance

/-- If `f` is a quasi-isomorphism, then the induced change-of-rings tensor transformation
`1 \otimes f` is an isomorphism of functors `D(R) ⥤ D(A)`. -/
theorem derivedTensorChangeOfRingsMap_isIso_of_quasiIso
    {L N : CpxA} (f : L ⟶ N) [QuasiIso f] :
    IsIso (derivedTensorChangeOfRingsMap R (DerivedCategory.Q.map f)) := by
  letI : IsIso (DerivedCategory.Q.map f) := by
    infer_instance
  simpa using
    derivedTensorChangeOfRingsMap_isIso R (DerivedCategory.Q.map f)

end

end CategoryTheory

/-! ### Lemma_15_60_3 (from Chap15) -/
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
  (ModuleCat.extendScalars (algebraMap R A)).mapHomologicalComplex (up ℤ)

private abbrev extendScalarsHomotopy : KModR ⥤ KModA :=
  (ModuleCat.extendScalars (algebraMap R A)).mapHomotopyCategory (up ℤ)

/-- The derived-category restriction-of-scalars functor along `R → A`. -/
private abbrev restrictScalarsDerived : DModA ⥤ DModR :=
  (ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory

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
      (HomologicalComplex.quasiIso (ModuleCat R) (up ℤ)) := sorry

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
      (HomologicalComplex.quasiIso (ModuleCat A) (up ℤ)) := sorry

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
      (HomologicalComplex.quasiIso (ModuleCat R) (up ℤ)) := sorry

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
      (HomologicalComplex.quasiIso (ModuleCat A) (up ℤ)) := sorry

attribute [local instance] restrictScalars_derivedTensorWithAlgebra_comp_isRightDerivedFunctor

/-- Lemma 15.60.3: the derived scalar-extension functor `- \otimes_R^{\mathbf L} A : D(R) ⥤
`D(A)` is left adjoint to the restriction functor on derived categories. In canonical mathlib
form, this is the specialization of `CategoryTheory.Adjunction.derived` to the canonical
cochain-complex lift
`(ModuleCat.extendRestrictScalarsAdj (algebraMap R A)).mapHomologicalComplex (up ℤ)` together
with the derived comparison morphisms constructed above.
-/
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

/-! ### Remark_15_60_4_Warning (from Chap15) -/
noncomputable section

open CategoryTheory
open MvPolynomial
open Opposite
open scoped DerivedTensorChangeOfRings DerivedTensorProduct DerivedTensorWithAlgebra

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

namespace Remark15604Warning

section

variable (k : Type*) [CommRing k]

local notation "Rxy" => MvPolynomial (Fin 2) k

/-- The quotient ring `A = k[x, y] / (xy)` from Remark `15.60.4`. -/
abbrev Ring : Type _ :=
  Rxy ⧸ principalIdeal ((X (0 : Fin 2) : Rxy) * (X (1 : Fin 2) : Rxy))

local notation "A" => Ring k
local notation "DModA" => DerivedCategory (ModuleCat A)
private abbrev single₀ : ModuleCat A ⥤ DModA := ModuleCat.single0Functor

/-- The class of `x` in the quotient ring `A = k[x, y] / (xy)`. -/
abbrev x : Ring k :=
  Ideal.Quotient.mk _ (X (0 : Fin 2) : Rxy)

/-- The object `N = A / (x)` viewed in `D(A)`. -/
abbrev N : DModA :=
  Functor.obj (single₀ k) (ModuleCat.of A (A ⧸ principalIdeal (x k)))

/-- The object `N' = A` viewed in `D(A)`. -/
abbrev NPrime : DModA :=
  Functor.obj (single₀ k) (ModuleCat.of A A)

end

end Remark15604Warning

section

variable (k : Type*) [CommRing k]

local notation "R" => MvPolynomial (Fin 2) k
local notation "A" => Remark15604Warning.Ring k
local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "x" => Remark15604Warning.x k
local notation "N" => Remark15604Warning.N k
local notation "N'" => Remark15604Warning.NPrime k

/- Domain-style sampling for Remark 15.60.4:
- primary domain: change-of-rings derived tensor products in derived categories of modules over a
  quotient of a polynomial ring, together with the chapter's one-variable powered-Koszul stage
  owner for the two-term complex `A ⟶ A`;
- sampled owner declarations of the same kind:
  `ModuleCat.single0Functor`,
  `principalIdeal`,
  `derivedTensorChangeOfRings`,
  `(ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory`,
  `derivedCompletionKoszulPowersDerivedInverseSystem`;
- best owner abstraction: `derivedTensorChangeOfRings` owns the two change-of-rings tensor
  objects, `(ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory` owns the derived
  restriction-of-scalars operation, `ModuleCat.single0Functor` owns the degree-zero derived
  objects, `principalIdeal` owns the one-generator ideals `(xy)` and `(x)`, while the
  source-facing objects of the warning itself are the public abbreviations
  `Remark15604Warning.Ring k`, `Remark15604Warning.x k`, `Remark15604Warning.N k`, and
  `Remark15604Warning.NPrime k`; the canonical stage
  `(derivedCompletionKoszulPowersDerivedInverseSystem (fun _ : Fin 1 ↦ x)).obj (Opposite.op 0)`
  from Lemma `15.92.16` represents the two-term complex `A \xrightarrow{x} A`;
- primitive data: the ring `A = k[x, y] / (xy)`, the element `x ∈ A`, and the degree-zero derived
  objects `N = (A / (x))[0]` and `N' = A[0]`;
- derived API: the canonical degree-zero owner `ModuleCat.single0Functor`, the derived
  restriction-of-scalars images of `N` and `N'`, the two change-of-rings tensor objects, the
  canonical Koszul model
  `(derivedCompletionKoszulPowersDerivedInverseSystem (fun _ : Fin 1 ↦ x)).obj (Opposite.op 0)`,
  the split model `N[1] ⊞ N`, and the comparison/non-isomorphism theorems.

Source/core/bridge triage:
- `source-facing`: the warning counterexample objects `N`, `N'`, their restriction-of-scalars
  images, their two change-of-rings tensor products, and the statement that the resulting objects
  of `D(A)` are not isomorphic;
- `core/canonical`: `derivedTensorChangeOfRings`,
  `(ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory`, the powered Koszul tower
  `K^•[n](f)`, and `derivedCompletionKoszulPowersDerivedInverseSystem`;
- `bridge/view`: the two comparison theorems identifying the source-facing tensors with the
  canonical two-term Koszul model and the split object. -/

-- Proof sketch: in the warning example `N = A/(x)` and `N' = A`. The remark computes
-- `((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj N) \otimes_R^{\mathbf L}
-- N'` as the two-term complex `A \xrightarrow{x} A`, while
-- `((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj N') \otimes_R^{\mathbf L}
-- N` is computed as `N[1] ⊞ N`.
/-- The change-of-rings object
`((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj N) ⊗_R^{\mathbf L} N'`
is represented by the two-term complex `A \xrightarrow{x} A`, namely the canonical derived
powered-Koszul stage. -/
theorem Remark15604Warning.nTensorNPrime_iso_koszulStage0 :
    IsIsomorphic
      (((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj N) ⊗[R]^L[A] N')
      ((derivedCompletionKoszulPowersDerivedInverseSystem (fun _ : Fin 1 ↦ x)).obj (op 0)) := sorry

/-- The second change-of-rings object
`((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj N') ⊗_R^{\mathbf L} N`
is represented by `N[1] ⊞ N`. -/
theorem Remark15604Warning.nPrimeTensorN_iso_shiftBiproduct :
    IsIsomorphic
      (((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj N') ⊗[R]^L[A] N)
      (N⟦(1 : ℤ)⟧ ⊞ N) := sorry

section

variable [Nontrivial k]

/- Remark 15.60.4 (Warning): for any nontrivial commutative ring `k`, with `R = k[x,y]`,
`A = R/(xy)`, `N = A/(x)`, and `N' = A`, the two change-of-rings derived tensor products
`((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj N) ⊗_R^{\mathbf L} N'`
and
`((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj N') ⊗_R^{\mathbf L} N`
are not isomorphic in `D(A)`.
-/
theorem Remark15604Warning.counterexample :
    ¬ IsIsomorphic
      (((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj N) ⊗[R]^L[A] N')
      (((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj N') ⊗[R]^L[A] N) :=
  sorry

end

end

end CategoryTheory

/-! ### Lemma_15_60_5 (from Chap15) -/
open CategoryTheory CategoryTheory.Pretriangulated
open ComplexShape HomotopyCategory

noncomputable section

universe u

namespace CochainComplex

section

variable {R : Type u} [CommRing R]

local notation "KHom" => HomotopyCategory (ModuleCat R) (up ℤ)

/-
Domain-style sampling for Lemma 15.60.5:
- primary domain: K-flat objects in the homotopy category `K(R)` of cochain complexes of
  `R`-modules and their behavior in distinguished triangles;
- sampled owner declarations:
  `HomotopyCategory.IsKFlat`,
  `CochainComplex.isKFlat_obj₃_of_distinguished_triangle`,
  `CochainComplex.isKFlat_obj₂_of_distinguished_triangle`,
  `CochainComplex.isKFlat_obj₁_of_distinguished_triangle`;
- best owner abstraction: the owner layer is already the object property `K ↦ K.IsKFlat` on
  `K(R)`, with the three two-out-of-three distinguished-triangle consequences packaged by the
  canonical theorems above;
- primitive vs. derived:
  primitive data are only a distinguished triangle `T` in `K(R)` and K-flatness hypotheses on two
  of its vertices;
  the three closure implications are derived API from the existing owner theorems, so this file
  should specialize those directly instead of keeping a parallel local theorem family.

Source/core/bridge triage:
- `source-facing`: the three K-flat two-out-of-three implications for distinguished triangles in
  `K(R)`;
- `core/canonical`: `HomotopyCategory.IsKFlat` and the owner theorems
  `isKFlat_obj₃_of_distinguished_triangle`, `isKFlat_obj₂_of_distinguished_triangle`,
  `isKFlat_obj₁_of_distinguished_triangle`;
- `bridge/view`: the `ModuleCat R` specialization of those canonical `K(C)` owner theorems to the
  source-local homotopy category `K(R)`.
-/

/- Lemma 15.60.5 (1): if `T` is a distinguished triangle in `K(R)` and the first two terms are
K-flat, then the third term is K-flat. This file checks the canonical owner theorem from
`Lemma_15_59_5` on the specialized source-facing surface `K(R)`. -/
#check
  (isKFlat_obj₃_of_distinguished_triangle :
    (T : Triangle KHom) → T ∈ distTriang KHom → T.obj₁.IsKFlat → T.obj₂.IsKFlat →
      T.obj₃.IsKFlat)

/- Lemma 15.60.5 (2): if `T` is a distinguished triangle in `K(R)` and the first and third terms
are K-flat, then the second term is K-flat. This file checks the canonical owner theorem from
`Lemma_15_59_5` on the specialized source-facing surface `K(R)`. -/
#check
  (isKFlat_obj₂_of_distinguished_triangle :
    (T : Triangle KHom) → T ∈ distTriang KHom → T.obj₁.IsKFlat → T.obj₃.IsKFlat →
      T.obj₂.IsKFlat)

/- Lemma 15.60.5 (3): if `T` is a distinguished triangle in `K(R)` and the second and third terms
are K-flat, then the first term is K-flat. This file checks the canonical owner theorem from
`Lemma_15_59_5` on the specialized source-facing surface `K(R)`. -/
#check
  (isKFlat_obj₁_of_distinguished_triangle :
    (T : Triangle KHom) → T ∈ distTriang KHom → T.obj₂.IsKFlat → T.obj₃.IsKFlat →
      T.obj₁.IsKFlat)

end

end CochainComplex
