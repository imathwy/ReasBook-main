import Mathlib.Algebra.Homology.BifunctorHomotopy
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.Localization
import Mathlib.CategoryTheory.Localization.Monoidal.Braided
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import StacksProject_2024.Chap15.Lemma_15_58_3_Owner
import StacksProject_2024.Chap17.Definition_17_5_1
import StacksProject_2024.Chap13.Remark_13_10_9
import StacksProject_2024.Chap13.Situation_13_15_1
import StacksProject_2024.Chap20.Definition_20_26_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open HomotopyCategory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false

universe u

namespace AlgebraicGeometry.RingedSpace

/- Core owner layer for Definition 20.26.14:
- source-facing owner: `derivedTensorProduct`;
- core data: the fixed-right-factor source functor, its left-derived existence, and the counit;
- derived exactness companions such as `CommShift` and `IsTriangulated` live in the heavier
  `Definition_20_26_14.lean` layer and are intentionally excluded from this core file. -/

variable {X : RingedSpace.{u}}
variable [CategoryWithHomology (RingedSpace.Modules X)]
variable [HasCountableCoproducts (RingedSpace.Modules X)]
variable [MonoidalCategory (RingedSpace.Modules X)]
variable [MonoidalPreadditive (RingedSpace.Modules X)]
variable [HasColimits (RingedSpace.Modules X)]
variable [(curriedTensor (RingedSpace.Modules X)).Additive]
variable [∀ ℱ : RingedSpace.Modules X, ((curriedTensor (RingedSpace.Modules X)).obj ℱ).Additive]
variable [∀ (ℱ 𝒢 : CochainComplex (RingedSpace.Modules X) ℤ),
  CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor (RingedSpace.Modules X))]

/-- An abelian category of `\mathcal O_X`-modules is preadditive. -/
local instance preadditiveModules20_26_14_core : Preadditive (RingedSpace.Modules X) :=
  (inferInstance : Abelian (RingedSpace.Modules X)).toPreadditive

/-- An abelian category of `\mathcal O_X`-modules has binary biproducts. -/
local instance hasBinaryBiproductsModules20_26_14_core :
    HasBinaryBiproducts (RingedSpace.Modules X) :=
  Abelian.hasBinaryBiproducts

local notation "Complexes" => CochainComplex (RingedSpace.Modules X) ℤ
local notation "KMod" => HomotopyCategory (RingedSpace.Modules X) (up ℤ)
local notation "DMod" => DerivedCategory (RingedSpace.Modules X)
local notation "Q" =>
  (HomotopyCategory.quotient (RingedSpace.Modules X) (up ℤ) : Complexes ⥤ KMod)
local notation "Qh" => (DerivedCategory.Qh : KMod ⥤ DMod)
local notation "Qis" => HomotopyCategory.quasiIso (RingedSpace.Modules X) (up ℤ)

private noncomputable instance tensorComplexRight_additive
    (K : Complexes) :
    (((curriedTensor (RingedSpace.Modules X)).map₂CochainComplex).flip.obj K).Additive :=
  map₂CochainComplex_flip_obj_additive
    (curriedTensor (RingedSpace.Modules X))
    K

private noncomputable instance derivedTensorSourceHomotopyFunctorOfComplex_aux_additive
    (K : Complexes) :
    ((((curriedTensor (RingedSpace.Modules X)).map₂CochainComplex).flip.obj K) ⋙ Q).Additive :=
  by
    let F := ((curriedTensor (RingedSpace.Modules X)).map₂CochainComplex).flip.obj K
    let _ : F.Additive := tensorComplexRight_additive (X := X) K
    infer_instance

/-- Fixed-right-factor tensor-totalization descends to a functor from the homotopy category to the
derived category. -/
noncomputable abbrev derivedTensorSourceHomotopyFunctorOfComplex
    (K : Complexes) :
    KMod ⥤ DMod :=
  CategoryTheory.Quotient.lift
      (homotopic (RingedSpace.Modules X) (up ℤ))
      ((((curriedTensor (RingedSpace.Modules X)).map₂CochainComplex).flip.obj K) ⋙ Q)
      (fun _ _ _ _ ⟨h⟩ ↦
        HomotopyCategory.eq_of_homotopy _ _
          (HomologicalComplex.mapBifunctorMapHomotopy₁ h
            (𝟙 K)
            (curriedTensor (RingedSpace.Modules X))
            (up ℤ))) ⋙
    Qh

/-- Fixed-right-factor source tensor functor on the homotopy category, built from a chosen
cochain-complex representative before passing to a derived object. -/
noncomputable abbrev derivedTensorSourceFunctor
    (ℱ : DMod) :
    KMod ⥤ DMod :=
  derivedTensorSourceHomotopyFunctorOfComplex
    ((DerivedCategory.Q : Complexes ⥤ DMod).objPreimage ℱ)

-- Proof sketch: fix a representative of `ℱ` in cochain complexes, descend fixed-right total
-- tensoring to the homotopy category via the quotient lift above, and then resolve the varying
-- left factor by K-flat complexes. Quasi-isomorphism invariance of tensoring with a K-flat
-- complex supplies the universal property needed for the total left derived functor.
/-- Tensoring on the homotopy category with a fixed right complex admits a total left derived
functor on `D(\mathcal O_X)`. -/
theorem derivedTensorSourceFunctor_hasLeftDerivedFunctor
    (ℱ : DMod) :
    (derivedTensorSourceFunctor ℱ).HasLeftDerivedFunctor Qis := by
  sorry

attribute [instance] derivedTensorSourceFunctor_hasLeftDerivedFunctor

/-- Definition 20.26.14: for an object `\mathcal F^\bullet` of `D(\mathcal O_X)`, the derived
tensor product `- \otimes_{\mathcal O_X}^{\mathbf L} \mathcal F^\bullet` is the endofunctor of
`D(\mathcal O_X)` obtained by left deriving the homotopy-category tensor functor with fixed right
factor a chosen representative of `\mathcal F^\bullet`. -/
@[stacks 06YH]
noncomputable def derivedTensorProduct
    (ℱ : DMod) [Functor.HasLeftDerivedFunctor (derivedTensorSourceFunctor ℱ) Qis] :
    DMod ⥤ DMod :=
  (derivedTensorSourceFunctor ℱ).totalLeftDerived Qh Qis

/-- The canonical counit exhibiting `derivedTensorProduct ℱ` as the total left derived functor of
the fixed-right-factor source functor built from `ℱ`. -/
noncomputable abbrev derivedTensorProductCounit
    (ℱ : DMod) [Functor.HasLeftDerivedFunctor (derivedTensorSourceFunctor ℱ) Qis] :
    Qh ⋙ derivedTensorProduct ℱ ⟶
      derivedTensorSourceFunctor ℱ :=
  by
    simpa [derivedTensorProduct] using
      ((derivedTensorSourceFunctor ℱ).totalLeftDerivedCounit Qh Qis)

-- Proof sketch: this is the defining `IsLeftDerivedFunctor` witness for the total left derived
-- functor used in `derivedTensorProduct`.
omit [HasCountableCoproducts (RingedSpace.Modules X)]
  [MonoidalPreadditive (RingedSpace.Modules X)]
  [HasColimits (RingedSpace.Modules X)] in
/-- Derived tensoring with a fixed right factor is the left derived functor of the corresponding
homotopy-category tensor functor. -/
theorem derivedTensorProduct_isLeftDerivedFunctor
    (ℱ : DMod) [Functor.HasLeftDerivedFunctor (derivedTensorSourceFunctor ℱ) Qis] :
    (derivedTensorProduct ℱ).IsLeftDerivedFunctor
      (derivedTensorProductCounit ℱ)
      Qis := by
  simpa [derivedTensorProduct, derivedTensorProductCounit] using
    (show
      ((derivedTensorSourceFunctor ℱ).totalLeftDerived Qh Qis).IsLeftDerivedFunctor
        ((derivedTensorSourceFunctor ℱ).totalLeftDerivedCounit Qh Qis)
        Qis from inferInstance)

attribute [instance] derivedTensorProduct_isLeftDerivedFunctor

end AlgebraicGeometry.RingedSpace

namespace RingedSpaceDerivedTensor

/- Textbook surface notation for the derived tensor product object `K ⊗^L L` in
`D(\mathcal O_X)`. -/
scoped notation:70 K:70 " ⊗^L " L:71 =>
  Functor.obj (AlgebraicGeometry.RingedSpace.derivedTensorProduct L) K

end RingedSpaceDerivedTensor
