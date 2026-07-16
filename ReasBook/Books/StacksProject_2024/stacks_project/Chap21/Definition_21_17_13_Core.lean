import Mathlib.Algebra.Homology.BifunctorHomotopy
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.Localization
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import StacksProject_2024.stacks_project.Chap13.Remark_13_10_9
import StacksProject_2024.stacks_project.Chap18.RingedSiteModuleCategoryBasic

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape
open HomotopyCategory

universe u v

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/- Primitive/derived split for Definition 21.17.13:
- primitive owner layer: the ambient module category `ringedSiteModuleCategory J 𝒪`, the
  fixed-right-factor homotopy tensor functor `derivedTensorSourceFunctor F` built from the chosen
  representative complex of `F : D(\mathcal O)`, and the derived tensor owner `derivedTensorProduct`;
- derived API layer: the left-derived universal property, commutation with shift, and the
  triangulated exactness statements, which live in `Definition_21_17_13.lean`.

This file keeps only the primitive owner data needed by later source-facing tensor-product
statements such as Lemma `21.45.5`, so those files do not need to import the heavier derived API
closure. -/

variable [Abelian (ringedSiteModuleCategory J 𝒪)]
variable [CategoryWithHomology (ringedSiteModuleCategory J 𝒪)]
variable [HasCountableCoproducts (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalPreadditive (ringedSiteModuleCategory J 𝒪)]
variable [HasColimits (ringedSiteModuleCategory J 𝒪)]
variable [(curriedTensor (ringedSiteModuleCategory J 𝒪)).Additive]
variable [∀ X : ringedSiteModuleCategory J 𝒪,
  ((curriedTensor (ringedSiteModuleCategory J 𝒪)).obj X).Additive]
variable [∀ (X Y : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ),
  CochainComplex.HasMapBifunctor X Y (curriedTensor (ringedSiteModuleCategory J 𝒪))]

instance instPreadditiveRingedSiteModuleCategory :
    Preadditive (ringedSiteModuleCategory J 𝒪) :=
  (inferInstance : Abelian (ringedSiteModuleCategory J 𝒪)).toPreadditive

instance instHasBinaryBiproductsRingedSiteModuleCategory :
    HasBinaryBiproducts (ringedSiteModuleCategory J 𝒪) :=
  Abelian.hasBinaryBiproducts

local notation "Complexes" => CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ
local notation "KMod" => HomotopyCategory (ringedSiteModuleCategory J 𝒪) (up ℤ)
local notation "DMod" => DerivedCategory (ringedSiteModuleCategory J 𝒪)
local notation "Q" =>
  (HomotopyCategory.quotient (ringedSiteModuleCategory J 𝒪) (up ℤ) : Complexes ⥤ KMod)
local notation "Qh" => (DerivedCategory.Qh : KMod ⥤ DMod)
local notation "Qis" => HomotopyCategory.quasiIso (ringedSiteModuleCategory J 𝒪) (up ℤ)

private noncomputable instance tensorComplexRight_additive
    (K : Complexes) :
    (((curriedTensor (ringedSiteModuleCategory J 𝒪)).map₂CochainComplex).flip.obj K).Additive :=
  map₂CochainComplex_flip_obj_additive
    (curriedTensor (ringedSiteModuleCategory J 𝒪))
    K

private noncomputable instance derivedTensorSourceFunctorAux_additive
    (K : Complexes) :
    ((((curriedTensor (ringedSiteModuleCategory J 𝒪)).map₂CochainComplex).flip.obj K) ⋙ Q).Additive :=
  by
    let F := ((curriedTensor (ringedSiteModuleCategory J 𝒪)).map₂CochainComplex).flip.obj K
    let _ : F.Additive := tensorComplexRight_additive (J := J) (𝒪 := 𝒪) K
    infer_instance

/-- Fixed-right-factor source tensor functor on the homotopy category, built from a chosen
cochain-complex representative before passing to a derived object. -/
noncomputable abbrev derivedTensorSourceFunctorOfComplex
    (K : Complexes) :
    KMod ⥤ DMod :=
  CategoryTheory.Quotient.lift
      (homotopic (ringedSiteModuleCategory J 𝒪) (up ℤ))
      ((((curriedTensor (ringedSiteModuleCategory J 𝒪)).map₂CochainComplex).flip.obj K) ⋙ Q)
      (fun _ _ _ _ ⟨h⟩ ↦
        HomotopyCategory.eq_of_homotopy _ _
          (HomologicalComplex.mapBifunctorMapHomotopy₁ h
            (𝟙 K)
            (curriedTensor (ringedSiteModuleCategory J 𝒪))
            (up ℤ))) ⋙
    Qh

/-- The homotopy-category tensor functor whose left derived functor defines derived tensoring with
a fixed right factor in `D(\mathcal O)`, built from `DerivedCategory.Q.objPreimage F`. -/
noncomputable abbrev derivedTensorSourceFunctor
    (F : DMod) :
    KMod ⥤ DMod :=
  derivedTensorSourceFunctorOfComplex ((DerivedCategory.Q : Complexes ⥤ DMod).objPreimage F)

-- Proof sketch: fix a representative of `F` in cochain complexes, descend fixed-right total
-- tensoring to the homotopy category via the quotient lift above, and then resolve the varying
-- left factor by K-flat complexes. Quasi-isomorphism invariance of tensoring with a K-flat
-- complex supplies the universal property needed for the total left derived functor.
/-- Tensoring on the homotopy category with a fixed right derived object admits a total left
derived functor on `D(\mathcal O)`. -/
theorem derivedTensorSourceFunctor_hasLeftDerivedFunctor
    (F : DMod) :
    (derivedTensorSourceFunctor F).HasLeftDerivedFunctor Qis := by
  sorry

attribute [instance] derivedTensorSourceFunctor_hasLeftDerivedFunctor

/-- Definition 21.17.13: for an object `\mathcal F^\bullet` of `D(\mathcal O)`, the derived tensor
product `- \otimes_\mathcal O^{\mathbf L} \mathcal F^\bullet` is the endofunctor of `D(\mathcal
O)` obtained by left deriving the homotopy-category tensor functor with fixed right factor a
chosen representative of `\mathcal F^\bullet`. -/
noncomputable def derivedTensorProduct
    (F : DMod) [Functor.HasLeftDerivedFunctor (derivedTensorSourceFunctor F) Qis] :
    DMod ⥤ DMod :=
  (derivedTensorSourceFunctor F).totalLeftDerived Qh Qis

/-- The canonical object `K ⊗^L L` of `D(\mathcal O)` obtained by evaluating the derived tensor
functor with right factor `L` at `K`. This stable object-level owner underlies the exported
notation `K ⊗^L L`. -/
noncomputable def derivedTensorObj
    (K L : DMod) [Functor.HasLeftDerivedFunctor (derivedTensorSourceFunctor L) Qis] :
    DMod :=
  (derivedTensorProduct L).obj K

/-- The canonical counit exhibiting `derivedTensorProduct F` as a left derived functor of
`derivedTensorSourceFunctor F`. -/
noncomputable abbrev derivedTensorProductCounit
    (F : DMod) [Functor.HasLeftDerivedFunctor (derivedTensorSourceFunctor F) Qis] :
    Qh ⋙
      derivedTensorProduct F ⟶
      derivedTensorSourceFunctor F := by
  simpa [derivedTensorProduct] using
    ((derivedTensorSourceFunctor F).totalLeftDerivedCounit Qh Qis)

section

omit [HasSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasCountableCoproducts (ringedSiteModuleCategory J 𝒪)]
  [MonoidalPreadditive (ringedSiteModuleCategory J 𝒪)]
  [HasColimits (ringedSiteModuleCategory J 𝒪)]

/- Derived tensoring with a fixed right factor is the total left derived functor of the
corresponding homotopy-category tensor functor. -/
theorem derivedTensorProduct_isLeftDerivedFunctor
    (F : DMod) [Functor.HasLeftDerivedFunctor (derivedTensorSourceFunctor F) Qis] :
    (derivedTensorProduct F).IsLeftDerivedFunctor
      (derivedTensorProductCounit F)
      Qis := by
  simpa [derivedTensorProduct, derivedTensorProductCounit] using
    (show
        ((derivedTensorSourceFunctor F).totalLeftDerived Qh Qis).IsLeftDerivedFunctor
          ((derivedTensorSourceFunctor F).totalLeftDerivedCounit Qh Qis)
          Qis from inferInstance)

end

attribute [instance] derivedTensorProduct_isLeftDerivedFunctor

end

end SheafOfModules.RingedSite

namespace RingedSiteDerivedTensor

open CategoryTheory

/- Textbook surface notation for the derived tensor product object `K ⊗^L L` in `D(\mathcal O)`.
-/
scoped notation:70 K:70 " ⊗^L " L:71 =>
  SheafOfModules.RingedSite.derivedTensorObj K L

end RingedSiteDerivedTensor
