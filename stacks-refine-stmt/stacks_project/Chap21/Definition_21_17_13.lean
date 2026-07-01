import Mathlib
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import stacks_project.Chap13.Remark_13_10_9
import stacks_project.Chap18.Lemma_18_19_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open CategoryTheory.MonoidalCategory

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
local notation "Mod" => ringedSiteModuleCategory J 𝒪
local notation "KMod" => HomotopyCategory Mod (up ℤ)
local notation "DMod" => DerivedCategory Mod
local notation "Qis" => HomotopyCategory.quasiIso Mod (up ℤ)
local notation "Qh" => (DerivedCategory.Qh : KMod ⥤ DMod)

/- Domain-style sampling for Definition 21.17.13:
- primary domain: derived tensor products on the unbounded derived category of sheaves of
  `\mathcal O`-modules on a ringed site;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `tensor_left_homotopy_functor`,
  `Functor.HasLeftDerivedFunctor`,
  `Functor.totalLeftDerived`;
- best owner abstraction: the ambient owner is `ringedSiteModuleCategory J 𝒪`, and the source
  definition is the total left derived endofunctor of homotopy-category tensoring with a fixed
  right factor;
- primitive vs derived: the primitive public data are the ambient ringed-site module category and
  the fixed object `F : DerivedCategory (ringedSiteModuleCategory J 𝒪)`. Chosen representatives in
  the homotopy category are internal implementation data, while the endofunctor
  `derivedTensorProduct F` and the notation `K ⊗^L L` are the derived public API.

Source/core/bridge triage:
- `source-facing`: the derived tensor product endofunctor `- ⊗^L F` on `D(\mathcal O)`;
- `core/canonical`: `Functor.totalLeftDerived` applied to the fixed-right-factor homotopy tensor
  functor on `ringedSiteModuleCategory J 𝒪`;
- `bridge/view`: the scoped notation `K ⊗^L L` for evaluating the owner endofunctor on objects. -/

variable [hAbelian : Abelian Mod]
variable [CategoryWithHomology Mod]
variable [hCount : HasCountableCoproducts Mod]
variable (monoidalMod : MonoidalCategory Mod)
local instance instMonoidalMod : MonoidalCategory Mod := monoidalMod
variable [MonoidalPreadditive Mod]
variable [hColim : HasColimits Mod]
variable (hCurriedTensorAdditive : (curriedTensor Mod).Additive)
local instance instCurriedTensorAdditive : (curriedTensor Mod).Additive := hCurriedTensorAdditive

variable (hTensorObjAdditive : ∀ X : Mod, ((curriedTensor Mod).obj X).Additive)
local instance instTensorObjAdditive (X : Mod) : ((curriedTensor Mod).obj X).Additive :=
  hTensorObjAdditive X

variable
    (hMapBifunctor :
      ∀ (X Y : CochainComplex Mod ℤ), CochainComplex.HasMapBifunctor X Y (curriedTensor Mod))
local instance instMapBifunctor
    (X Y : CochainComplex Mod ℤ) :
    CochainComplex.HasMapBifunctor X Y (curriedTensor Mod) :=
  hMapBifunctor X Y

/-- The homotopy-category tensor functor whose left derived functor defines derived tensoring with
a fixed right factor in `D(\mathcal O)`. -/
private noncomputable abbrev derivedTensorSourceFunctor
    (F : DMod) :
    KMod ⥤ DMod :=
  CategoryTheory.Quotient.lift (homotopic Mod (up ℤ))
    ((((curriedTensor Mod).map₂CochainComplex).flip.obj
        (Qh.objPreimage F).as) ⋙ HomotopyCategory.quotient Mod (up ℤ))
    (fun _ _ _ _ ⟨h⟩ ↦
      HomotopyCategory.eq_of_homotopy _ _
        (HomologicalComplex.mapBifunctorMapHomotopy₁ h (𝟙 (Qh.objPreimage F).as)
          (curriedTensor Mod) (up ℤ))) ⋙
    Qh

-- Proof sketch: choose a homotopy-category representative of `F`, replace it by a K-flat
-- resolution using the flat-resolution results developed above, and use the quasi-isomorphism
-- invariance of tensoring with a K-flat complex to invoke the universal property of the total left
-- derived functor.
/-- Tensoring on the homotopy category with a fixed derived right factor admits a total left
derived functor on `D(\mathcal O)`. -/
theorem derivedTensorSourceFunctor_hasLeftDerivedFunctor
    (F : DMod) :
    (derivedTensorSourceFunctor F).HasLeftDerivedFunctor Qis := sorry

/-- Definition 21.17.13: for an object `\mathcal F^\bullet` of `D(\mathcal O)`, the derived tensor
product `- \otimes_\mathcal O^{\mathbf L} \mathcal F^\bullet` is the endofunctor of `D(\mathcal
O)` obtained by left deriving the homotopy-category tensor functor with fixed right factor a
chosen representative of `\mathcal F^\bullet`. -/
noncomputable def derivedTensorProduct
    (F : DMod) :
    DMod ⥤ DMod :=
  let G : KMod ⥤ DMod := derivedTensorSourceFunctor F
  letI : G.HasLeftDerivedFunctor Qis :=
    derivedTensorSourceFunctor_hasLeftDerivedFunctor F
  G.totalLeftDerived Qh Qis

-- Proof sketch: the homotopy-category tensor functor with fixed right factor commutes with the
-- shift by Remark `13.10.9`, and the total left derived functor inherits this commutation.
/-- Derived tensoring with a fixed right factor commutes with the triangulated shift. -/
noncomputable instance derivedTensorProduct_commShift
    (F : DMod) :
    (derivedTensorProduct F).CommShift ℤ := sorry

-- Proof sketch: the underived tensor functor on the homotopy category is triangulated by Remark
-- `13.10.9`, and passing to its total left derived functor yields an exact functor on the derived
-- category.
/-- The derived tensor product endofunctor on `D(\mathcal O)` is exact in the triangulated sense.
-/
theorem derivedTensorProduct_isTriangulated
    (F : DMod) :
    (derivedTensorProduct F).IsTriangulated := sorry

end

end SheafOfModules.RingedSite

namespace RingedSiteDerivedTensor

/- Textbook surface notation for the derived tensor product object `K ⊗^L L` in `D(\mathcal O)`.
-/
scoped notation:70 K:70 " ⊗^L " L:71 =>
  CategoryTheory.Functor.obj (SheafOfModules.RingedSite.derivedTensorProduct L) K

end RingedSiteDerivedTensor
