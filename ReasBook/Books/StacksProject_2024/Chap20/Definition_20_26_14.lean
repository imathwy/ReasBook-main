import Mathlib
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import StacksProject_2024.Chap17.Definition_17_5_1
import StacksProject_2024.Chap13.Remark_13_10_9
import StacksProject_2024.Chap20.Definition_20_26_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false

namespace AlgebraicGeometry.RingedSpace

/-
Domain-style sampling for Definition 20.26.14:
- primary domain: fixed-right-factor tensoring on the homotopy category of `\mathcal O_X`-modules
  and its total left derived functor on `D(\mathcal O_X)`;
- sampled owner declarations:
  `Functor.map₂CochainComplex`,
  `Functor.mapHomotopyCategory`,
  `Functor.totalLeftDerived`,
  `Functor.totalLeftDerivedCounit`,
  `CategoryTheory.derivedTensorProduct` from Chapter 15;
- best owner abstraction: the public owner here is the endofunctor-valued
  `derivedTensorProduct : D(\mathcal O_X) → D(\mathcal O_X) ⥤ D(\mathcal O_X)`, while the chosen
  representative of the right factor, the homotopy-category source functor, and the derived-functor
  witness data are internal construction data for that owner via `Functor.totalLeftDerived`;
- primitive vs derived: the primitive mathematical input is only the fixed right factor
  `ℱ : D(\mathcal O_X)`, while the shift compatibility and triangulated exactness of
  `derivedTensorProduct ℱ` are derived API.

Source/core/bridge triage:
- `source-facing`: the derived tensor product on `D(\mathcal O_X)`;
- `core/canonical`: `Functor.totalLeftDerived` of the canonical fixed-right-factor homotopy tensor
  functor;
- `bridge/view`: no extra bridge owner is needed, since the source item is already the canonical
  endofunctor built from that core construction.

Notation decision:
- the high-frequency source-facing surface is the object-level derived tensor product, so the file
  exposes a scoped notation `K ⊗^L L` for downstream object statements;
- the owner remains the functor-valued declaration `derivedTensorProduct`, and the notation is only
  its object-level surface. -/

variable {X : RingedSpace}
variable [hAbelian : Abelian (RingedSpace.Modules X)]
variable [CategoryWithHomology (RingedSpace.Modules X)]
variable [HasCountableCoproducts (RingedSpace.Modules X)]
variable [MonoidalCategory (RingedSpace.Modules X)]
variable [MonoidalPreadditive (RingedSpace.Modules X)]
variable [HasColimits (RingedSpace.Modules X)]
variable [(curriedTensor ((RingedSpace.Modules X))).Additive]
variable [∀ ℱ : (RingedSpace.Modules X), ((curriedTensor ((RingedSpace.Modules X))).obj ℱ).Additive]
variable [∀ (ℱ 𝒢 : CochainComplex (RingedSpace.Modules X) ℤ),
  CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor ((RingedSpace.Modules X)))]

/-- An abelian category of `\mathcal O_X`-modules is preadditive. -/
local instance : Preadditive (RingedSpace.Modules X) :=
  hAbelian.toPreadditive

/-- An abelian category of `\mathcal O_X`-modules has binary biproducts. -/
local instance :
    HasBinaryBiproducts (RingedSpace.Modules X) :=
  Abelian.hasBinaryBiproducts

local notation "KMod" => HomotopyCategory (RingedSpace.Modules X) (up ℤ)
local notation "DMod" => DerivedCategory (RingedSpace.Modules X)
local notation "Qh" => (DerivedCategory.Qh : KMod ⥤ DMod)
local notation "Qis" => HomotopyCategory.quasiIso (RingedSpace.Modules X) (up ℤ)

/-- The homotopy-category tensor functor whose left derived functor defines derived tensoring with
a fixed right factor in `D(\mathcal O_X)`. -/
private noncomputable abbrev derivedTensorSourceFunctor (ℱ : DMod) : KMod ⥤ DMod :=
  CategoryTheory.Quotient.lift (homotopic (RingedSpace.Modules X) (up ℤ))
    ((((curriedTensor (RingedSpace.Modules X)).map₂CochainComplex).flip.obj
        (DerivedCategory.Qh.objPreimage ℱ).as) ⋙
      HomotopyCategory.quotient (RingedSpace.Modules X) (up ℤ))
    (fun _ _ _ _ ⟨h⟩ ↦
      HomotopyCategory.eq_of_homotopy _ _
        (HomologicalComplex.mapBifunctorMapHomotopy₁ h
          (𝟙 (DerivedCategory.Qh.objPreimage ℱ).as)
          (curriedTensor (RingedSpace.Modules X)) (up ℤ))) ⋙
    Qh

-- Proof sketch: choose a homotopy-category representative of `\mathcal F^\bullet`, replace it by
-- a K-flat resolution using the flat-resolution results developed above, and use the
-- quasi-isomorphism invariance of tensoring with a K-flat complex to invoke the universal
-- property of the total left derived functor.
/-- Tensoring on the homotopy category with a fixed derived right factor admits a total left
derived functor on `D(\mathcal O_X)`. -/
private theorem derivedTensorSourceFunctor_hasLeftDerivedFunctor
    (ℱ : DMod) :
    (derivedTensorSourceFunctor ℱ).HasLeftDerivedFunctor Qis := sorry

/-- Definition 20.26.14: for an object `\mathcal F^\bullet` of `D(\mathcal O_X)`, the derived
tensor product `- \otimes_{\mathcal O_X}^{\mathbf L} \mathcal F^\bullet` is the endofunctor of
`D(\mathcal O_X)` obtained by left deriving the homotopy-category tensor functor with fixed right
factor a chosen representative of `\mathcal F^\bullet`. -/
noncomputable def derivedTensorProduct (ℱ : DMod) : DMod ⥤ DMod :=
  letI := derivedTensorSourceFunctor_hasLeftDerivedFunctor ℱ
  (derivedTensorSourceFunctor ℱ).totalLeftDerived Qh Qis

-- Proof sketch: the homotopy-category tensor functor with fixed right factor commutes with
-- shifts by Remark `13.10.9`, and the same compatibility is inherited by the total left derived
-- functor on the derived category.
/-- Derived tensoring with a fixed right factor commutes with the triangulated shift. -/
noncomputable instance derivedTensorProduct_commShift (ℱ : DMod) :
    (derivedTensorProduct ℱ).CommShift ℤ := sorry

-- Proof sketch: the underived tensor functor on the homotopy category is triangulated by the
-- preceding homotopy-category tensor formalism, and passing to its total left derived functor
-- yields an exact functor on the derived category.
/-- The derived tensor product endofunctor on `D(\mathcal O_X)` is exact in the triangulated
sense. -/
theorem derivedTensorProduct_isTriangulated (ℱ : DMod) :
    (derivedTensorProduct ℱ).IsTriangulated := sorry

end AlgebraicGeometry.RingedSpace

namespace RingedSpaceDerivedTensor

/- Textbook surface notation for the derived tensor product object `K ⊗^L L` in
`D(\mathcal O_X)`. -/
scoped notation:70 K:70 " ⊗^L " L:71 =>
  Functor.obj (AlgebraicGeometry.RingedSpace.derivedTensorProduct L) K

end RingedSpaceDerivedTensor
