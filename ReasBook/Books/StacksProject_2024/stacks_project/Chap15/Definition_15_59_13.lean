import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Homology.BifunctorHomotopy
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.Localization
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Localization.Monoidal.Braided
import Mathlib.CategoryTheory.Monoidal.Preadditive
import StacksProject_2024.Chap13.Remark_13_10_9
import StacksProject_2024.Chap15.Lemma_15_58_3_Internal

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open MonoidalCategory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "Mod" => ModuleCat R
local notation "Cpx" => CochainComplex Mod ℤ
local notation "KMod" => HomotopyCategory Mod (up ℤ)
local notation "DMod" => DerivedCategory Mod
local notation "Qh" => (DerivedCategory.Qh : KMod ⥤ DMod)
local notation "Qis" => HomotopyCategory.quasiIso Mod (up ℤ)

local instance : MonoidalCategory KMod :=
  homotopyCategory_monoidalCategory

/- Domain-style sampling for Definition 15.59.13:
- primary domain: derived tensor products in the unbounded derived category `D(R)`;
- sampled owner declarations:
  `MonoidalCategory.tensorRight`,
  `Functor.totalLeftDerived`,
  `HomotopyCategory.quasiIso`,
  `DerivedCategory.Qh`;
- best owner abstraction: the public owner is the functor-level derived tensor product
  `derivedTensorProduct M`, while the chosen homotopy-category representative of `M` stays
  auxiliary and internal to the fixed-right-factor tensor functor on `K(R)`;
- primitive vs. derived:
  primitive data are the chosen homotopy-category representative `tensorRightRepresentative M`
  and the induced homotopy-category tensor functor below;
  derived API is the total left derived functor on `D(R)` and its exactness/shift companions.
-/

noncomputable abbrev tensorRightRepresentative
    (M : DMod) :
    KMod :=
  (HomotopyCategory.quotient Mod (up ℤ)).obj
    ((DerivedCategory.Q : Cpx ⥤ DMod).objPreimage M)

noncomputable def tensorRightRepresentativeIso
    (M : DMod) :
    ((Qh).obj (tensorRightRepresentative M)) ≅ M :=
  (DerivedCategory.quotientCompQhIso Mod).app
      ((DerivedCategory.Q : Cpx ⥤ DMod).objPreimage M) ≪≫
    ((DerivedCategory.Q : Cpx ⥤ DMod).objObjPreimageIso M)

private noncomputable abbrev tensorRightFunctor
    (M : DMod) :
    KMod ⥤ KMod :=
  MonoidalCategory.tensorRight (tensorRightRepresentative M)

-- Proof sketch: choose a representative complex of `M` in `K(R)`, replace it by a K-flat
-- resolution using the preceding K-flat theory, and use quasi-isomorphism invariance of tensoring
-- with a K-flat complex to invoke the universal property of the total left derived functor.
/-- Totalized tensoring with a chosen representative of a derived `R`-complex admits a total left
derived functor on `D(R)`. -/
theorem tensorRightCompQh_hasLeftDerivedFunctor
    (M : DMod) :
    (tensorRightFunctor M ⋙ Qh).HasLeftDerivedFunctor Qis := by
  sorry

/-- Definition 15.59.13: for an object `M^•` of `D(R)`, the derived tensor product
`- \otimes_R^{\mathbf L} M^•` is the endofunctor of `D(R)` obtained by left deriving totalized
tensoring with a chosen representative of `M^•` in `K(R)`. -/
noncomputable def derivedTensorProduct
    (M : DMod) :
    DMod ⥤ DMod :=
  let F : KMod ⥤ DMod := tensorRightFunctor M ⋙ Qh
  letI : F.HasLeftDerivedFunctor Qis := tensorRightCompQh_hasLeftDerivedFunctor M
  F.totalLeftDerived Qh Qis

-- Proof sketch: the homotopy-category tensor functor with fixed right factor commutes with shifts,
-- and the same compatibility is inherited by the total left derived functor on the derived
-- category.
/-- The derived tensor product functor commutes with the triangulated shift. -/
noncomputable instance derivedTensorProduct_commShift
    (M : DMod) :
    (derivedTensorProduct M).CommShift ℤ := by
  sorry

-- Proof sketch: the underived tensor functor on `K(R)` with fixed right factor is triangulated by
-- Lemma `15.58.4`; passing to its total left derived functor yields an exact functor on `D(R)`.
/-- The derived tensor product functor is exact in the triangulated sense. -/
theorem derivedTensorProduct_isTriangulated
    (M : DMod) :
    (derivedTensorProduct M).IsTriangulated := by
  sorry

end

end CategoryTheory

namespace DerivedTensorProduct

/- Textbook notation for the derived tensor product object `K ⊗[R]^L L` in `D(R)`. -/
set_option quotPrecheck false in
scoped notation:70 K:70 " ⊗[" R:70 "]^L " L:71 =>
  (@CategoryTheory.derivedTensorProduct R _ L).obj K

end DerivedTensorProduct
