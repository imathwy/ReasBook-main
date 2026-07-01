import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import stacks_project.Chap13.Remark_13_10_9
import stacks_project.Chap15.Lemma_15_58_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open ComplexShape
open CategoryTheory.MonoidalCategory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "KMod" => HomotopyCategory (ModuleCat R) (up ℤ)
local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "Qh" => (DerivedCategory.Qh : KMod ⥤ DMod)
local notation "Qis" => HomotopyCategory.quasiIso (ModuleCat R) (up ℤ)

/-- The homotopy-category functor whose total left derived functor defines tensoring with a fixed
derived object of `D(R)`. -/
private noncomputable abbrev derivedTensorSourceFunctor (M : DMod) : KMod ⥤ DMod :=
  tensorRight (DerivedCategory.Qh.objPreimage M) ⋙ Qh

-- Proof sketch: choose a representative complex of `M` in `K(R)`, replace it by a K-flat
-- resolution using the preceding K-flat theory, and use quasi-isomorphism invariance of tensoring
-- with a K-flat complex to invoke the universal property of the total left derived functor.
/-- Totalized tensoring with a chosen representative of a derived `R`-complex admits a total left
derived functor on `D(R)`. -/
private theorem derivedTensorSourceFunctor_hasLeftDerivedFunctor
    (M : DMod) :
    (derivedTensorSourceFunctor M).HasLeftDerivedFunctor Qis := sorry

/-- Definition 15.59.13: for an object `M^•` of `D(R)`, the derived tensor product
`- \otimes_R^{\mathbf L} M^•` is the endofunctor of `D(R)` obtained by left deriving totalized
tensoring with a chosen representative of `M^•` in `K(R)`. -/
noncomputable def derivedTensorProduct (M : DMod) : DMod ⥤ DMod :=
  letI := derivedTensorSourceFunctor_hasLeftDerivedFunctor M
  (derivedTensorSourceFunctor M).totalLeftDerived Qh Qis

-- Proof sketch: the homotopy-category tensor functor with fixed right factor commutes with shifts,
-- and the same compatibility is inherited by the total left derived functor on the derived
-- category.
/-- The derived tensor product functor commutes with the triangulated shift. -/
noncomputable instance derivedTensorProduct_commShift (M : DMod) :
    (derivedTensorProduct M).CommShift ℤ := sorry

-- Proof sketch: the underived tensor functor on `K(R)` with fixed right factor is triangulated by
-- Lemma `15.58.4`; passing to its total left derived functor yields an exact functor on `D(R)`.
/-- The derived tensor product functor is exact in the triangulated sense. -/
theorem derivedTensorProduct_isTriangulated (M : DMod) :
    (derivedTensorProduct M).IsTriangulated := sorry

end

end CategoryTheory

namespace DerivedTensorProduct

/- Textbook notation for the derived tensor product object `K ⊗[R]^L L` in `D(R)`. -/
scoped notation:70 K:70 " ⊗[" R:70 "]^L " L:71 =>
  Functor.obj (@CategoryTheory.derivedTensorProduct R _ L) K

end DerivedTensorProduct
