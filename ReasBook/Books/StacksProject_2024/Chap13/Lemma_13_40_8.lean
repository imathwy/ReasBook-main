import Mathlib
import StacksProject_2024.Chap13.Lemma_13_35_1
import StacksProject_2024.Chap13.Definition_13_40_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Pretriangulated
open CategoryTheory.Limits
open scoped CategoryTheory.ObjectProperty.ExtensionProductNotation

universe v u

namespace CategoryTheory.ObjectProperty

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable (A : ObjectProperty D) [A.IsTriangulated]

/-
Domain-style sampling for Lemma 13.40.8:
- primary domain: admissibility and semi-orthogonal decompositions of triangulated subcategories;
- sampled core/canonical declarations:
  `Functor.leftAdjointObjIsDefined`,
  `Functor.isRightAdjoint_iff_leftAdjointObjIsDefined_eq_top`,
  `ObjectProperty.extensionProduct`;
- best owner abstraction: the inclusion functor owner `A.ι.leftAdjointObjIsDefined`, whose
  equality with `⊤` is the canonical adjoint-existence criterion for `A.ι`;
- primitive data: the triangulated object property `A` and its inclusion functor `A.ι`;
- derived API: in this weaker section, the source-facing extension-product description
  `(^⊥A) ⋆ A = ⊤`; the later stronger section adds retract stability and the
  orthogonal-equality corollary under strict fullness;
- source/core/bridge triage:
  `source-facing`: the semi-orthogonal decomposition criterion `(^⊥A) ⋆ A = ⊤`;
  `core/canonical`: `A.ι.leftAdjointObjIsDefined` together with
    `Functor.isRightAdjoint_iff_leftAdjointObjIsDefined_eq_top`;
  `bridge/view`: the identification of `A.ι.leftAdjointObjIsDefined` with
    `(^⊥A) ⋆ A`.

Primitive data should stay with the inclusion-functor owner. The extension-product condition is a
source-facing bridge theorem, not a second owner for adjointability. -/

-- Proof sketch: for `X : D`, the corepresentability criterion defining
-- `A.ι.leftAdjointObjIsDefined X` is equivalent to the existence of a distinguished triangle
-- `B ⟶ X ⟶ A' ⟶ B⟦1⟧` with `^⊥A B` and `A A'`, via Lemma `13.40.3` applied to the universal map
-- corepresenting `Hom_D(X, A.ι.obj -)`.
/-- Bridge theorem for Lemma 13.40.8: the canonical partial-left-adjoint domain of the inclusion
`A.ι` is exactly the extension product `(^⊥A) ⋆ A`. -/
theorem leftAdjointObjIsDefined_eq_leftOrthogonal_extensionProduct :
    A.ι.leftAdjointObjIsDefined = (^⊥A) ⋆ A := by
  sorry

-- Proof sketch: this is dual to Lemma `13.40.7`. For `(→)`, let `u` be a chosen left adjoint to
-- the inclusion `A.ι`; for each `X`, complete the unit map `X ⟶ A.ι.obj ((Functor.rightAdjoint
-- A.ι).obj X)` to a distinguished triangle and use Lemma `13.40.3` to identify the first term
-- with an object of `^⊥A`. For `(←)`, choose such a triangle for each `X` and use
-- the bijectivity criterion of Lemma `13.40.3` to define the object and morphism parts of a left
-- adjoint to the inclusion.
/-- Lemma 13.40.8: for a triangulated subcategory `A` of a pretriangulated category `D`, the
inclusion functor `A.ι : A.FullSubcategory ⥤ D` is a right adjoint, equivalently admits a left
adjoint, if and only if every object of `D` belongs to the extension product of its left
orthogonal `^⊥A` with `A`. -/
theorem isRightAdjoint_iff_leftOrthogonal_extensionProduct_eq_top :
    A.ι.IsRightAdjoint ↔ (^⊥A) ⋆ A = ⊤ := by
  simpa [A.leftAdjointObjIsDefined_eq_leftOrthogonal_extensionProduct] using
    A.ι.isRightAdjoint_iff_leftAdjointObjIsDefined_eq_top

end

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
variable (A : ObjectProperty D) [A.IsTriangulated]

-- Proof sketch: by the main equivalence, the hypothesis gives `(^⊥A) ⋆ A = ⊤`. Lemma `13.40.6`
-- shows this extension product is triangulated, and Lemma `13.40.4`
-- shows `^⊥A` is stable under retracts; then the textbook argument implies that `A`
-- itself is stable under retracts.
/-- If the inclusion of `A` into `D` admits a left adjoint, then `A` is saturated, i.e. stable
under retracts. -/
theorem isStableUnderRetracts_of_inclusion_isRightAdjoint
    (hA : A.ι.IsRightAdjoint) :
    A.IsStableUnderRetracts := sorry

-- Proof sketch: use the main equivalence to obtain, for each `X`, a distinguished triangle
-- `B ⟶ X ⟶ A' ⟶ B⟦1⟧` with `^⊥A B` and `A A'`. If `X` lies in the right orthogonal
-- of `^⊥A`, then the map `B ⟶ X` is zero, so Lemma `13.4.11` splits the triangle and
-- `A.isStableUnderRetracts_of_inclusion_isRightAdjoint hA` gives strict fullness of `A`,
-- forcing `X` to lie in `A`. The reverse inclusion is immediate from the definition of the left
-- orthogonal.
/-- If the inclusion of `A` into `D` has a left adjoint, then `A` equals the right orthogonal of
its left orthogonal. -/
theorem eq_leftOrthogonal_rightOrthogonal_of_inclusion_isRightAdjoint
    (hA : A.ι.IsRightAdjoint) :
    A = (^⊥A)^⊥ := sorry

end

end CategoryTheory.ObjectProperty
