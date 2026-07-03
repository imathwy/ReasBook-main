import Mathlib
import StacksProject_2024.Chap13.Lemma_13_35_1
import StacksProject_2024.Chap13.Definition_13_40_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open CategoryTheory.Limits
open scoped CategoryTheory.ObjectProperty.ExtensionProductNotation

universe v u

namespace CategoryTheory.ObjectProperty

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable (A : ObjectProperty D) [A.IsTriangulated]

/- Domain-style sampling for Lemma 13.40.7:
- primary domain: admissibility and semi-orthogonal decompositions of triangulated subcategories;
- sampled core/canonical declarations:
  `Functor.rightAdjointObjIsDefined`,
  `Functor.isLeftAdjoint_iff_rightAdjointObjIsDefined_eq_top`,
  `ObjectProperty.extensionProduct`,
  `ObjectProperty.rightOrthogonal`;
- best owner abstraction: the inclusion functor owner `A.ι.rightAdjointObjIsDefined`, whose
  equality with `⊤` is the canonical adjoint-existence criterion for `A.ι`;
- primitive data: the triangulated object property `A` and its inclusion functor `A.ι`;
- derived API: the source-facing extension-product description `A ⋆ A^⊥ = ⊤`, retract stability,
  and the orthogonal-equality corollary under strict fullness;
- source/core/bridge triage:
  `source-facing`: the semi-orthogonal decomposition criterion `A ⋆ A^⊥ = ⊤`;
  `core/canonical`: `A.ι.rightAdjointObjIsDefined` together with
    `Functor.isLeftAdjoint_iff_rightAdjointObjIsDefined_eq_top`;
  `bridge/view`: the identification of `A.ι.rightAdjointObjIsDefined` with
    `A ⋆ A^⊥`.

Primitive data should stay with the inclusion-functor owner. The extension-product condition is a
source-facing bridge theorem, not a second owner for adjointability. -/

-- Proof sketch: for `X : D`, the representability criterion defining
-- `A.ι.rightAdjointObjIsDefined X` is equivalent to the existence of a distinguished triangle
-- `A' ⟶ X ⟶ B ⟶ A'⟦1⟧` with `A A'` and `A^⊥ B`, via Lemma `13.40.2` applied to the universal map
-- representing `Hom_D(A.ι.obj -, X)`.
/-- Bridge theorem for Lemma 13.40.7: the canonical partial-right-adjoint domain of the inclusion
`A.ι` is exactly the extension product `A ⋆ A^⊥`. -/
theorem rightAdjointObjIsDefined_eq_extensionProduct_rightOrthogonal :
    A.ι.rightAdjointObjIsDefined = A ⋆ A^⊥ := by
  sorry

-- Proof sketch: for `(→)`, let `v` be a chosen right adjoint to the inclusion `A.ι`; for each
-- `X`, complete the counit map `A.ι.obj ((Functor.leftAdjoint A.ι).obj X) ⟶ X` to a distinguished
-- triangle and use Lemma `13.40.2` to identify the cone with an object of `A^⊥`.
-- For `(←)`, use the chosen distinguished triangle for each `X` to define the object part of a
-- right adjoint and use the same bijectivity criterion from Lemma `13.40.2` to define the action
-- on morphisms and prove the adjunction.
/-- Lemma 13.40.7: for a triangulated subcategory `A` of a pretriangulated category `D`, the
inclusion functor `A.ι : A.FullSubcategory ⥤ D` has a right adjoint if and only if every object of
`D` belongs to the extension product of `A` with its right orthogonal `A^⊥`. -/
theorem isLeftAdjoint_iff_extensionProduct_rightOrthogonal_eq_top :
    A.ι.IsLeftAdjoint ↔ A ⋆ A^⊥ = ⊤ := by
  simpa [A.rightAdjointObjIsDefined_eq_extensionProduct_rightOrthogonal] using
    A.ι.isLeftAdjoint_iff_rightAdjointObjIsDefined_eq_top

end

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
variable (A : ObjectProperty D) [A.IsTriangulated]

-- Proof sketch: by the main equivalence, the hypothesis gives `A ⋆ A^⊥ = ⊤`. Lemma `13.40.5`
-- shows this extension product is triangulated, and Lemma
-- `13.40.4` shows `A^⊥` is stable under retracts; then the textbook argument implies
-- that `A` itself is stable under retracts.
/-- If the inclusion of `A` into `D` admits a right adjoint, then `A` is saturated, i.e. stable
under retracts. -/
theorem isStableUnderRetracts_of_inclusion_isLeftAdjoint
    (hA : A.ι.IsLeftAdjoint) :
    A.IsStableUnderRetracts := sorry

-- Proof sketch: use the main equivalence to obtain, for each `X`, a distinguished triangle
-- `A' ⟶ X ⟶ B ⟶ A'⟦1⟧` with `A A'` and `A^⊥ B`. If `X` lies in the left orthogonal
-- of `A^⊥`, then the map `X ⟶ B` is zero, so Lemma `13.4.11` splits the triangle and
-- saturation from `hA` gives strict fullness of `A`, forcing `X` to lie in `A`. The reverse
-- inclusion is immediate from the
-- definition of the right orthogonal.
/-- If the inclusion of `A` into `D` has a right adjoint, then `A` equals the left orthogonal of
its right orthogonal. -/
theorem eq_rightOrthogonal_leftOrthogonal_of_inclusion_isLeftAdjoint
    (hA : A.ι.IsLeftAdjoint) :
    A = ^⊥(A^⊥) := sorry

end

end CategoryTheory.ObjectProperty
