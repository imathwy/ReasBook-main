import Mathlib
import StacksProject_2024.Chap12.Definition_12_10_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty

universe u v w

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Remark 19.9.4, source-facing witness: a set-sized abelian full subcategory of `A`
containing the chosen set-sized family of objects. The original remark asks for this kind of full
abelian subcategory; it does not assert closure under the ambient weak Serre-class operations. -/
structure SmallAbelianFullSubcategoryContaining (E : ObjectProperty A) where
  carrier : ObjectProperty A
  contains : E ≤ carrier
  small : ObjectProperty.Small.{w} carrier
  abelian : Abelian carrier.FullSubcategory

/-- Remark 19.9.4: for any set-sized family of objects in an abelian category, there is an
abelian full subcategory whose objects form a set and which contains that family. This is the form
used to reduce diagram-chase statements in a large abelian category to the small case. -/
theorem exists_small_abelian_fullSubcategory_containing
    (E : ObjectProperty A) [ObjectProperty.Small.{w} E] :
    Nonempty (SmallAbelianFullSubcategoryContaining.{u, v, w} (A := A) E) := by
  sorry

end CategoryTheory
