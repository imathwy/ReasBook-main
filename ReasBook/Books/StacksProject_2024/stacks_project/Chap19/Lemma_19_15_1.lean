import Mathlib
import StacksProject_2024.Chap13.Lemma_13_38_1
import StacksProject_2024.Chap19.Lemma_19_13_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe v u

namespace CategoryTheory.IsGrothendieckAbelian

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{max u v} A]

/-- The standard derived-category model attached to a Grothendieck abelian category in this item
file. -/
local instance grothendieckAbelian_hasDerivedCategoryForLemma_19_15_1 :
    HasDerivedCategory.{max u v} A :=
  HasDerivedCategory.standard A

/-
Domain-style sampling:
- primary domain: Brown representability for contravariant cohomological functors on triangulated
  categories with direct sums, specialized here to derived categories of Grothendieck abelian
  categories;
- sampled owner declarations:
  `brown_representability`,
  `derivedCategory_hasCoproductsOfShape`,
  `HasDerivedCategory.standard`,
  `Functor.IsHomological`,
  `preadditiveYoneda`;
- best owner abstraction: the Chapter 13 owner theorem `brown_representability`, specialized to
  `DerivedCategory A`;
- primitive data: the Grothendieck abelian category `A`, the contravariant functor `H`, its
  homologicality, and its preservation of products indexed by arbitrary direct sums;
- derived API: the representing object conclusion
  `∃ X : DerivedCategory A, Nonempty (preadditiveYoneda.obj X ≅ H)`, together with the ambient
  coproduct and compact-generation bridges on `DerivedCategory A`.

Source/core/bridge triage:
- `source-facing`: `derivedCategory_brownRepresentability`;
- `core/canonical`: `brown_representability`;
- `bridge/view`: `derivedCategory_hasCoproducts` and `derivedCategory_isCompactlyGenerated`,
  which specialize the Chapter `13` owner to the derived category of a Grothendieck abelian
  category. -/

/-- A Grothendieck abelian category has arbitrary direct sums in its derived category. -/
local instance derivedCategory_hasCoproducts : HasCoproducts.{max u v} (DerivedCategory A) :=
  fun _ ↦ CategoryTheory.derivedCategory_hasCoproductsOfShape

/-- A Grothendieck abelian category has compactly generated derived category. -/
theorem derivedCategory_isCompactlyGenerated :
    IsCompactlyGenerated (DerivedCategory A) := by
  -- Route correction: the naive Gabriel-Popescu image of `R[0]` is the right weak-generator
  -- candidate from the source proof, but compact generation needs a separate quotient/localization
  -- bridge rather than a direct compactness proof for that image.
  -- Proof comment: the ambient compact-generation theorem is already packaged as a typeclass
  -- instance for derived categories of Grothendieck abelian categories.
  infer_instance

-- Proof sketch: Chapter `19` supplies the standard derived-category model, the coproduct owner
-- `derivedCategory_hasCoproductsOfShape`, and the compact-generation bridge
-- `derivedCategory_isCompactlyGenerated`. With those ambient owners in place, Lemma `13.38.1`
-- applies directly to `DerivedCategory A`.
/-- Lemma 19.15.1: if `A` is Grothendieck abelian, then every contravariant cohomological functor
on `D(A)` that sends direct sums to products is representable. -/
theorem derivedCategory_brownRepresentability
    (H : (DerivedCategory A)ᵒᵖ ⥤ AddCommGrpCat.{max u v})
    (hH : H.rightOp.IsHomological)
    (hprod : ∀ J : Type (max u v), PreservesLimitsOfShape (Discrete J) H) :
    ∃ X : DerivedCategory A, Nonempty (preadditiveYoneda.obj X ≅ H) := by
  exact brown_representability H derivedCategory_isCompactlyGenerated hH hprod

end CategoryTheory.IsGrothendieckAbelian
