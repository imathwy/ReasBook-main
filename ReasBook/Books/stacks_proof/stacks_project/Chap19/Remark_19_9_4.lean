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
@[stacks 05PQ]
structure SmallAbelianFullSubcategoryContaining (E : ObjectProperty A) where
  carrier : ObjectProperty A
  contains : E ≤ carrier
  small : ObjectProperty.Small.{w} carrier
  abelian : Abelian carrier.FullSubcategory

/-- Helper for Chap19 Remark 19 9 4: if the ambient abelian category is already `w`-small, then
the ambient object property `⊤` itself gives the required small abelian full subcategory
containing `E`. -/
lemma exists_small_abelian_fullSubcategory_containing_of_smallAmbient
    (E : ObjectProperty A) [ObjectProperty.Small.{w} E] [Small.{w} A] :
    Nonempty (SmallAbelianFullSubcategoryContaining.{u, v, w} (A := A) E) := by
  -- Proof comment: when `A` is already `w`-small, the full subcategory on all objects stays
  -- `w`-small and inherits the ambient abelian structure.
  have hContains : E ≤ (⊤ : ObjectProperty A) := by
    intro X hX
    trivial
  have hSmallTop : ObjectProperty.Small.{w} (⊤ : ObjectProperty A) := by
    let f : A → Subtype (⊤ : ObjectProperty A) := fun X ↦ ⟨X, trivial⟩
    have hf : Function.Surjective f := by
      rintro ⟨X, hX⟩
      exact ⟨X, rfl⟩
    exact small_of_surjective hf
  have hAbelianTop : Abelian (⊤ : ObjectProperty A).FullSubcategory := by
    letI : (⊤ : ObjectProperty A).ContainsZero := inferInstance
    letI : (⊤ : ObjectProperty A).IsClosedUnderKernels := inferInstance
    letI : (⊤ : ObjectProperty A).IsClosedUnderCokernels := inferInstance
    letI : (⊤ : ObjectProperty A).IsClosedUnderFiniteProducts := by
      exact ObjectProperty.IsClosedUnderFiniteProducts.mk' (P := (⊤ : ObjectProperty A))
    infer_instance
  let witness : SmallAbelianFullSubcategoryContaining.{u, v, w} (A := A) E :=
    { carrier := ⊤
      contains := hContains
      small := hSmallTop
      abelian := hAbelianTop }
  exact ⟨witness⟩

/-- Remark 19.9.4: for any set-sized family of objects in an abelian category, there is an
abelian full subcategory whose objects form a set and which contains that family. This is the form
used to reduce diagram-chase statements in a large abelian category to the small case. -/
@[stacks 05PQ]
theorem exists_small_abelian_fullSubcategory_containing
    (E : ObjectProperty A) [ObjectProperty.Small.{w} E] :
    Nonempty (SmallAbelianFullSubcategoryContaining.{u, v, w} (A := A) E) := by
  -- Route correction: the earlier weak-Serre-closure plan is not the real blocker. The issue is
  -- already visible at the universe level: to close a `w`-small family under kernels and
  -- cokernels, one must range over all morphisms between its objects, and those hom-types need
  -- not be `w`-small.
  -- TODO: as stated, this theorem needs either an added hypothesis such as `LocallySmall.{w} A`
  -- (or a stronger ambient `w`-smallness assumption) or a weaker conclusion allowing the witness
  -- carrier to live in a larger universe than `w`.
  sorry

end CategoryTheory
