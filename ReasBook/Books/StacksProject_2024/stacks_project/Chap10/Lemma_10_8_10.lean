import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import StacksProject_2024.Chap04.Lemma_4_19_8

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits

universe u v

noncomputable section

section

variable {I : Type u} [Category.{v} I] [Small.{v} I]
variable [HasSpanCocones I]

-- Proof sketch: the source statement is about abelian groups, whose owner category in mathlib is
-- `AddCommGrpCat`. By `hasExactColimitsOfShape_of_preservesMono`, it is enough to show that
-- `colim : (I ⥤ AddCommGrpCat) ⥤ AddCommGrpCat` preserves monomorphisms. Decompose `I` into
-- connected components using Lemma `4.19.8`, each of which is filtered, apply filtered exactness
-- in `AddCommGrpCat` componentwise, and reassemble the result using exactness of coproducts.

/-- Lemma 10.8.10: if the index category `I` satisfies the hypotheses of Categories, Lemma 4.19.8,
then taking colimits of diagrams of abelian groups over `I` is exact. The owner abstraction is the
instance `HasExactColimitsOfShape I AddCommGrpCat`. -/
instance abelian_group_colimits_exact
    (hMap : ∀ ⦃X Y : I⦄ (f g : X ⟶ Y), ∃ (Z : I) (h : Y ⟶ Z), f ≫ h = g ≫ h) :
    HasExactColimitsOfShape I AddCommGrpCat := by
  letI : Functor.PreservesMonomorphisms (colim : (I ⥤ AddCommGrpCat) ⥤ AddCommGrpCat) := by
    sorry
  exact hasExactColimitsOfShape_of_preservesMono AddCommGrpCat I

end
