import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.StackBundle

universe u v uX vX

namespace CategoryTheory

open Bicategory
open FibredCategoryMor
open Functor
open Opposite
open scoped CategoryTheory.Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

attribute [local instance] Types.instFunLike Types.instConcreteCategory

namespace FibredCategoryMor
namespace DescentCompletionObject

/-- Helper for Chap08 Lemma 8 8 1: the mixed owner of the descent-completion stack.  This records
the universe growth of the source construction instead of forcing the descent-completion category
into the original owner. -/
abbrev stackOwner :=
  StackOver.{u, v, max (max (max vX uX) v) u, max (max u v) vX} J

/-- Helper for Chap08 Lemma 8 8 1: the source-facing third-stage frontier.  The first field is the
input assumption used to define composition of descent-completion morphisms, while the last two
fields are exactly the omitted source checks 3.12 and 3.13: Hom presheaves of the completed
projection are sheaves, and descent data for the completed projection are effective. -/
structure Stage3Frontier (X : FibredCategoryOver.{u, v, uX, vX} C) where
  /-- Hom presheaves in the pre-completion category are sheaves, so the descent-completion
  morphism composition is defined by sheaf gluing. -/
  homSheaves :
    DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X
  /-- Source stage 3.12: Hom presheaves of the descent-completion projection are sheaves. -/
  projectionHomSheaves :
    projectionFunctorHomPresheavesAreSheaves (J := J) homSheaves
  /-- Source stage 3.13: descent data for the descent-completion projection are effective. -/
  projectionDescentEffective :
    projectionFunctorCoverwiseDescentEffective (J := J) homSheaves

namespace Stage3Frontier

/-- Helper for Chap08 Lemma 8 8 1: a completed third-stage frontier bundles the
descent-completion projection as a mixed-universe stack over the site. -/
noncomputable def stack {X : FibredCategoryOver.{u, v, uX, vX} C}
    (S : Stage3Frontier (J := J) X) :
    stackOwner.{u, v, uX, vX} (J := J) :=
  projectionStackOverOfHomSheafEffective (J := J)
    S.homSheaves S.projectionHomSheaves S.projectionDescentEffective

/-- Helper for Chap08 Lemma 8 8 1: the projection attached to a completed third-stage frontier is a
stack on the site. -/
theorem projectionFunctor_isStackOnSite
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (S : Stage3Frontier (J := J) X) :
    letI := DescentCompletionObject.category (J := J) S.homSheaves
    IsStackOnSite J (projectionFunctor (J := J) S.homSheaves) :=
  projectionFunctor_isStackOnSite_of_homSheaf_effective (J := J)
    S.homSheaves S.projectionHomSheaves S.projectionDescentEffective

end Stage3Frontier
end DescentCompletionObject
end FibredCategoryMor

end CategoryTheory
