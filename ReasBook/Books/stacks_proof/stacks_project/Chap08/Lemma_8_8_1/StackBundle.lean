import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.HomSheaf

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

set_option backward.isDefEq.respectTransparency false in
/-- Bundle the descent-completion projection as a stack over the site without using
`StackOver.ofProjection`.  The direct constructor keeps the mixed object/Hom universes of the
descent-completion category instead of forcing them to be equal. -/
noncomputable def projectionStackOverOfIsStackOnSite
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    (hStack :
      letI := category (J := J) hSheaf
      IsStackOnSite J (projectionFunctor (J := J) hSheaf)) :
    StackOver.{u, v, max (max (max vX uX) v) u, max (max u v) vX} J := by
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  letI : IsStackOnSite J P := hStack
  exact
    ⟨FibredCategoryOver.ofFunctor P, by
      simpa [FibredCategoryOver.p, FibredCategoryOver.ofFunctor, P] using hStack⟩

/-- Once source stages 3.12 and 3.13 are supplied, the descent-completion projection bundles as
a mixed-universe `StackOver J`. -/
noncomputable def projectionStackOverOfHomSheafEffective
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    (hHom : projectionFunctorHomPresheavesAreSheaves (J := J) hSheaf)
    (hEff : projectionFunctorCoverwiseDescentEffective (J := J) hSheaf) :
    StackOver.{u, v, max (max (max vX uX) v) u, max (max u v) vX} J :=
  projectionStackOverOfIsStackOnSite (J := J) hSheaf
    (projectionFunctor_isStackOnSite_of_homSheaf_effective (J := J) hSheaf hHom hEff)

end DescentCompletionObject
end FibredCategoryMor

end CategoryTheory
