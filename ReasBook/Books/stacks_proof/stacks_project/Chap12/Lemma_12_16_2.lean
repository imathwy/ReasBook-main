import Mathlib.CategoryTheory.Abelian.Transfer
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.GradedObject
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

universe w v u

namespace CategoryTheory

/- Lemma 12.16.2 is a `bridge/view` item in the category-theoretic domain of graded objects and
functor categories. The source-facing owner object is `GradedObject β C`, while the canonical core
owner of the abelian structure is the functor category `Discrete β ⥤ C` via
`piEquivalenceFunctorDiscrete β C` together with the owner instance
`FunctorCategory.functorCategoryAbelian`. There is no extra primitive data here: the
`Preadditive` and finite-product structures on graded objects are only internal support transported
across this equivalence, and the abelian structure is then the canonical transfer via
`abelianOfEquivalence`. -/

/-- Lemma 12.16.2: if `C` is an abelian category, then the category of `β`-graded objects in `C`
is abelian. -/
@[stacks 0126]
noncomputable instance (β : Type w) (C : Type u) [Category.{v} C] [Abelian C] :
    Abelian (GradedObject β C) := by
  let E := piEquivalenceFunctorDiscrete β C
  letI : Preadditive (GradedObject β C) := Preadditive.ofFullyFaithful E.fullyFaithfulFunctor
  letI : HasFiniteProducts (GradedObject β C) :=
    ⟨fun _ ↦ Adjunction.hasLimitsOfShape_of_equivalence E.functor⟩
  exact abelianOfEquivalence E.functor

/-- Graded objects in an abelian category carry the canonical homology package induced by the
abelian structure. -/
noncomputable instance (β : Type w) (C : Type u) [Category.{v} C] [Abelian C] :
    CategoryWithHomology (GradedObject β C) := by
  have hzero : (Preadditive.preadditiveHasZeroMorphisms :
      HasZeroMorphisms (GradedObject β C)) = GradedObject.hasZeroMorphisms β :=
    HasZeroMorphisms.ext _ _
  exact hzero ▸
    @_root_.CategoryTheory.categoryWithHomology_of_abelian (GradedObject β C) _ _

end CategoryTheory
