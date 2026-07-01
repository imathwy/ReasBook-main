import Mathlib
import Mathlib.Tactic.Recall
import stacks_project.Chap14.Definition_14_15_1

open Opposite
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
variable (U : SSet) (V : CosimplicialObject C)
variable [∀ n : SimplexCategory, Finite (U.obj (op n))]

#check (((opOpEquivalence SimplexCategory).inverse ⋙
    homFromCosimplicialSet U ((opOpEquivalence SimplexCategory).functor ⋙ V)) :
    CosimplicialObject C)

end CategoryTheory
