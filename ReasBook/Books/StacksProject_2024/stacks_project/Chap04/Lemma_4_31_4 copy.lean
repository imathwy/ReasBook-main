import Mathlib
import StacksProject_2024.stacks_project.Chap04.Definition_4_31_2
import StacksProject_2024.stacks_project.Chap04.Example_4_31_3
import StacksProject_2024.stacks_project.Chap04.Lemma_4_31_6

open CategoryTheory
open Limits
open CategoricalPullback
open CatCommSqOver
open scoped CategoricalPullback

universe u

variable {A : Type u} [SmallCategory A]
variable {B : Type u} [SmallCategory B]
variable {C : Type u} [SmallCategory C]

variable (F : A ⥤ C) (G : B ⥤ C)

namespace CategoryTheory.Limits

/-- The canonical square carried by mathlib's categorical pullback, viewed as an object of the
bicategory of `2`-commutative squares over `F` and `G` in `Cat`. -/
abbrev categoricalPullbackSquare :
    BicategoricalTwoCommutativeSquare F.toCatHom G.toCatHom :=
  ((toCatCommSqOver F G (F ⊡ G)).obj (𝟭 _)).toBicategoricalSquare

/-- Declaration for the Definition 4.31.2 universal property in `Cat`: the canonical square
attached to `CategoricalPullback F G` is final in the bicategory of squares over `F` and `G`. -/
noncomputable instance categoricalPullbackSquare_isFinal :
    Bicategory.IsFinal (categoricalPullbackSquare F G) := by sorry

end CategoryTheory.Limits
