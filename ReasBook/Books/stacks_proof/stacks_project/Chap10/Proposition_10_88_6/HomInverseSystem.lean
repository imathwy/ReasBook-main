import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.Data.List.TFAE
import Mathlib.Tactic.TFAE
import stacks_proof.stacks_project.Chap10.Definition_10_88_2
import stacks_proof.stacks_project.Chap10.Lemma_10_11_1
import stacks_proof.stacks_project.Chap10.Lemma_10_11_4
import stacks_proof.stacks_project.Chap10.Lemma_10_79_4
import stacks_proof.stacks_project.Chap10.Lemma_10_82_14
import stacks_proof.stacks_project.Chap10.Lemma_10_88_3
import stacks_proof.stacks_project.Chap10.Lemma_10_88_5

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped TensorProduct MonoidalCategory

universe u v w

noncomputable section

section HomInverseSystem

variable {R : Type u} [Ring R]
variable {I : Type v} [Preorder I]

/-- The inverse system `i ↦ Hom_R(M_i, N)` attached to a directed system of `R`-modules. -/
abbrev colimitPresentationHomInverseSystem
    (F : I ⥤ ModuleCat.{max v w} R) (N : ModuleCat.{max v w} R) :
    Iᵒᵖ ⥤ Type (max v w) :=
  F.op ⋙ preadditiveYoneda.obj N ⋙ forget AddCommGrpCat

end HomInverseSystem
