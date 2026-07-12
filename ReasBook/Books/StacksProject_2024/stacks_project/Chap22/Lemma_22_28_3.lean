import Mathlib.Algebra.Homology.Additive
import Mathlib.Tactic.Recall

open CategoryTheory
open CategoryTheory.Limits

section

universe v u

variable {DGBimodAB DGRightTensorModule : Type u}
variable [Category.{v} DGBimodAB] [HasZeroMorphisms DGBimodAB]
variable [Category.{v} DGRightTensorModule] [HasZeroMorphisms DGRightTensorModule]
variable (e : DGBimodAB ≌ DGRightTensorModule)

/-
Lemma 22.28.3: in the cochain-complex model for differential graded module categories, an
equivalence between the underlying ordinary `(A, B)`-bimodule category and the ordinary right
`A^{opp} ⊗_R B`-module category induces the corresponding equivalence between differential graded
`(A, B)`-bimodules and right differential graded `A^{opp} ⊗_R B`-modules by lifting along
`CategoryTheory.Equivalence.mapHomologicalComplex`. This item is recall-only: the canonical owner
is the generic homological-complex lift of an equivalence, and the source-facing specialization is
the cochain-complex case. -/
recall CategoryTheory.Equivalence.mapHomologicalComplex

set_option linter.hashCommand false in
#check (e.mapHomologicalComplex (ComplexShape.up ℤ) :
  CochainComplex DGBimodAB ℤ ≌ CochainComplex DGRightTensorModule ℤ)

end
