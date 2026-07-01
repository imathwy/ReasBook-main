import Mathlib.CategoryTheory.Abelian.Opposite
import Mathlib.CategoryTheory.Abelian.Transfer
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
import Mathlib.CategoryTheory.Preadditive.Transfer
import Mathlib.Tactic.Recall
import stacks_project.Chap12.Definition_12_3_8

universe v u

namespace CategoryTheory

open Limits

variable (A : Type u) [Category.{v} A]

/-
Source/core/bridge triage for Lemma 12.5.2:
- source-facing: opposite and unop preserve the preadditive/additive/abelian structures in the
  Stacks sense
- core/canonical owners: `instPreadditiveOpposite`, `HasFiniteProducts`, and the abelian opposite
  instance from mathlib
- bridge/view: `Preadditive.ofFullyFaithful`, `hasFiniteProducts_of_opposite`, and
  `abelianOfEquivalence`
-/

section

variable [Preadditive A]

/- Lemma 12.5.2 (1): the opposite of a preadditive category is canonically preadditive. -/
recall instPreadditiveOpposite (A : Type u) [Category.{v} A] [Preadditive A] : Preadditive Aᵒᵖ

/-
Lemma 12.5.2 (1): if `A` is additive, then `Aᵒᵖ` is additive. In the canonical owner language of
Definition 12.3.8, the remaining additive structure is the finite-product instance below.
-/
@[reducible] noncomputable def instHasFiniteProductsOpposite
    [HasFiniteProducts A] :
    HasFiniteProducts Aᵒᵖ := by
  let _ : HasFiniteBiproducts A := HasFiniteBiproducts.of_hasFiniteProducts
  let _ : HasFiniteCoproducts A := inferInstance
  infer_instance

end

section

variable [Preadditive Aᵒᵖ]

/- Lemma 12.5.2 (1): if `Aᵒᵖ` is preadditive, then `A` is canonically preadditive. -/
@[reducible] noncomputable def instPreadditiveUnop : Preadditive A :=
  Preadditive.ofFullyFaithful (Functor.FullyFaithful.ofFullyFaithful (opOp A))

/-
Lemma 12.5.2 (1): if `Aᵒᵖ` is additive, then `A` is additive. In the canonical owner language of
Definition 12.3.8, the remaining additive structure is the finite-product instance below.
-/
@[reducible] noncomputable def instHasFiniteProductsUnop
    [HasFiniteProducts Aᵒᵖ] :
    HasFiniteProducts A := by
  let _ : HasFiniteBiproducts Aᵒᵖ := HasFiniteBiproducts.of_hasFiniteProducts
  let _ : HasFiniteCoproducts Aᵒᵖ := inferInstance
  exact hasFiniteProducts_of_opposite

end

section

variable [Abelian A]

/- Lemma 12.5.2 (2): the opposite of an abelian category is canonically abelian. -/
recall instAbelianOpposite (A : Type u) [Category.{v} A] [Abelian A] : Abelian Aᵒᵖ

end

section

variable [Abelian Aᵒᵖ]

/- Lemma 12.5.2 (2): if the opposite category `Aᵒᵖ` is abelian, then `A` is abelian. -/
@[reducible] noncomputable def instAbelianUnop : Abelian A :=
  let _ : Preadditive A := instPreadditiveUnop A
  let _ : HasFiniteProducts A := instHasFiniteProductsUnop A
  let _ : Abelian Aᵒᵖᵒᵖ := instAbelianOpposite Aᵒᵖ
  abelianOfEquivalence (opOpEquivalence A).symm.functor

attribute [instance] instHasFiniteProductsOpposite
attribute [instance] instPreadditiveUnop
attribute [instance] instHasFiniteProductsUnop
attribute [instance] instAbelianUnop

end

end CategoryTheory
