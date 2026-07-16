import Mathlib
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
import StacksProject_2024.stacks_project.Chap12.Definition_12_18_3

open CategoryTheory Limits ComplexShape HomologicalComplex HomologicalComplex₂ Opposite
open scoped HomologicalComplex₂

noncomputable section

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

/-- The opposite of a bicomplex, viewed as a cochain complex of opposite cochain complexes. -/
abbrev productTotalCochainOp
    (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) :
    CochainComplex (CochainComplex C ℤ)ᵒᵖ ℤ :=
  (ChainComplex.cochainComplexEquivalence ((CochainComplex C ℤ)ᵒᵖ)).functor.obj K.op

/-- The opposite bicomplex whose coproduct total models the product total of `K`. -/
abbrev productTotalOpBicomplex
    (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) :
    HomologicalComplex₂ Cᵒᵖ (up ℤ) (up ℤ) :=
  (((CochainComplex.opEquivalence C).functor).mapHomologicalComplex (up ℤ)).obj
    (productTotalCochainOp K)

/-- The canonical coproduct total of the opposite bicomplex underlying the product total of `K`. -/
abbrev productTotalOp
    [HasCountableProducts C]
    (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) :
    CochainComplex Cᵒᵖ ℤ :=
  (productTotalOpBicomplex K).total (up ℤ)

/-- The product total complex of a bicomplex, defined as the unop of the canonical total of the
transported opposite bicomplex. -/
abbrev productTotal
    [HasCountableProducts C]
    (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) :
    CochainComplex C ℤ :=
  ((CochainComplex.opEquivalence C).inverse.obj (productTotalOp K)).unop

/-- Functoriality of the product total construction on cohomological bicomplexes. -/
abbrev productTotalFunctor
    [HasCountableProducts C] :
    HomologicalComplex₂ C (up ℤ) (up ℤ) ⥤ CochainComplex C ℤ :=
  opOp _ ⋙
    ((HomologicalComplex.opFunctor (CochainComplex C ℤ) (up ℤ)) ⋙
      (ChainComplex.cochainComplexEquivalence ((CochainComplex C ℤ)ᵒᵖ)).functor ⋙
      ((CochainComplex.opEquivalence C).functor).mapHomologicalComplex (up ℤ) ⋙
      totalFunctor Cᵒᵖ (up ℤ) (up ℤ) (up ℤ) ⋙
      (CochainComplex.opEquivalence C).inverse).leftOp

end HomologicalComplex₂

scoped[HomologicalComplex₂] notation:max "Tot_π(" K ")" => HomologicalComplex₂.productTotal K
