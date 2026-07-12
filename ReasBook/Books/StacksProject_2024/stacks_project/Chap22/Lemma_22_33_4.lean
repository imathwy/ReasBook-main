import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import StacksProject_2024.Chap22.Lemma_22_33_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open DifferentialGradedCategory

noncomputable section

universe u v w x y z t

section

variable {R : Type u} [CommRing R]
variable {DGModA : Type v} {DGModB : Type w}
variable [DifferentialGradedCategory R DGModA] [DifferentialGradedCategory R DGModB]
variable {DerivedA : Type x} {DerivedB : Type y}
variable [Category.{z} DerivedA] [Category.{t} DerivedB]

-- Semantic recall hits: `Functor.totalLeftDerivedCounit` is the comparison from the total
-- left-derived tensor functor back to the underived tensor functor. Local Chapter 22 precedent
-- from Lemma `22.33.2` represents `- ⊗_A N` on homotopy categories by
-- `tensorWithN.mapK ⋙ QB`.

/-- Lemma 22.33.4: if the differential graded `(A, B)`-bimodule `N` has property `(P)` as a
left differential graded `A`-module, then the derived tensor product
`M ⊗_Aᴸ N` is computed by the ordinary tensor product `M ⊗_A N` for every
differential graded `A`-module `M`. In the current categorical owner, the property `(P)`
hypothesis is expressed by the induced tensor functor inverting quasi-isomorphisms, and
"computed by" is recorded by the total-left-derived counit being a natural isomorphism. -/
@[stacks 0GZ2]
theorem derivedTensorWithLeftPropertyP_isComputedByTensor
    (QisA : MorphismProperty (K R DGModA))
    (QisB : MorphismProperty (K R DGModB))
    (QA : K R DGModA ⥤ DerivedA) [QA.IsLocalization QisA]
    (QB : K R DGModB ⥤ DerivedB) [QB.IsLocalization QisB]
    (tensorWithN : DgFunctor R DGModA DGModB)
    [(tensorWithN.mapK ⋙ QB).HasLeftDerivedFunctor QisA]
    (hN_left_propertyP :
      QisA.IsInvertedBy (tensorWithN.mapK ⋙ QB)) :
    IsIso ((tensorWithN.mapK ⋙ QB).totalLeftDerivedCounit QA QisA) := by
  simpa using
    (Functor.isIso_of_isLeftDerivedFunctor_of_inverts
      ((tensorWithN.mapK ⋙ QB).totalLeftDerived QA QisA)
      ((tensorWithN.mapK ⋙ QB).totalLeftDerivedCounit QA QisA)
      hN_left_propertyP)

/-- Companion theorem: under the same property `(P)` hypothesis, the total-left-derived counit
at `M` is an isomorphism. This is the pointwise comparison form of
`derivedTensorWithLeftPropertyP_isComputedByTensor`. -/
theorem derivedTensorWithLeftPropertyP_counit_app_isIso
    (QisA : MorphismProperty (K R DGModA))
    (QisB : MorphismProperty (K R DGModB))
    (QA : K R DGModA ⥤ DerivedA) [QA.IsLocalization QisA]
    (QB : K R DGModB ⥤ DerivedB) [QB.IsLocalization QisB]
    (tensorWithN : DgFunctor R DGModA DGModB)
    [(tensorWithN.mapK ⋙ QB).HasLeftDerivedFunctor QisA]
    (hN_left_propertyP :
      QisA.IsInvertedBy (tensorWithN.mapK ⋙ QB))
    (M : K R DGModA) :
    IsIso (((tensorWithN.mapK ⋙ QB).totalLeftDerivedCounit QA QisA).app M) := by
  letI : IsIso ((tensorWithN.mapK ⋙ QB).totalLeftDerivedCounit QA QisA) :=
    derivedTensorWithLeftPropertyP_isComputedByTensor
      QisA QisB QA QB tensorWithN hN_left_propertyP
  infer_instance

end
