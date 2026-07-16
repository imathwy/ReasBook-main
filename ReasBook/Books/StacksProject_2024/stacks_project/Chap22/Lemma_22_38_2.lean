import StacksProject_2024.stacks_project.Chap22.Definition_22_3_1
import StacksProject_2024.stacks_project.Chap22.Lemma_22_26_5
import StacksProject_2024.stacks_project.Chap22.Lemma_22_34_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open DifferentialGradedCategory

noncomputable section

universe u vR vA vB vC vDC

section

variable {R : Type u} [CommRing R]
variable (A C : CochainDGAlgebra R)
variable {DGModR : Type vR} {DGModA : Type vA} {DGModB : Type vB} {DGModC : Type vC}
variable [DifferentialGradedCategory R DGModR]
variable [DifferentialGradedCategory R DGModA]
variable [DifferentialGradedCategory R DGModB]
variable [DifferentialGradedCategory R DGModC]
variable {DC : Type vDC} [Category DC]
variable (QisR : MorphismProperty (K R DGModR)) [QisR.ContainsIdentities]
variable (QisA : MorphismProperty (K R DGModA))
variable (QisB : MorphismProperty (K R DGModB))
variable (QC : K R DGModC ⥤ DC)
variable (underlyingRObject : CochainDGAlgebra R → K R DGModR)
variable (tensorWithUnderlyingAlgebraOnK : CochainDGAlgebra R → K R DGModR ⥤ K R DGModR)
variable (tensorWithN : DgFunctor R DGModA DGModB)
variable (tensorWithN' : DgFunctor R DGModB DGModC)
variable [(tensorWithUnderlyingAlgebraOnK C).HasPointwiseLeftDerivedFunctorAt QisR
  (underlyingRObject A)]
variable [(tensorWithN.mapK ⋙ QisB.Q).HasLeftDerivedFunctor QisA]
variable [(tensorWithN'.mapK ⋙ QC).HasLeftDerivedFunctor QisB]

-- Source/core/bridge triage:
-- * source-facing: existence of a DG tensor functor `tensorWithNN'` representing tensoring with
--   the composite `(A, C)`-bimodule `N ⊗_B N'`, together with the resulting isomorphism on
--   derived tensor functors;
-- * core/canonical: an explicit comparison morphism between the chosen total left-derived tensor
--   functors;
-- * bridge/view: the underived associativity identification
--   `tensorWithN.mapK ⋙ tensorWithN'.mapK ≅ tensorWithNN'.mapK`
--   and the explicit-witness bridge
--   `derivedTensorCompositionComparisonOfHasLeftDerivedFunctor`.

/-- Lemma 22.38.2: let `R` be a ring and let `(A, d)`, `(B, d)`, and `(C, d)` be cochain
differential graded `R`-algebras. If the ordinary tensor `A ⊗[R] C` represents `A ⊗[R]ᴸ C`,
then for any differential graded `(A, B)`- and `(B, C)`-bimodule tensor functors `tensorWithN`
and `tensorWithN'`, their composite derived tensor functor is isomorphic to derived tensoring
with some differential graded `(A, C)`-bimodule. In the current Chapter 22 API, that bimodule is
represented by a DG tensor functor `tensorWithNN'`; the theorem records both the underived
associativity identification `tensorAssoc` and the invertibility of the canonical Chapter 22
comparison morphism
`derivedTensorCompositionComparisonOfHasLeftDerivedFunctor`. -/
@[stacks 0BZ8]
theorem existsDerivedTensorCompositionIsoOfTensorAlgebraRepresents
    (hAC :
      IsIso
        (leftDerivedValueProjection
          QisR (tensorWithUnderlyingAlgebraOnK C) (𝟙 (underlyingRObject A))
          (QisR.id_mem (underlyingRObject A)))) :
    ∃ (tensorWithNN' : DgFunctor R DGModA DGModC)
      (tensorAssoc :
        tensorWithN.mapK ⋙ tensorWithN'.mapK ≅ tensorWithNN'.mapK)
      (hNN' : (tensorWithNN'.mapK ⋙ QC).HasLeftDerivedFunctor QisA),
      IsIso
        (derivedTensorCompositionComparisonOfHasLeftDerivedFunctor
          QisA QisB QC tensorWithN.mapK tensorWithN'.mapK tensorWithNN'.mapK hNN'
          tensorAssoc) := by
  sorry

end
