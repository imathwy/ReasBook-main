import Mathlib
import stacks_project.Chap12.Definition_12_23_4
import stacks_project.Chap12.Lemma_12_23_2
import stacks_project.Chap12.Lemma_12_19_12

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory

namespace HomologicalComplex.Filtered

variable {C : Type u} [Category.{v} C] [Abelian C]

open FilteredObject FilteredObject.Hom

variable (K : HomologicalComplex (FilteredObject C) (ComplexShape.refl PUnit.{1}))

/-- The two-step successor inequality on `ℤ`. -/
-- Proof sketch: compose the inequalities `p ≤ p + 1` and `p + 1 ≤ p + 2`.
private theorem int_le_add_two (p : ℤ) : p ≤ p + 1 + 1 := sorry

/-- Successive stage-comparison maps compose to the direct comparison map. -/
private theorem stageMapOfLE_comp {p q r : ℤ} (hpq : p ≤ q) (hqr : q ≤ r) :
    stageMapOfLE K hqr ≫ stageMapOfLE K hpq = stageMapOfLE K (le_trans hpq hqr) := by
  have h :=
    congrArg
      (fun α ↦ (NatTrans.mapHomologicalComplex α (ComplexShape.refl PUnit.{1})).app K)
      (stageFunctorMapOfLE_comp (C := C) hpq hqr)
  simpa [stageMapOfLE, NatTrans.mapHomologicalComplex_comp] using h

/-- The one-object differential object `F^p K / F^{p + 2} K`. -/
private noncomputable def twoStepQuotientDifferentialObject (p : ℤ) :
    HomologicalComplex C (ComplexShape.refl PUnit.{1}) :=
  cokernel (stageMapOfLE K (int_le_add_two p))

/-- The quotient map `gr^{p + 1} K ⟶ F^p K / F^{p + 2} K` induced by the inclusion
`F^{p + 1} K ⟶ F^p K`. -/
private theorem gradedPieceSuccToTwoStepQuotient_condition (p : ℤ) :
    stageMapOfLE K (le_succ_int (p + 1)) ≫ stageMapOfLE K (le_succ_int p) =
      (𝟙 _) ≫ stageMapOfLE K (int_le_add_two p) := by
  have hproof :
      le_trans (le_succ_int p) (le_succ_int (p + 1)) = int_le_add_two p := by
    apply Subsingleton.elim
  simpa [hproof] using stageMapOfLE_comp K (le_succ_int p) (le_succ_int (p + 1))

/-- The morphism of one-object differential objects `gr^{p + 1} K ⟶ F^p K / F^{p + 2} K`. -/
private noncomputable def gradedPieceSuccToTwoStepQuotientHom (p : ℤ) :
    gradedPiece K (p + 1) ⟶ twoStepQuotientDifferentialObject K p :=
  (gradedPieceCokernelIso K (p + 1)).inv ≫
    cokernel.map
      (stageMapOfLE K (le_succ_int (p + 1)))
      (stageMapOfLE K (int_le_add_two p))
      (𝟙 _)
      (stageMapOfLE K (le_succ_int p))
      (gradedPieceSuccToTwoStepQuotient_condition K p)

/-- The projection `F^p K / F^{p + 2} K ⟶ gr^p K`. -/
private theorem twoStepQuotientToGradedPiece_condition (p : ℤ) :
    stageMapOfLE K (int_le_add_two p) ≫ (𝟙 _) =
      stageMapOfLE K (le_succ_int (p + 1)) ≫ stageMapOfLE K (le_succ_int p) := by
  simpa using (gradedPieceSuccToTwoStepQuotient_condition K p).symm

/-- The morphism of one-object differential objects `F^p K / F^{p + 2} K ⟶ gr^p K`. -/
private noncomputable def twoStepQuotientToGradedPieceHom (p : ℤ) :
    twoStepQuotientDifferentialObject K p ⟶ gradedPiece K p :=
  cokernel.map
      (stageMapOfLE K (int_le_add_two p))
      (stageMapOfLE K (le_succ_int p))
      (stageMapOfLE K (le_succ_int (p + 1)))
      (𝟙 _)
      (twoStepQuotientToGradedPiece_condition K p) ≫
    (gradedPieceCokernelIso K p).hom

/-- The composite `gr^{p + 1} K ⟶ F^p K / F^{p + 2} K ⟶ gr^p K` is zero as a morphism of
one-object differential objects. -/
-- Proof sketch: the projection to `gr^p K` kills the image of `F^{p + 1} K ⟶ F^p K`, and the
-- first map is induced by that inclusion.
private theorem twoStepGradedShortComplex_zero (p : ℤ) :
    gradedPieceSuccToTwoStepQuotientHom K p ≫ twoStepQuotientToGradedPieceHom K p = 0 := sorry

/-- The short complex of one-object differential objects
`gr^{p + 1} K ⟶ F^p K / F^{p + 2} K ⟶ gr^p K`. -/
private noncomputable def twoStepGradedShortComplex (p : ℤ) :
    ShortComplex (HomologicalComplex C (ComplexShape.refl PUnit.{1})) :=
  ShortComplex.mk
    (gradedPieceSuccToTwoStepQuotientHom K p)
    (twoStepQuotientToGradedPieceHom K p)
    (twoStepGradedShortComplex_zero K p)

/-- The short complex
`0 ⟶ gr^{p + 1} K ⟶ F^p K / F^{p + 2} K ⟶ gr^p K ⟶ 0`
is short exact in one-object differential objects. -/
-- Proof sketch: evaluate the complex at the unique object `PUnit.unit`; this gives the usual
-- graded-piece short exact sequence of cokernels associated to the filtration stages.
private theorem twoStepGradedShortExact (p : ℤ) :
    (twoStepGradedShortComplex K p).ShortExact := sorry

/-- The boundary map
`H(gr^p K) ⟶ H(gr^{p + 1} K)`
attached to the short exact sequence
`0 ⟶ gr^{p + 1} K ⟶ F^p K / F^{p + 2} K ⟶ gr^p K ⟶ 0`. -/
noncomputable def pageOneBoundaryMap (p : ℤ) :
    (gradedPiece K p).homology PUnit.unit ⟶
      (gradedPiece K (p + 1)).homology PUnit.unit :=
  (twoStepGradedShortExact K p).δ PUnit.unit PUnit.unit rfl

-- Proof sketch: for an associated spectral sequence `E` of `K`, the page-`E₁` comparison is the
-- owner isomorphism `pageOneIso K E`, and the source-facing statement is that under this
-- identification the `d₁` differential is the connecting morphism of the graded short exact
-- sequence.
/-- Lemma 12.23.3: for an associated spectral sequence `E` of the filtered differential object
`K`, the differential `d_1^p : E₁^p ⟶ E₁^{p + 1}` agrees, under the canonical page-`E₁`
identifications from Lemma `12.23.2`, with the boundary map in homology attached to the short
exact sequence of differential objects
`0 ⟶ gr^{p + 1} K ⟶ F^p K / F^{p + 2} K ⟶ gr^p K ⟶ 0`. -/
theorem pageOne_differential_eq_boundary_map
    (E : SpectralSequence C (fun r ↦ ComplexShape.up' (r : ℤ)) 0)
    [IsAssociatedToFilteredDifferentialObject K E]
    (p : ℤ) :
    (E.page 1).d p (p + 1) ≫ (pageOneIso K E (p + 1)).hom =
      (pageOneIso K E p).hom ≫ pageOneBoundaryMap K p := sorry

end HomologicalComplex.Filtered

end CategoryTheory
