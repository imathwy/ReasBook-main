import stacks_project.Chap12.Lemma_12_24_2
import stacks_project.Chap12.Lemma_12_19_12
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜]

/-
Domain-style sampling for Lemma `12.24.3`.
- primary domain: filtered cochain complexes, their graded-piece complexes, and the page-one
  comparison with the associated cohomological spectral sequence;
- sampled owner declarations in this domain:
  `FilteredComplex`,
  `FilteredComplex.stageMapOfLE`,
  `FilteredComplex.gradedPiece`,
  `FilteredComplex.pageOneIso`,
  `ShortComplex.ShortExact`,
  `Subobject.Factors`;
- best owner abstraction: the filtered-complex owner `FilteredComplex 𝒜`, with the page-one
  comparison already owned by `FilteredComplex.pageOneIso`; the filtration-raising hypothesis is
  most canonically expressed by `Subobject.Factors` for the next filtration stage;
- primitive data: a filtered complex `K`, and in part `(3)` a filtration-raising lift of its
  differential through `F^{p+1} K^{n+1}`;
- derived API in this file: the two-step quotient short exact sequence, its boundary map on
  graded-piece homology, and the induced map on graded pieces from a filtration-raising lift;
- source/core/bridge triage:
  `source-facing`: the boundary-map and raised-graded-piece descriptions of the page-one
  differential;
  `core/canonical`: `FilteredComplex`, `ShortComplex`, `ShortComplex.ShortExact`, and the owner
  `FilteredComplex.pageOneIso`;
  `bridge/view`: the two-step quotient complex and the induced comparison maps used to express the
  source-facing formulas. -/

namespace FilteredComplex

section Basic

variable [HasZeroMorphisms 𝒜]

private theorem twoStep_le (p : ℤ) : p ≤ p + 1 + 1 := by
  omega

private abbrev stageMap (K : FilteredComplex 𝒜) (p i j : ℤ) :
    (K.X i).stage p ⟶ (K.X j).stage p :=
  FilteredObject.Hom.stageMap (K.d i j) p

private theorem stageMap_arrow (K : FilteredComplex 𝒜) (p i j : ℤ) :
    stageMap K p i j ≫ ((K.X j).filtration.obj p).arrow =
      ((K.X i).filtration.obj p).arrow ≫ (K.d i j).hom :=
  FilteredObject.Hom.stageMap_comm (K.d i j) p

end Basic

section GradedPieceObject

variable [HasZeroMorphisms 𝒜] [HasCokernels 𝒜]

private theorem gradedPiece_obj_eq_cokernel (K : FilteredComplex 𝒜) (n p : ℤ) :
    (K.gradedPiece p).X n = cokernel ((K.stageMapOfLE (lt_add_one p).le).f n) := by
  rfl

end GradedPieceObject

section Cokernel

variable [HasZeroMorphisms 𝒜] [HasFiniteColimits 𝒜]

private theorem gradedPiece_eq_cokernel (K : FilteredComplex 𝒜) (p : ℤ) :
    K.gradedPiece p = cokernel (K.stageMapOfLE (lt_add_one p).le) := sorry

private noncomputable def gradedPieceCokernelIso (K : FilteredComplex 𝒜) (p : ℤ) :
    K.gradedPiece p ≅ cokernel (K.stageMapOfLE (lt_add_one p).le) :=
  eqToIso (gradedPiece_eq_cokernel K p)

omit [HasFiniteColimits 𝒜] in
private theorem gradedPieceSuccToTwoStep_condition (K : FilteredComplex 𝒜) (p : ℤ) :
    K.stageMapOfLE (lt_add_one (p + 1)).le ≫ K.stageMapOfLE (lt_add_one p).le =
      (𝟙 _) ≫ K.stageMapOfLE (twoStep_le p) := by
  have hproof :
      le_trans (lt_add_one p).le (lt_add_one (p + 1)).le = twoStep_le p := by
    exact Subsingleton.elim _ _
  simpa [hproof] using K.stageMapOfLE_comp (lt_add_one p).le (lt_add_one (p + 1)).le

omit [HasFiniteColimits 𝒜] in
private theorem twoStepToGradedPiece_condition (K : FilteredComplex 𝒜) (p : ℤ) :
    K.stageMapOfLE (twoStep_le p) ≫ (𝟙 _) =
      K.stageMapOfLE (lt_add_one (p + 1)).le ≫ K.stageMapOfLE (lt_add_one p).le := by
  simpa using (gradedPieceSuccToTwoStep_condition K p).symm

private noncomputable def twoStepQuotient (K : FilteredComplex 𝒜) (p : ℤ) :
    CochainComplex 𝒜 ℤ :=
  cokernel (K.stageMapOfLE (twoStep_le p))

private noncomputable def gradedPieceSuccToTwoStepHom (K : FilteredComplex 𝒜) (p : ℤ) :
    K.gradedPiece (p + 1) ⟶ twoStepQuotient K p :=
  (gradedPieceCokernelIso K (p + 1)).hom ≫
    cokernel.map
      (K.stageMapOfLE (lt_add_one (p + 1)).le)
      (K.stageMapOfLE (twoStep_le p))
      (𝟙 _)
      (K.stageMapOfLE (lt_add_one p).le)
      (gradedPieceSuccToTwoStep_condition K p)

private noncomputable def twoStepToGradedPieceHom (K : FilteredComplex 𝒜) (p : ℤ) :
    twoStepQuotient K p ⟶ K.gradedPiece p :=
  cokernel.map
    (K.stageMapOfLE (twoStep_le p))
    (K.stageMapOfLE (lt_add_one p).le)
    (K.stageMapOfLE (lt_add_one (p + 1)).le)
    (𝟙 _)
    (twoStepToGradedPiece_condition K p) ≫
    (gradedPieceCokernelIso K p).inv

private theorem twoStepGradedShortComplex_zero (K : FilteredComplex 𝒜) (p : ℤ) :
    gradedPieceSuccToTwoStepHom K p ≫ twoStepToGradedPieceHom K p = 0 := sorry

private noncomputable def twoStepGradedShortComplex (K : FilteredComplex 𝒜) (p : ℤ) :
    ShortComplex (CochainComplex 𝒜 ℤ) :=
  ShortComplex.mk
    (gradedPieceSuccToTwoStepHom K p)
    (twoStepToGradedPieceHom K p)
    (twoStepGradedShortComplex_zero K p)

end Cokernel

section Boundary

variable [Abelian 𝒜]

private theorem twoStepGradedShortExact (K : FilteredComplex 𝒜) (p : ℤ) :
    (twoStepGradedShortComplex K p).ShortExact := sorry

/-- The connecting morphism in homology attached to the canonical short exact sequence
`0 ⟶ gr^{p+1}(K^•) ⟶ F^p K^• / F^{p+2} K^• ⟶ gr^p(K^•) ⟶ 0`. -/
private theorem pageOneBoundaryMap_target_eq (K : FilteredComplex 𝒜) (p q : ℤ) :
    (gr^{p + 1} K).homology (p + q + 1) =
      (gr^{p + 1} K).homology ((p + 1) + q) :=
  by
    simp [add_assoc, add_left_comm, add_comm]

/-- The boundary map on the page-one terms coming from the short exact sequence
`0 ⟶ gr^{p+1}(K^•) ⟶ F^p K^• / F^{p+2} K^• ⟶ gr^p(K^•) ⟶ 0`. -/
noncomputable def pageOneBoundaryMap (K : FilteredComplex 𝒜) (p q : ℤ) :
    (gr^{p} K).homology (p + q) ⟶ (gr^{p + 1} K).homology ((p + 1) + q) :=
  (twoStepGradedShortExact K p).δ (p + q) (p + q + 1)
      (ComplexShape.up_mk (p + q) (p + q + 1) rfl) ≫
    eqToHom (pageOneBoundaryMap_target_eq K p q)

-- Proof sketch: apply the boundary-map construction in homology to the short exact sequence
-- `0 ⟶ gr^{p+1}(K^•) ⟶ F^p K^• / F^{p+2} K^• ⟶ gr^p(K^•) ⟶ 0`, and compare the page-one terms
-- of the chosen cohomological spectral sequence with the homology of the graded complexes.
/-- Lemma 12.24.3 (1): for a cohomological spectral sequence equipped with the standard page-one
identification for a filtered complex, the `d₁^{p,q}` differential is the boundary morphism in
cohomology attached to the short exact sequence of complexes
`0 ⟶ gr^{p+1}(K^•) ⟶ F^p K^• / F^{p+2} K^• ⟶ gr^p(K^•) ⟶ 0`. -/
theorem pageOne_differential_eq_boundary_map
    (K : FilteredComplex 𝒜) (E : CohomologicalSpectralSequence 𝒜 0)
    [IsAssociatedToFilteredComplex K E]
    (p q : ℤ) :
    CommSq
      ((E.page 1).d (p, q) (p + 1, q))
      ((pageOneIso K E p q).hom)
      ((pageOneIso K E (p + 1) q).hom)
      (K.pageOneBoundaryMap p q) := sorry

end Boundary

section RaisesFiltration

variable [HasZeroMorphisms 𝒜]

/-- The differential of a filtered complex raises the filtration by one if, for every degree `n`
and filtration index `p`, the ambient composite `F^p K^n ⟶ K^{n+1}` factors through the next
filtration stage `F^{p+1} K^{n+1} ↪ K^{n+1}`. Equivalently, the restricted differential
`F^p K^n ⟶ F^p K^{n+1}` factors through the inclusion `F^{p+1} K^{n+1} ⟶ F^p K^{n+1}`. -/
def RaisesFiltration (K : FilteredComplex 𝒜) : Prop :=
  ∀ n p : ℤ,
    ((K.X (n + 1)).filtration.obj (p + 1)).Factors
      (((K.X n).filtration.obj p).arrow ≫ (K.d n (n + 1)).hom)

private noncomputable def raisedStageMap
    (K : FilteredComplex 𝒜) (hK : K.RaisesFiltration) (n p : ℤ) :
    ((K.X n).filtration.obj p : 𝒜) ⟶ ((K.X (n + 1)).filtration.obj (p + 1) : 𝒜) :=
  ((K.X (n + 1)).filtration.obj (p + 1)).factorThru
    (((K.X n).filtration.obj p).arrow ≫ (K.d n (n + 1)).hom)
    (hK n p)

private theorem raisedStageMap_arrow
    (K : FilteredComplex 𝒜) (hK : K.RaisesFiltration) (n p : ℤ) :
    raisedStageMap K hK n p ≫
        ((K.X (n + 1)).filtration.obj (p + 1)).arrow =
      ((K.X n).filtration.obj p).arrow ≫ (K.d n (n + 1)).hom :=
  Subobject.factorThru_arrow _ _ (hK n p)

private theorem raisedStageMap_stageMap
    (K : FilteredComplex 𝒜) (hK : K.RaisesFiltration) (n p : ℤ) :
    raisedStageMap K hK n p ≫
        Subobject.ofLE
          ((K.X (n + 1)).filtration.obj (p + 1))
          ((K.X (n + 1)).filtration.obj p)
          ((K.X (n + 1)).succ_le p) =
      stageMap K p n (n + 1) := by
  apply (cancel_mono ((K.X (n + 1)).filtration.obj p).arrow).1
  rw [Category.assoc, Subobject.ofLE_arrow, raisedStageMap_arrow, stageMap_arrow]

end RaisesFiltration

section RaisedGradedPiece

variable [HasZeroMorphisms 𝒜] [HasCokernels 𝒜]

private theorem raisedGradedPieceMap_condition
    (K : FilteredComplex 𝒜) (hK : K.RaisesFiltration) (n p : ℤ) :
    (K.stageMapOfLE (lt_add_one p).le).f n ≫
        raisedStageMap K hK n p ≫
          cokernel.π ((K.stageMapOfLE (lt_add_one (p + 1)).le).f (n + 1)) =
      0 := sorry

/-- The map on graded pieces induced by a filtration-raising differential. -/
noncomputable def raisedGradedPieceMap
    (K : FilteredComplex 𝒜) (hK : K.RaisesFiltration) (n p : ℤ) :
    (gr^{p} K).X n ⟶ (gr^{p + 1} K).X (n + 1) :=
  eqToHom (gradedPiece_obj_eq_cokernel K n p) ≫
    cokernel.desc
      ((K.stageMapOfLE (lt_add_one p).le).f n)
      (raisedStageMap K hK n p ≫
        cokernel.π ((K.stageMapOfLE (lt_add_one (p + 1)).le).f (n + 1)))
      (raisedGradedPieceMap_condition K hK n p) ≫
    eqToHom (gradedPiece_obj_eq_cokernel K (n + 1) (p + 1)).symm

-- Proof sketch: if each differential `F^p K^n ⟶ F^p K^{n+1}` factors through `F^{p+1} K^{n+1}`,
-- then its composite with the quotient map to `gr^p(K^{n+1})` vanishes, so the induced
-- differential on `gr^p(K^•)` is zero.
/-- Lemma 12.24.3 (2): if the differential of a filtered complex factors through the next
filtration step, then the induced differential on each graded complex `gr^p(K^•)` is zero. -/
theorem gradedPiece_d_eq_zero_of_filtration_raise
    (K : FilteredComplex 𝒜) (hK : K.RaisesFiltration) (n p : ℤ) :
    (gr^{p} K).d n (n + 1) = 0 := sorry

private theorem gradedPiece_prev_d_eq_zero_of_filtration_raise
    (K : FilteredComplex 𝒜) (hK : K.RaisesFiltration) (p q : ℤ) :
    (gr^{p} K).d (p + q - 1) (p + q) = 0 := sorry

private theorem raisedGradedPieceMap_target_eq (K : FilteredComplex 𝒜) (p q : ℤ) :
    (gr^{p + 1} K).X (p + q + 1) =
      (gr^{p + 1} K).X ((p + 1) + q) := by
  simp [add_assoc, add_left_comm, add_comm]

/-- The `(p,q)`-indexed graded-piece map induced by a filtration-raising differential. -/
noncomputable def pageOneRaisedGradedPieceMap
    (K : FilteredComplex 𝒜) (hK : K.RaisesFiltration) (p q : ℤ) :
    (gr^{p} K).X (p + q) ⟶ (gr^{p + 1} K).X ((p + 1) + q) :=
  raisedGradedPieceMap K hK (p + q) p ≫
    eqToHom (raisedGradedPieceMap_target_eq K p q)

end RaisedGradedPiece

section PageOneZero

variable [HasZeroMorphisms 𝒜] [HasCokernels 𝒜] [CategoryWithHomology 𝒜]

/-- When the graded differential vanishes, the page-one term is canonically the corresponding
graded piece in degree `p + q`. -/
noncomputable def pageOneZeroIso
    (K : FilteredComplex 𝒜) (hK : K.RaisesFiltration) (p q : ℤ) :
    (gr^{p} K).homology (p + q) ≅ (gr^{p} K).X (p + q) :=
  ((gr^{p} K).isoHomologyπ (p + q - 1) (p + q)
      (by simp)
      (gradedPiece_prev_d_eq_zero_of_filtration_raise K hK p q)).symm ≪≫
    (gr^{p} K).iCyclesIso (p + q) (p + q + 1)
      (by simp)
      (gradedPiece_d_eq_zero_of_filtration_raise K hK (p + q) p)

end PageOneZero

section RaisedBoundary

variable [Abelian 𝒜]

-- Proof sketch: once the `E₁`-page is identified with the degree-`p+q` objects of the graded
-- complexes because those differentials vanish, the description of `d₁` as a connecting map
-- reduces to the map induced by the filtration-raising differential on the graded pieces.
/-- Lemma 12.24.3 (3): after identifying `E₁^{p,q}` with the degree-`p+q` piece of `gr^p(K^•)`
under the filtration-raising hypothesis, the page-one differential is the morphism induced by the
differential on the filtered complex. -/
theorem pageOne_differential_eq_raisedGradedPieceMap
    (K : FilteredComplex 𝒜) (E : CohomologicalSpectralSequence 𝒜 0)
    [IsAssociatedToFilteredComplex K E]
    (hK : K.RaisesFiltration)
    (p q : ℤ) :
    CommSq
      ((E.page 1).d (p, q) (p + 1, q))
      ((pageOneIso K E p q).hom ≫ (pageOneZeroIso K hK p q).hom)
      ((pageOneIso K E (p + 1) q).hom ≫ (pageOneZeroIso K hK (p + 1) q).hom)
      (pageOneRaisedGradedPieceMap K hK p q) := sorry

end RaisedBoundary

end FilteredComplex

end CategoryTheory
