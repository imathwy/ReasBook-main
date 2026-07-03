import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_12_23_1 (from Chap12) -/
open CategoryTheory.Limits
open scoped CategoryTheory

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/- Domain-style sampling for Definition 12.23.1:
- primary domain: filtered differential objects in a category with zero morphisms,
  obtained by specializing the differential-object owner from Definition 12.22.1 to the category
  of filtered objects from Definition 12.19.1;
- sampled core/canonical declarations in this domain:
  `HomologicalComplex (Fil(C)) (ComplexShape.refl PUnit.{1})`,
  `HomologicalComplex C (ComplexShape.refl PUnit.{1})`,
  `FilteredObject.Hom.preserves`,
  `HomologicalComplex.d_comp_d`;
- best owner abstraction: the one-object homological-complex owner
  `HomologicalComplex (Fil(C)) (ComplexShape.refl PUnit.{1})`;
- primitive data: a filtered object together with its unique differential, which is automatically
  filtration-preserving because it is a morphism in `Fil(C)`;
- derived API: preservation of each filtration stage via `FilteredObject.Hom.preserves`,
  square-zero of the differential via `HomologicalComplex.d_comp_d`, and commutation of morphisms
  with differentials via `HomologicalComplex.Hom.comm`;
- source/core/bridge triage:
  `source-facing`: a filtered object equipped with a filtration-preserving endomorphism squaring
    to zero;
  `core/canonical`: the one-object complex owner in `Fil(C)`;
  `bridge/view`: the forgetful view to Definition `12.22.1`, obtained by forgetting the
    filtration.

This item adds no new public data beyond the existing owner, so the refined file keeps a direct
canonical recall/check rather than introducing a parallel alias such as
`FilteredDifferentialObject`. -/
/- Definition 12.23.1: this is the `Fil(C)` specialization of the chapter's owner
declaration for differential objects from Definition 12.22.1. In the source's abelian setting,
this means a filtered differential object is canonically a one-object homological complex in the
category of filtered objects, equivalently a filtered object equipped with an endomorphism
preserving each filtration stage and squaring to zero. The owner recall itself only needs zero
morphisms on `C`. -/
#check (HomologicalComplex (Fil(C)) (ComplexShape.refl PUnit.{1}))

/- Companion recall: the unique differential of a one-object filtered complex preserves each
filtration stage because it is a morphism in `Fil(C)`. -/
recall FilteredObject.Hom.preserves

/- Companion recall: the unique differential of a one-object filtered complex squares to zero by
specializing `HomologicalComplex.d_comp_d`. -/
recall HomologicalComplex.d_comp_d

/- Companion recall: morphisms of one-object filtered complexes commute with the distinguished
differentials by `HomologicalComplex.Hom.comm`. -/
recall HomologicalComplex.Hom.comm

end CategoryTheory

/-! ### Lemma_12_23_2 (from Chap12) -/
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

open FilteredObject FilteredObject.Hom

namespace HomologicalComplex.Filtered

variable (K : HomologicalComplex (FilteredObject C) (ComplexShape.refl PUnit.{1}))

/-- The page-`E₀` complex attached to the filtered differential object `K`. -/
noncomputable def pageZero :
    HomologicalComplex C (ComplexShape.up' (0 : ℤ)) :=
  { X := fun p ↦ (gradedPiece K p).X PUnit.unit
    d := fun p q ↦
      if h : p = q then by
        subst h
        exact (gradedPiece K p).d PUnit.unit PUnit.unit
      else 0
    shape := fun p q hpq ↦ by
      by_cases h : p = q
      · exfalso
        exact hpq (by simp [ComplexShape.up', h])
      · simp [h]
    d_comp_d' := fun p q r hpq hqr ↦ by
      have hpq' : p = q := by
        simpa [ComplexShape.up'] using hpq
      have hqr' : q = r := by
        simpa [ComplexShape.up'] using hqr
      subst hpq'
      subst hqr'
      simpa [gradedPiece] using
        (gradedPiece K p).d_comp_d PUnit.unit PUnit.unit PUnit.unit }

private noncomputable def pageZeroScIso (p : ℤ) :
    (pageZero K).sc' p p p ≅
      (gradedPiece K p).sc' PUnit.unit PUnit.unit PUnit.unit :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [pageZero, gradedPiece])
    (by simp [pageZero, gradedPiece])

/-- The page-`E₀` complex computes, in degree `p`, the homology of the graded differential object
`gr^p(K)`. -/
noncomputable def pageZeroHomologyIso (p : ℤ) :
    (pageZero K).homology p ≅
      (gradedPiece K p).homology PUnit.unit := by
  let hprevPage : (ComplexShape.up' (0 : ℤ)).prev p = p :=
    ComplexShape.prev_eq' (ComplexShape.up' (0 : ℤ)) (by simp [ComplexShape.up'])
  let hnextPage : (ComplexShape.up' (0 : ℤ)).next p = p :=
    ComplexShape.next_eq' (ComplexShape.up' (0 : ℤ)) (by simp [ComplexShape.up'])
  exact
    (pageZero K).homologyIsoSc' p p p hprevPage hnextPage ≪≫
      ShortComplex.homologyMapIso (pageZeroScIso K p) ≪≫
        ((gradedPiece K p).homologyIsoSc' PUnit.unit PUnit.unit PUnit.unit
          rfl rfl).symm

variable {E : SpectralSequence C (fun r ↦ ComplexShape.up' (r : ℤ)) 0}

/-- The core owner class asserting that `E` is a spectral sequence associated to the filtered
differential object `K`, encoded by the literal page-zero identification with the associated
graded differential object. -/
class IsAssociatedToFilteredDifferentialObject
    (K : HomologicalComplex (FilteredObject C) (ComplexShape.refl PUnit.{1}))
    (E : SpectralSequence C (fun r ↦ ComplexShape.up' (r : ℤ)) 0) : Prop where
  pageZero_eq : E.page 0 = pageZero K

/-- Source-facing companion: the owner page-zero equality yields the canonical isomorphism from
the zeroth page of `E` to the graded page-zero complex of `K`. -/
noncomputable def pageZeroIso
    (K : HomologicalComplex (FilteredObject C) (ComplexShape.refl PUnit.{1}))
    (E : SpectralSequence C (fun r ↦ ComplexShape.up' (r : ℤ)) 0)
    [hE : IsAssociatedToFilteredDifferentialObject K E] :
    E.page 0 ≅ pageZero K :=
  eqToIso hE.pageZero_eq

/-- The page-`E₁` identification induced by a page-`E₀` comparison with the associated graded
complex. -/
noncomputable def pageOneIso
    (K : HomologicalComplex (FilteredObject C) (ComplexShape.refl PUnit.{1}))
    (E : SpectralSequence C (fun r ↦ ComplexShape.up' (r : ℤ)) 0)
    [hE : IsAssociatedToFilteredDifferentialObject K E] (p : ℤ) :
    (E.page 1).X p ≅
      (gradedPiece K p).homology PUnit.unit :=
  (E.iso 0 1 p).symm ≪≫
    HomologicalComplex.homologyMapIso (pageZeroIso K E) p ≪≫
      pageZeroHomologyIso K p

/-- Lemma 12.23.2: a filtered differential object admits an associated spectral sequence together
with the canonical page-`E₀` comparison isomorphism to the associated graded differential object
`pageZero K`. The page-`E₁` identification with the homology of the graded pieces is then derived
from the owner class `IsAssociatedToFilteredDifferentialObject K E`, the owner transition
`E.iso 0 1`, and `pageOneIso`, rather than stored as separate primitive data. -/
theorem exists_associatedSpectralSequence :
    ∃ E : SpectralSequence C (fun r ↦ ComplexShape.up' (r : ℤ)) 0,
      IsAssociatedToFilteredDifferentialObject K E := by
  sorry

end HomologicalComplex.Filtered

end CategoryTheory

/-! ### Lemma_12_23_3 (from Chap12) -/
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

/-! ### Definition_12_23_4 (from Chap12) -/
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

open FilteredObject

namespace HomologicalComplex.Filtered

/-- Every integer is bounded above by its successor. -/
theorem le_succ_int (p : ℤ) : p ≤ p + 1 := by
  omega

variable (K : HomologicalComplex (FilteredObject C) (ComplexShape.refl PUnit.{1}))

/- Domain-style sampling for Definition 12.23.4:
- primary domain: filtered differential objects in an abelian category and the induced filtration
  on their homology;
- sampled owner declarations in this domain:
  `FilteredObject.stage`,
  `FilteredObject.gradedPiece`,
  `FilteredObject.stageFunctor`,
  `FilteredObject.stageFunctorMapOfLE`,
  `FilteredObject.associatedGradedFunctor`,
  `GradedObject.eval_preservesZeroMorphisms`;
- best owner abstraction: the filtered differential object
  `K : HomologicalComplex (FilteredObject C) (ComplexShape.refl PUnit.{1})`, with stage and
  comparison data obtained by lifting the filtered-object owners along `mapHomologicalComplex`;
- primitive data: the filtered differential object `K`;
- derived API: `underlying`, `stage`, `stageMapOfLE`, `gradedPiece`, `homologyMap`, and the
  induced filtration on `H(K)`;
- internal bridge: the mapped stage inclusion into `underlying K`, used only to define the
  homology-stage images canonically;
- source/core/bridge triage:
  `source-facing`: `inducedHomologyFiltration`;
  `core/canonical`: the filtered-object owners named above together with the owner object `K`;
  `bridge/view`: the one-object-complex specializations in this namespace. -/

/-- Bridge/view layer: forget the filtration on the owner object of filtered differential
objects. -/
abbrev underlying : HomologicalComplex C (ComplexShape.refl PUnit.{1}) :=
  (FilteredObject.forget.mapHomologicalComplex (ComplexShape.refl PUnit.{1})).obj K

/-- Bridge/view layer: evaluate the owner object at the `p`-th filtration stage. -/
abbrev stage (p : ℤ) : HomologicalComplex C (ComplexShape.refl PUnit.{1}) :=
  ((stageFunctor p).mapHomologicalComplex (ComplexShape.refl PUnit.{1})).obj K

/-- Internal bridge: the inclusion of the `p`-th filtration stage differential object into the
underlying one. -/
private abbrev stageInclusion (p : ℤ) : stage K p ⟶ underlying K :=
  (NatTrans.mapHomologicalComplex (stageFunctorToForget p)
    (ComplexShape.refl PUnit.{1})).app K

/-- The canonical map `F^q K ⟶ F^p K` of one-object complexes for `p ≤ q`. -/
abbrev stageMapOfLE {p q : ℤ} (hpq : p ≤ q) : stage K q ⟶ stage K p :=
  (NatTrans.mapHomologicalComplex (stageFunctorMapOfLE hpq)
    (ComplexShape.refl PUnit.{1})).app K

/-- Bridge/view layer: the graded differential object `gr^p(K)` is obtained from the chapter
owner `associatedGradedFunctor` by evaluation at `p`. -/
noncomputable abbrev gradedPiece (p : ℤ) :
    HomologicalComplex C (ComplexShape.refl PUnit.{1}) :=
  ((associatedGradedFunctor ⋙ GradedObject.eval p).mapHomologicalComplex
    (ComplexShape.refl PUnit.{1})).obj K

/-- Bridge/view layer: for a one-object filtered differential object, the canonical graded piece
agrees with the cokernel presentation `F^p K / F^{p + 1} K`. -/
theorem gradedPiece_eq_cokernel (p : ℤ) :
    gradedPiece K p = cokernel (stageMapOfLE K (le_succ_int p)) := by
  sorry

/-- The canonical comparison between the owner-based graded piece and its cokernel presentation. -/
noncomputable def gradedPieceCokernelIso (p : ℤ) :
    gradedPiece K p ≅ cokernel (stageMapOfLE K (le_succ_int p)) :=
  eqToIso (gradedPiece_eq_cokernel K p)

/-- The map on homology induced by the inclusion `F^p K ⟶ K`. -/
noncomputable abbrev homologyMap (p : ℤ) :
    (stage K p).homology PUnit.unit ⟶ (underlying K).homology PUnit.unit :=
  HomologicalComplex.homologyMap (stageInclusion K p) PUnit.unit

/-- The inclusion `F^q K ⟶ K` factors through `F^p K ⟶ K` whenever `p ≤ q`. -/
private theorem stageMapOfLE_comp_stageInclusion {p q : ℤ} (hpq : p ≤ q) :
    stageMapOfLE K hpq ≫ stageInclusion K p = stageInclusion K q := by
  have h :=
    congrArg
      (fun α ↦ (NatTrans.mapHomologicalComplex α (ComplexShape.refl PUnit.{1})).app K)
      (stageFunctorMapOfLE_comp_stageFunctorToForget hpq)
  simpa [stageMapOfLE, stageInclusion, NatTrans.mapHomologicalComplex_comp] using h

-- Proof sketch: the inclusion `F^q K ⟶ K` factors through `F^p K ⟶ K` via `stageMapOfLE K hpq`;
-- apply functoriality of `HomologicalComplex.homologyMap`.
/-- The homology map from `F^q K` to `H(K)` factors through the map from `F^p K` whenever
`p ≤ q`. -/
private theorem homologyMap_factorization {p q : ℤ} (hpq : p ≤ q) :
    homologyMap K q =
      HomologicalComplex.homologyMap (stageMapOfLE K hpq) PUnit.unit ≫ homologyMap K p := by
  rw [homologyMap, homologyMap, ← HomologicalComplex.homologyMap_comp,
    stageMapOfLE_comp_stageInclusion]

-- Proof sketch: use `homologyMap_factorization` to see that the image of the map from
-- `F^q K` factors through the image of the map from `F^p K`, then apply monotonicity of image
-- subobjects.
/-- The images of the stagewise homology maps form a decreasing filtration. -/
private theorem inducedHomologyFiltration_antitone :
    Antitone
      (fun p : ℤ ↦ imageSubobject (homologyMap K p)) := by
  intro p q hpq
  change
    imageSubobject (homologyMap K q) ≤ imageSubobject (homologyMap K p)
  rw [homologyMap_factorization K hpq]
  exact imageSubobject_comp_le _ _

/-- Definition 12.23.4: the induced filtration on `H(K, d)` is the decreasing filtration whose
`p`-th stage is the image of the canonical map `H(F^p K, d) ⟶ H(K, d)`. -/
noncomputable def inducedHomologyFiltration :
    DecreasingFiltration ((underlying K).homology PUnit.unit) where
  toFun p := imageSubobject (homologyMap K p)
  monotone' _ _ hpq := inducedHomologyFiltration_antitone K hpq

-- Proof sketch: unfold `inducedHomologyFiltration`; the statement is exactly its defining
-- formula.
/-- The `p`-th stage of the induced homology filtration is the image of the stagewise homology
map. -/
theorem inducedHomologyFiltration_obj (p : ℤ) :
    (inducedHomologyFiltration K).obj p =
      imageSubobject (homologyMap K p) := rfl

end HomologicalComplex.Filtered

end CategoryTheory

/-! ### Lemma_12_23_5 (from Chap12) -/
open CategoryTheory
open CategoryTheory.Limits
open scoped SpectralSequence

noncomputable section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace HomologicalComplex.Filtered

variable (K : HomologicalComplex (FilteredObject C) (ComplexShape.refl PUnit.{1}))

/-- Bridge/view layer: forgetting the `E₀` page of the associated spectral sequence attached to a
filtered differential object yields the canonical page-`E₁` owner to which Definition `12.20.2`
applies. -/
abbrev toPageOneSpectralSequence
    (E : SpectralSequence C (fun r ↦ ComplexShape.up' (r : ℤ)) 0) :
    SpectralSequence C (fun r ↦ ComplexShape.up' (r : ℤ)) 1 where
  page r hr := E.page r <| by omega
  iso r r' q hrr' hr := E.iso r r' q hrr' <| by omega

section WeakConvergence

variable [LocallySmall C] [WellPowered C] [HasWidePullbacks C] [HasCoproducts C]
  [InitialMonoClass C]

private abbrev filtrationStage (p : ℤ) : Subobject ((K.X PUnit.unit).obj) :=
  (K.X PUnit.unit).filtration.obj p

private abbrev cyclesSubobject : Subobject ((K.X PUnit.unit).obj) :=
  kernelSubobject ((K.d PUnit.unit PUnit.unit).hom)

private abbrev boundariesSubobject : Subobject ((K.X PUnit.unit).obj) :=
  imageSubobject ((K.d PUnit.unit PUnit.unit).hom)

/- Domain-style triage for Lemma `12.23.5`.
- source-facing layer: the eventual cycle/boundary representatives from equations `(12.23.5.1)`
  and `(12.23.5.2)`;
- core/canonical owner: `inducedHomologyFiltration K` and the spectral-sequence owner
  `SpectralSequence.infinityPage`;
- bridge/view layer: the comparison theorem below, which uses the source-facing eventual
  inclusions to compare the intrinsic graded piece of `H(K)` with the canonical owner
  `E_∞^p`. -/

/-- The eventual boundary representative
`⋃_r (F^p K ∩ im(F^{p-r+1} K ⟶ K)) + F^{p+1} K`
appearing in equation `(12.23.5.2)`. -/
def eventualBoundaryStep (p : ℤ) :
    Subobject ((K.X PUnit.unit).obj) :=
  ⨆ r : ℕ,
    (filtrationStage K p ⊓
        imageSubobject
          ((filtrationStage K (p - r + 1)).arrow ≫ (K.d PUnit.unit PUnit.unit).hom)) ⊔
      filtrationStage K (p + 1)

/-- The eventual cycle representative
`⋂_r (F^p K ∩ d⁻¹(F^{p+r} K)) + F^{p+1} K`
appearing in equation `(12.23.5.1)`. -/
def eventualCycleStep (p : ℤ) :
    Subobject ((K.X PUnit.unit).obj) :=
  ⨅ r : ℕ,
    (filtrationStage K p ⊓
        (Subobject.pullback ((K.d PUnit.unit PUnit.unit).hom)).obj
          (filtrationStage K (p + r))) ⊔
      filtrationStage K (p + 1)

/-- The cycle representative
`(\ker d ∩ F^p K) + F^{p+1} K`
for the `p`-th graded piece of the induced homology filtration. -/
def homologyCycleStep (p : ℤ) :
    Subobject ((K.X PUnit.unit).obj) :=
  (cyclesSubobject K ⊓ filtrationStage K p) ⊔ filtrationStage K (p + 1)

/-- The boundary representative
`(\operatorname{im} d ∩ F^p K) + F^{p+1} K`
for the `p`-th graded piece of the induced homology filtration. -/
def homologyBoundaryStep (p : ℤ) :
    Subobject ((K.X PUnit.unit).obj) :=
  (boundariesSubobject K ⊓ filtrationStage K p) ⊔ filtrationStage K (p + 1)

-- Proof sketch: the source-facing inclusions from `(12.23.5.2)` and `(12.23.5.1)` place the
-- intrinsic representatives `homologyBoundaryStep K p ≤ homologyCycleStep K p` between the
-- actual limiting boundary and cycle pieces. Therefore `gr^p H(K)` is the intermediate quotient
-- of a chain of subobjects inside the eventual quotient `E_∞^p`.
/-- The eventual boundary representative is contained in the intrinsic boundary representative. -/
theorem eventualBoundaryStep_le_homologyBoundaryStep (p : ℤ) :
    eventualBoundaryStep K p ≤ homologyBoundaryStep K p := by
  sorry

/-- The intrinsic boundary representative is contained in the intrinsic cycle representative. -/
theorem homologyBoundaryStep_le_homologyCycleStep (p : ℤ) :
    homologyBoundaryStep K p ≤ homologyCycleStep K p := by
  sorry

/-- The intrinsic cycle representative is contained in the eventual cycle representative. -/
theorem homologyCycleStep_le_eventualCycleStep (p : ℤ) :
    homologyCycleStep K p ≤ eventualCycleStep K p := by
  sorry

/-- Lemma 12.23.5: once the eventual cycle and boundary pieces `Z_∞^p` and `B_∞^p` exist, the
always-true inclusions `(12.23.5.2)` and `(12.23.5.1)` show that the graded piece `gr^p H(K)` of
the induced homology filtration is a subquotient of the canonical limit term `E_∞^p` of the
associated spectral sequence. -/
theorem inducedHomologyGradedPiece_isSubquotient_limitTerm
    (E : SpectralSequence C (fun r ↦ ComplexShape.up' (r : ℤ)) 0)
    [IsAssociatedToFilteredDifferentialObject K E]
    (p : ℤ) :
    IsSubquotient ((inducedHomologyFiltration K).gradedPiece p)
      ((toPageOneSpectralSequence E).infinityPage p) := by
  sorry

end WeakConvergence

end HomologicalComplex.Filtered

end CategoryTheory

/-! ### Lemma_12_23_5_Submodule (from Chap12) -/
universe uR uM uN

section

variable {R : Type uR} [Ring R]
variable {M : Type uM} [AddCommGroup M] [Module R M]
variable {N : Type uN} [AddCommGroup N] [Module R N]

-- Proof sketch: each summand in the supremum is bounded by
-- `(LinearMap.range d ⊓ G p) ⊔ G (p + 1)`. Indeed, `Submodule.map d (F (p - r + 1))` is
-- contained in `LinearMap.range d` for every `r`, so
-- `G p ⊓ Submodule.map d (F (p - r + 1)) ≤ LinearMap.range d ⊓ G p`; then taking the supremum
-- over all `r` preserves the inequality.
/-- The supremum of the submodules `(G^p ∩ d(F^{p-r+1})) + G^{p+1}` is always contained in
`Im(d) ∩ G^p + G^{p+1}`. -/
theorem iSup_inf_map_prev_stage_sup_next_le_range_inf_stage_sup_next
    (d : M →ₗ[R] N) (F : ℤ → Submodule R M) (G : ℤ → Submodule R N) (p : ℤ) :
    (⨆ r : ℕ, (G p ⊓ Submodule.map d (F (p - r + 1))) ⊔ G (p + 1)) ≤
      (LinearMap.range d ⊓ G p) ⊔ G (p + 1) := by
  refine iSup_le fun r ↦ sup_le ?_ le_sup_right
  refine (le_inf ?_ inf_le_left).trans le_sup_left
  exact inf_le_right.trans LinearMap.map_le_range

end

/-! ### Definition_12_23_6 (from Chap12) -/
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace HomologicalComplex.Filtered

variable (K : HomologicalComplex (FilteredObject C) (ComplexShape.refl PUnit.{1}))

section Abutment

variable [LocallySmall C] [WellPowered C] [HasWidePullbacks C] [HasCoproducts C]
  [InitialMonoClass C]

/-- Definition 12.23.6 (1): the spectral sequence associated to a filtered differential object
weakly converges to `H(K)` if the actual eventual-cycle and eventual-boundary equalities
`(12.23.5.2)` and `(12.23.5.1)` hold in every filtration degree. This is stronger than the
subquotient comparison of Lemma `12.23.5`, and it is the equality-based criterion used for weak
convergence in the later source definitions. -/
def weaklyConvergesToHomology : Prop :=
  ∀ p : ℤ,
    eventualBoundaryStep K p = homologyBoundaryStep K p ∧
      homologyCycleStep K p = eventualCycleStep K p

/-- The induced filtration on `H(K)` is separated and exhaustive. -/
def inducedHomologyFiltrationSeparatedExhaustive : Prop :=
  DecreasingFiltration.IsSeparated (inducedHomologyFiltration K) ∧
    DecreasingFiltration.IsExhaustive (inducedHomologyFiltration K)

/-- Definition 12.23.6 (2): the spectral sequence associated to a filtered differential object
abuts to `H(K)` if it weakly converges to `H(K)` and the induced filtration on `H(K)` is
separated and exhaustive. -/
def abutsToHomology : Prop :=
  weaklyConvergesToHomology K ∧ inducedHomologyFiltrationSeparatedExhaustive K

-- Proof sketch: unfold `weaklyConvergesToHomology`; this is exactly the pair of pagewise
-- equalities `(12.23.5.2)` and `(12.23.5.1)` that encode stabilization of the actual eventual
-- boundaries and cycles in the associated spectral sequence.
/-- Weak convergence is equivalent to the pagewise equalities `(12.23.5.2)` and `(12.23.5.1)` for
the underlying filtered differential object. -/
theorem weaklyConvergesToHomology_iff :
    weaklyConvergesToHomology K ↔
      ∀ p : ℤ,
        eventualBoundaryStep K p = homologyBoundaryStep K p ∧
          homologyCycleStep K p = eventualCycleStep K p :=
  Iff.rfl

-- Proof sketch: the owner predicates `DecreasingFiltration.IsSeparated` and
-- `DecreasingFiltration.IsExhaustive` are equivalent, under the available complete lattice
-- structure on subobjects, to saying that the infimum of the filtration is `⊥` and the supremum
-- is `⊤`.
/-- The induced filtration on `H(K)` is separated and exhaustive exactly when its intersection is
zero and its union is the whole homology object. -/
theorem inducedHomologyFiltrationSeparatedExhaustive_iff :
    inducedHomologyFiltrationSeparatedExhaustive K ↔
      (⨅ p : ℤ, (inducedHomologyFiltration K).obj p) = ⊥ ∧
        (⨆ p : ℤ, (inducedHomologyFiltration K).obj p) = ⊤ := by
  simp [inducedHomologyFiltrationSeparatedExhaustive,
    DecreasingFiltration.isSeparated_iff_iInf_eq_bot,
    DecreasingFiltration.isExhaustive_iff_iSup_eq_top]

-- Proof sketch: unfold `abutsToHomology`; abutment is weak convergence together with
-- separatedness and exhaustiveness of the induced filtration on `H(K)`.
/-- Abutment is weak convergence together with separatedness and exhaustiveness of the induced
homology filtration. -/
theorem abutsToHomology_iff :
    abutsToHomology K ↔
      weaklyConvergesToHomology K ∧ inducedHomologyFiltrationSeparatedExhaustive K :=
  Iff.rfl

end Abutment

end HomologicalComplex.Filtered

end CategoryTheory

/-! ### Lemma_12_23_7 (from Chap12) -/
open CategoryTheory
open CategoryTheory.Limits
open ModuleCat
open HomologicalComplex.Filtered
open scoped CategoryTheory

noncomputable section

universe uR uM

section

variable {R : Type uR} [Ring R]
variable {M : Type uM} [AddCommGroup M] [Module R M]

/- Domain-style sampling for Lemma `12.23.7`:
- primary domain: filtered differential modules and the owner predicates on the associated
  one-object filtered differential object;
- sampled owner declarations in this domain:
  `CategoryTheory.DecreasingFiltration`,
  `CategoryTheory.FilteredObject`,
  `HomologicalComplex.Filtered.weaklyConvergesToHomology`,
  `HomologicalComplex.Filtered.abutsToHomology`,
  `FilteredCohomology.representative`;
- best owner abstraction: the packaged one-object complex in `Fil(ModuleCat R)`, with the Stacks
  Project submodule equalities kept as source-facing criteria;
- primitive data: the differential `d`, the antitone filtration `F`, and the stage-preservation
  proof `hdF`;
- derived API: the weak-convergence and abutment criteria below, obtained by specializing the
  owner predicates to the packaged filtered module, together with the canonical cohomology-step
  representative reused from `FilteredCohomology`;
- source/core/bridge triage:
  `source-facing`: `weakConvergenceCriterion` and `cohomologyFiltrationCriterion`;
  `core/canonical`: `HomologicalComplex.Filtered.{weaklyConvergesToHomology,abutsToHomology}`;
  `bridge/view`: the packaging of a filtered module as a one-object filtered differential object.

The owner predicates already exist upstream, so this file should only keep the source-facing
submodule criteria and the minimal bridge needed to specialize those owners. -/

/-- The pagewise equalities in equations `(12.23.5.2)` and `(12.23.5.1)` that characterize weak
convergence of the spectral sequence associated to a filtered differential module. -/
def weakConvergenceCriterion
    (d : M →ₗ[R] M) (F : ℤ → Submodule R M) : Prop :=
  ∀ p : ℤ,
    (⨆ r : ℕ, (F p ⊓ Submodule.map d (F (p - r + 1))) ⊔ F (p + 1)) =
        (LinearMap.range d ⊓ F p) ⊔ F (p + 1) ∧
      ((LinearMap.ker d ⊓ F p) ⊔ F (p + 1)) =
        ⨅ r : ℕ, (F p ⊓ Submodule.comap d (F (p + r))) ⊔ F (p + 1)

/-- The intersection/union equalities of Lemma `12.23.7 (2)` for the filtration induced on
cohomology, expressed on the canonical representatives
`FilteredCohomology.representative d d F p` inside `M`. -/
def cohomologyFiltrationCriterion
    (d : M →ₗ[R] M) (F : ℤ → Submodule R M) : Prop :=
  (⨅ p : ℤ, FilteredCohomology.representative d d F p) =
      LinearMap.range d ∧
    (⨆ p : ℤ, FilteredCohomology.representative d d F p) =
      LinearMap.ker d

private noncomputable abbrev toSubobject (S : Submodule R M) :
    Subobject (ModuleCat.of R M) :=
  (ModuleCat.subobjectModule (ModuleCat.of R M)).symm S

private def toFilteredObject (F : ℤ → Submodule R M) (hF : Antitone F) :
    Fil(ModuleCat R) where
  obj := ModuleCat.of R M
  filtration :=
    { toFun := fun p ↦ toSubobject (F (OrderDual.ofDual p))
      monotone' := by
        intro p q hpq
        exact
          (ModuleCat.subobjectModule (ModuleCat.of R M)).symm.monotone
            (show F (OrderDual.ofDual p) ≤ F (OrderDual.ofDual q) from hF hpq) }

variable [LocallySmall (ModuleCat R)] [WellPowered (ModuleCat R)]
  [HasWidePullbacks (ModuleCat R)] [HasCoproducts (ModuleCat R)]
  [InitialMonoClass (ModuleCat R)]

private theorem toSubobject_factors
    (d : M →ₗ[R] M) {S : Submodule R M} (hS : Submodule.map d S ≤ S) :
    (toSubobject S).Factors
      ((toSubobject S).arrow ≫ ModuleCat.ofHom d) := sorry

private def toFilteredEndomorphism
    (d : M →ₗ[R] M) (F : ℤ → Submodule R M) (hF : Antitone F)
    (hdF : ∀ p : ℤ, Submodule.map d (F p) ≤ F p) :
    toFilteredObject F hF ⟶ toFilteredObject F hF where
  hom := ModuleCat.ofHom d
  preserves := by
    intro p
    simpa [toFilteredObject] using toSubobject_factors d (hdF p)

private def toFilteredDifferentialObject
    (d : M →ₗ[R] M) (F : ℤ → Submodule R M) (hF : Antitone F)
    (hdF : ∀ p : ℤ, Submodule.map d (F p) ≤ F p) (hd : d.comp d = 0) :
    HomologicalComplex (Fil(ModuleCat R)) (ComplexShape.refl PUnit.{1}) where
  X := fun _ ↦ toFilteredObject F hF
  d := fun _ _ ↦ toFilteredEndomorphism d F hF hdF
  shape := by
    intro i j hij
    cases i
    cases j
    exact False.elim <| hij <| by simp
  d_comp_d' := by
    intro i j k _ _
    change toFilteredEndomorphism d F hF hdF ≫ toFilteredEndomorphism d F hF hdF = 0
    apply FilteredObject.Hom.ext
    ext x
    simpa [toFilteredEndomorphism] using LinearMap.congr_fun hd x

-- Proof sketch: package `(M, d, F)` as the corresponding one-object filtered differential object
-- in `FilteredObject (ModuleCat R)`, then specialize the owner criterion
-- `weaklyConvergesToHomology_iff` from Definition `12.23.6`.
/-- Lemma 12.23.7 (1): for a filtered differential module, weak convergence of the associated
spectral sequence to cohomology is exactly the pair of pagewise equalities `(12.23.5.2)` and
`(12.23.5.1)`. The canonical owner predicate is
`HomologicalComplex.Filtered.weaklyConvergesToHomology`; the right-hand side records its module
theoretic criterion. -/
theorem weaklyConvergesToCohomology_iff
    (d : M →ₗ[R] M) (F : ℤ → Submodule R M) (hF : Antitone F)
    (hdF : ∀ p : ℤ, Submodule.map d (F p) ≤ F p) (hd : d.comp d = 0) :
    weaklyConvergesToHomology (toFilteredDifferentialObject d F hF hdF hd) ↔
      weakConvergenceCriterion d F := sorry

/-- The induced filtration on `H(M, d)` is separated and exhaustive exactly when the textbook
intersection/union criterion holds for the representatives `Ker(d) ∩ F^p M + Im(d)`. -/
theorem cohomologyFiltrationCriterion_iff_separatedExhaustive
    (d : M →ₗ[R] M) (F : ℤ → Submodule R M) (hF : Antitone F)
    (hdF : ∀ p : ℤ, Submodule.map d (F p) ≤ F p) (hd : d.comp d = 0) :
    cohomologyFiltrationCriterion d F ↔
      inducedHomologyFiltrationSeparatedExhaustive
        (toFilteredDifferentialObject d F hF hdF hd) := sorry

-- Proof sketch: combine the owner characterization of abutment with the owner description of the
-- induced homology filtration as a decreasing filtration on `H(M, d)`, then identify its stages
-- in `ModuleCat R` with the representatives `Ker(d) ∩ F^p M + Im(d)`.
/-- Lemma 12.23.7 (2): for a filtered differential module, the associated spectral sequence abuts
to cohomology exactly when it weakly converges and the induced cohomology filtration satisfies the
textbook intersection/union criterion on the representatives `Ker(d) ∩ F^p M + Im(d)`. -/
theorem abutsToCohomology_iff
    (d : M →ₗ[R] M) (F : ℤ → Submodule R M) (hF : Antitone F)
    (hdF : ∀ p : ℤ, Submodule.map d (F p) ≤ F p) (hd : d.comp d = 0) :
    abutsToHomology (toFilteredDifferentialObject d F hF hdF hd) ↔
      weaklyConvergesToHomology (toFilteredDifferentialObject d F hF hdF hd) ∧
        cohomologyFiltrationCriterion d F := by
  rw [abutsToHomology_iff, ← cohomologyFiltrationCriterion_iff_separatedExhaustive d F hF hdF hd]

end
