import Mathlib
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_12_24_1 (from Chap12) -/
open CategoryTheory
open CategoryTheory.Limits
open scoped CategoryTheory
open CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable (𝒜 : Type u) [Category.{v} 𝒜] [HasZeroMorphisms 𝒜]

/- Definition 12.24.1: a filtered complex is a cochain complex in the category `Fil(𝒜)` of
filtered objects. In this project, `Fil(𝒜)` is represented by the owner abstraction
`FilteredObject 𝒜`, so the notion is recorded directly as `CochainComplex (Fil(𝒜)) ℤ`. The
source text uses this in the abelian setting, but the owner expression itself only needs the
filtered-object category structure together with zero morphisms; later cohomological
constructions add `[Abelian 𝒜]` when homology is involved. The abbreviation `FilteredComplex` is
kept as stable chapter vocabulary because the owner type is used pervasively downstream. -/
abbrev FilteredComplex (𝒜 : Type u) [Category.{v} 𝒜] [HasZeroMorphisms 𝒜] :=
  CochainComplex (Fil(𝒜)) ℤ

end CategoryTheory

/-! ### Lemma_12_24_2 (from Chap12) -/
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory

open FilteredComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

namespace CohomologicalSpectralSequence

/-- Bridge/view layer: forgetting the `E₀` page turns a cohomological spectral sequence starting
at `0` into the same spectral sequence viewed from page `E₁` onward. -/
abbrev toPageOneSpectralSequence (E : CohomologicalSpectralSequence 𝒜 0) :
    SpectralSequence 𝒜 (fun r ↦ ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)) 1 where
  page r hr := E.page r
  iso r r' pq hrr' hr := E.iso r r' pq

end CohomologicalSpectralSequence

namespace FilteredComplex

variable {K : FilteredComplex 𝒜} {E : CohomologicalSpectralSequence 𝒜 0}

/-- Bridge/view layer: for a fixed filtration index `p`, the `p`-th column of the `E₀` page of a
cohomological spectral sequence is a cochain complex in the `q`-direction. -/
def pageZeroColumn (E : CohomologicalSpectralSequence 𝒜 0) (p : ℤ) : CochainComplex 𝒜 ℤ where
  X q := (E.page 0).X (p, q)
  d q q' := (E.page 0).d (p, q) (p, q')
  shape q q' hq := by
    have hpq :
        ¬ (ComplexShape.up' (⟨(0 : ℤ), 1⟩ : ℤ × ℤ)).Rel (p, q) (p, q') := by
      simpa [ComplexShape.up'] using hq
    exact (E.page 0).shape (p, q) (p, q') hpq
  d_comp_d' q q' q'' hqq' hq'q'' := by
    exact (E.page 0).d_comp_d (p, q) (p, q') (p, q'')

/-- Bridge/view layer: fixing the filtration index `p` turns the page-`E₀` construction into a
functor from cohomological spectral sequences to cochain complexes in the `q`-direction. -/
noncomputable def pageZeroColumnFunctor (p : ℤ) :
    CohomologicalSpectralSequence 𝒜 0 ⥤ CochainComplex 𝒜 ℤ where
  obj E := pageZeroColumn E p
  map φ :=
    { f := fun q ↦ (φ.hom 0).f (p, q)
      comm' := by
        intro q q' hqq'
        simpa [pageZeroColumn] using (φ.hom 0).comm (p, q) (p, q') }
  map_id E := by
    ext q
    rfl
  map_comp φ ψ := by
    ext q
    rfl

/-- Bridge/view layer: for a fixed filtration index `p`, the associated graded complex
`gr^p(K^•)` may be viewed as a cochain complex in the `q`-direction along the antidiagonal
`n = p + q`. -/
def gradedPieceColumn (K : FilteredComplex 𝒜) (p : ℤ) : CochainComplex 𝒜 ℤ where
  X q := (gradedPiece K p).X (p + q)
  d q q' := (gradedPiece K p).d (p + q) (p + q')
  shape q q' hq := by
    have hpq : ¬ (ComplexShape.up ℤ).Rel (p + q) (p + q') := by
      simpa [ComplexShape.up, ComplexShape.up', add_assoc] using hq
    exact (gradedPiece K p).shape (p + q) (p + q') hpq
  d_comp_d' q q' q'' hqq' hq'q'' := by
    exact (gradedPiece K p).d_comp_d (p + q) (p + q') (p + q'')

/-- Bridge/view layer: fixing the filtration index `p` turns the reindexed graded-piece
construction into a functor from filtered complexes to cochain complexes in the `q`-direction. -/
noncomputable def gradedPieceColumnFunctor (p : ℤ) :
    FilteredComplex 𝒜 ⥤ CochainComplex 𝒜 ℤ where
  obj K := gradedPieceColumn K p
  map α :=
    { f := fun q ↦ (gradedPieceMap α p).f (p + q)
      comm' := by
        intro q q' hqq'
        simpa [gradedPieceColumn, hqq', add_assoc] using
          (gradedPieceMap α p).comm (p + q) (p + q') }
  map_id K := by
    ext q
    simpa [gradedPieceMap, gradedPieceColumn] using
      congrArg
        (fun φ ↦ φ.f (p + q))
        (((associatedGradedFunctor ⋙ GradedObject.eval p).mapHomologicalComplex
          (ComplexShape.up ℤ)).map_id K)
  map_comp α β := by
    ext q
    simpa [gradedPieceMap, gradedPieceColumn] using
      congrArg
        (fun φ ↦ φ.f (p + q))
        (((associatedGradedFunctor ⋙ GradedObject.eval p).mapHomologicalComplex
          (ComplexShape.up ℤ)).map_comp α β)

end FilteredComplex

/-- The core owner predicate asserting that `E` is a cohomological spectral sequence associated to
the filtered complex `K`, encoded by the existence of the standard page-zero comparison with the
graded pieces. -/
class IsAssociatedToFilteredComplex
    (K : FilteredComplex 𝒜) (E : CohomologicalSpectralSequence 𝒜 0) : Prop where
  pageZero_eq : ∀ p : ℤ,
    FilteredComplex.pageZeroColumn E p = FilteredComplex.gradedPieceColumn K p

namespace FilteredComplex

private noncomputable def pageZeroColumnScIso (E : CohomologicalSpectralSequence 𝒜 0) (p q : ℤ) :
    (pageZeroColumn E p).sc' (q - 1) q (q + 1) ≅
      (E.page 0).sc' (p, q - 1) (p, q) (p, q + 1) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp [pageZeroColumn])
    (by simp [pageZeroColumn])

/-- Bridge/view layer: the homology of the fixed-`p` `E₀` column computes the homology object of
the full `E₀` page at bidegree `(p,q)`. -/
private noncomputable def pageZeroColumn_homologyIso
    (E : CohomologicalSpectralSequence 𝒜 0) (p q : ℤ) :
    (pageZeroColumn E p).homology q ≅ (E.page 0).homology (p, q) :=
  let hprevColumn : (ComplexShape.up ℤ).prev q = q - 1 :=
    ComplexShape.prev_eq' (ComplexShape.up ℤ) (by simp [ComplexShape.up, ComplexShape.up'])
  let hnextColumn : (ComplexShape.up ℤ).next q = q + 1 :=
    ComplexShape.next_eq' (ComplexShape.up ℤ) (by simp [ComplexShape.up, ComplexShape.up'])
  let hprevPage :
      (ComplexShape.up' (⟨(0 : ℤ), 1⟩ : ℤ × ℤ)).prev (p, q) = (p, q - 1) :=
    ComplexShape.prev_eq' (ComplexShape.up' (⟨(0 : ℤ), 1⟩ : ℤ × ℤ))
      (by simp [ComplexShape.up'])
  let hnextPage :
      (ComplexShape.up' (⟨(0 : ℤ), 1⟩ : ℤ × ℤ)).next (p, q) = (p, q + 1) :=
    ComplexShape.next_eq' (ComplexShape.up' (⟨(0 : ℤ), 1⟩ : ℤ × ℤ))
      (by simp [ComplexShape.up'])
  (pageZeroColumn E p).homologyIsoSc' (q - 1) q (q + 1) hprevColumn hnextColumn ≪≫
    ShortComplex.homologyMapIso (pageZeroColumnScIso E p q) ≪≫
    ((E.page 0).homologyIsoSc' (p, q - 1) (p, q) (p, q + 1) hprevPage hnextPage).symm

private noncomputable def gradedPieceColumnScIso (K : FilteredComplex 𝒜) (p q : ℤ) :
    (gradedPieceColumn K p).sc' (q - 1) q (q + 1) ≅
      (gradedPiece K p).sc' (p + (q - 1)) (p + q) (p + (q + 1)) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp [gradedPieceColumn])
    (by simp [gradedPieceColumn])

/-- Bridge/view layer: the homology of the reindexed graded-piece complex along the antidiagonal
agrees with the ordinary homology of `gr^p(K^•)` in total degree `p + q`. -/
private noncomputable def gradedPieceColumn_homologyIso
    (K : FilteredComplex 𝒜) (p q : ℤ) :
    (gradedPieceColumn K p).homology q ≅ (gradedPiece K p).homology (p + q) :=
  let hprevColumn : (ComplexShape.up ℤ).prev q = q - 1 :=
    ComplexShape.prev_eq' (ComplexShape.up ℤ) (by simp [ComplexShape.up, ComplexShape.up'])
  let hnextColumn : (ComplexShape.up ℤ).next q = q + 1 :=
    ComplexShape.next_eq' (ComplexShape.up ℤ) (by simp [ComplexShape.up, ComplexShape.up'])
  let hprevGraded : (ComplexShape.up ℤ).prev (p + q) = p + (q - 1) :=
    ComplexShape.prev_eq' (ComplexShape.up ℤ)
      (by simp [ComplexShape.up, ComplexShape.up', sub_eq_add_neg, add_left_comm, add_comm])
  let hnextGraded : (ComplexShape.up ℤ).next (p + q) = p + (q + 1) :=
    ComplexShape.next_eq' (ComplexShape.up ℤ) (by simp [ComplexShape.up, ComplexShape.up', add_assoc])
  (gradedPieceColumn K p).homologyIsoSc' (q - 1) q (q + 1) hprevColumn hnextColumn ≪≫
    ShortComplex.homologyMapIso (gradedPieceColumnScIso K p q) ≪≫
    ((gradedPiece K p).homologyIsoSc' (p + (q - 1)) (p + q) (p + (q + 1))
      hprevGraded hnextGraded).symm

/-- Source-facing companion: the owner page-zero equality yields the canonical isomorphism from
the `p`-th `E₀` column to the corresponding graded-piece column. -/
noncomputable def pageZeroIso
    (K : FilteredComplex 𝒜) (E : CohomologicalSpectralSequence 𝒜 0)
    [hE : IsAssociatedToFilteredComplex K E] (p : ℤ) :
    pageZeroColumn E p ≅ gradedPieceColumn K p :=
  eqToIso (hE.pageZero_eq p)

/-- Source-facing companion: a page-zero column identification yields the standard page-one
identification by applying the owner transition `E.iso 0 1` to the homology of that
identification. -/
noncomputable def pageOneIso
    (K : FilteredComplex 𝒜) (E : CohomologicalSpectralSequence 𝒜 0)
    [hE : IsAssociatedToFilteredComplex K E]
    (p q : ℤ) :
    (E.page 1).X (p, q) ≅ (gradedPiece K p).homology (p + q) :=
  (E.iso 0 1 (p, q)).symm ≪≫
    (pageZeroColumn_homologyIso E p q).symm ≪≫
    HomologicalComplex.homologyMapIso (pageZeroIso K E p) q ≪≫
    gradedPieceColumn_homologyIso K p q

/-- Source-facing companion: the column-complex identification on page `E₀` yields, for each
fixed `p` and consecutive `q`, the canonical commutative square comparing differentials. -/
theorem pageZeroIso_commSq
    (K : FilteredComplex 𝒜) (E : CohomologicalSpectralSequence 𝒜 0)
    [hE : IsAssociatedToFilteredComplex K E]
    (p q : ℤ) :
    CommSq
      ((pageZeroColumn E p).d q (q + 1))
      ((pageZeroIso K E p).hom.f q)
      ((pageZeroIso K E p).hom.f (q + 1))
      ((gradedPieceColumn K p).d q (q + 1)) := sorry

end FilteredComplex

/-- Lemma 12.24.2: for a filtered complex `(K^\bullet, F)` in an abelian category, there exists
an associated cohomological spectral sequence together with the standard page-zero comparison data
identifying each fixed-`p` `E₀` column with the corresponding graded-piece complex
`gr^p(K^•)`. The chapter owner predicate `IsAssociatedToFilteredComplex K E` records these
canonical page-zero identifications, and the induced isomorphism family is
`FilteredComplex.pageZeroIso K E`. The differential
compatibility square is recovered from `FilteredComplex.pageZeroIso_commSq`, and the page-one
identification from `FilteredComplex.pageOneIso`. -/
theorem exists_filteredComplexAssociatedSpectralSequence
    (K : FilteredComplex 𝒜) :
    ∃ E : CohomologicalSpectralSequence 𝒜 0,
      IsAssociatedToFilteredComplex K E := by
  sorry

end CategoryTheory

/-! ### Lemma_12_24_3 (from Chap12) -/
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

/-! ### Lemma_12_24_4 (from Chap12) -/
open CategoryTheory

universe v u

namespace CategoryTheory

open FilteredComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

variable {K L : FilteredComplex 𝒜}

/-
Domain-style sampling for Lemma `12.24.4`.
- primary domain: functoriality of the Chapter `12` associated cohomological spectral sequence of a
  filtered complex;
- sampled core/canonical declarations in this domain:
  `SpectralSequence.Hom`,
  `SpectralSequence.hom_ext`,
  `IsAssociatedToFilteredComplex`,
  `FilteredComplex.pageZeroIso`,
  `FilteredComplex.pageZeroColumnFunctor`,
  `FilteredComplex.gradedPieceColumnFunctor`;
- best owner abstraction: the mathlib owner category of cohomological spectral sequences, via
  `SpectralSequence.Hom`, together with the Chapter `12` owner predicate
  `IsAssociatedToFilteredComplex K E` and its canonical page-zero comparison isomorphisms
  `FilteredComplex.pageZeroIso`; the fixed-column comparison maps are derived by functoriality from
  `FilteredComplex.pageZeroColumnFunctor` and `FilteredComplex.gradedPieceColumnFunctor`;
- primitive data: a morphism `α : K ⟶ L` of filtered complexes and owner witnesses expressing that
  the chosen spectral sequences `E` and `E'` are associated to `K` and `L`;
- derived API in this file: the induced morphism `associatedSpectralSequenceMap E E' α`, its
  page-zero compatibility theorem `associatedSpectralSequenceMap_commSq E E' α`, and the
  companion existence/uniqueness theorems;
- source/core/bridge triage:
  `source-facing`: `associatedSpectralSequenceMap`;
  `core/canonical`: `IsAssociatedToFilteredComplex`, `pageZeroIso`,
    `pageZeroColumnFunctor`, and `gradedPieceColumnFunctor`;
  `bridge/view`: the fixed-column comparison squares obtained from those owner functors. -/

section AssociatedSpectralSequenceMap

variable (E E' : CohomologicalSpectralSequence 𝒜 0)
variable [IsAssociatedToFilteredComplex K E] [IsAssociatedToFilteredComplex L E']
variable (α : K ⟶ L)

/-- A morphism of filtered complexes induces at least one compatible morphism between any chosen
associated spectral sequences. -/
theorem exists_associatedSpectralSequenceMap :
    ∃ φ : E ⟶ E',
      ∀ p : ℤ,
        CommSq
          ((pageZeroColumnFunctor p).map φ)
          (pageZeroIso K E p).hom
          (pageZeroIso L E' p).hom
          ((gradedPieceColumnFunctor p).map α) := by
  sorry

/-- Two morphisms of associated spectral sequences are equal as soon as they induce the same
canonical page-zero comparison squares. -/
theorem associatedSpectralSequenceMap_ext
    {φ ψ : E ⟶ E'}
    (hφ :
      ∀ p : ℤ,
        CommSq
          ((pageZeroColumnFunctor p).map φ)
          (pageZeroIso K E p).hom
          (pageZeroIso L E' p).hom
          ((gradedPieceColumnFunctor p).map α))
    (hψ :
      ∀ p : ℤ,
        CommSq
          ((pageZeroColumnFunctor p).map ψ)
          (pageZeroIso K E p).hom
          (pageZeroIso L E' p).hom
          ((gradedPieceColumnFunctor p).map α)) :
    φ = ψ := by
  apply SpectralSequence.hom_ext
  intro r hr
  induction r, hr using Int.le_induction with
  | base =>
      apply HomologicalComplex.hom_ext _ _
      intro pq
      rcases pq with ⟨p, q⟩
      have hcomm :
          (pageZeroColumnFunctor p).map φ ≫ (pageZeroIso L E' p).hom =
            (pageZeroColumnFunctor p).map ψ ≫ (pageZeroIso L E' p).hom := by
        exact (hφ p).w.trans (hψ p).w.symm
      have hq := congrArg (fun f ↦ f.f q) hcomm
      simpa [pageZeroColumnFunctor] using
        (cancel_mono ((pageZeroIso L E' p).hom.f q)).1 hq
  | succ n hn hn_eq =>
      apply HomologicalComplex.hom_ext _ _
      intro pq
      have hcomm :
          (E.iso n (n + 1) pq).hom ≫ (φ.hom (n + 1)).f pq =
            (E.iso n (n + 1) pq).hom ≫ (ψ.hom (n + 1)).f pq := by
        calc
          (E.iso n (n + 1) pq).hom ≫ (φ.hom (n + 1)).f pq =
              HomologicalComplex.homologyMap (φ.hom n) pq ≫ (E'.iso n (n + 1) pq).hom := by
                exact (φ.comm n (n + 1) pq).symm
          _ = HomologicalComplex.homologyMap (ψ.hom n) pq ≫ (E'.iso n (n + 1) pq).hom := by
                simp [hn_eq]
          _ = (E.iso n (n + 1) pq).hom ≫ (ψ.hom (n + 1)).f pq := by
                simpa using (ψ.comm n (n + 1) pq)
      exact (cancel_epi ((E.iso n (n + 1) pq).hom)).1 hcomm

/-- The induced morphism of associated spectral sequences is uniquely determined by the page-zero
comparison squares. -/
theorem existsUnique_associatedSpectralSequenceMap :
    ∃! φ : E ⟶ E',
      ∀ p : ℤ,
        CommSq
          ((pageZeroColumnFunctor p).map φ)
          (pageZeroIso K E p).hom
          (pageZeroIso L E' p).hom
          ((gradedPieceColumnFunctor p).map α) := by
  have h :
      ∃ φ : E ⟶ E',
        ∀ p : ℤ,
          CommSq
            ((pageZeroColumnFunctor p).map φ)
            (pageZeroIso K E p).hom
            (pageZeroIso L E' p).hom
            ((gradedPieceColumnFunctor p).map α) :=
    exists_associatedSpectralSequenceMap E E' α
  rcases h with ⟨φ, hφ⟩
  refine ⟨φ, hφ, ?_⟩
  intro ψ hψ
  exact associatedSpectralSequenceMap_ext E E' α hψ hφ

/-- The canonical morphism of associated spectral sequences induced by a morphism of filtered
complexes between chosen associated spectral sequences `E` and `E'`. -/
noncomputable def associatedSpectralSequenceMap : E ⟶ E' :=
  Classical.choose <|
    (existsUnique_associatedSpectralSequenceMap E E' α).exists

/-- The induced morphism of associated spectral sequences satisfies the canonical page-zero
comparison squares. -/
theorem associatedSpectralSequenceMap_commSq (p : ℤ) :
    CommSq
      ((pageZeroColumnFunctor p).map (associatedSpectralSequenceMap E E' α))
      (pageZeroIso K E p).hom
      (pageZeroIso L E' p).hom
      ((gradedPieceColumnFunctor p).map α) := by
  have h :
      ∀ p : ℤ,
        CommSq
          ((pageZeroColumnFunctor p).map (associatedSpectralSequenceMap E E' α))
          (pageZeroIso K E p).hom
          (pageZeroIso L E' p).hom
          ((gradedPieceColumnFunctor p).map α) :=
    Classical.choose_spec <|
      (existsUnique_associatedSpectralSequenceMap E E' α).exists
  exact h p

end AssociatedSpectralSequenceMap

end CategoryTheory

/-! ### Definition_12_24_5 (from Chap12) -/
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [HasZeroMorphisms 𝒜]

/-
Domain-style sampling for Definition `12.24.5`.
- primary domain: filtered cochain complexes over a category with zero morphisms and, in the
  abelian case, the induced filtration on their cohomology;
- sampled core/canonical declarations in this domain:
  `FilteredComplex 𝒜`,
  `FilteredObject.stageFunctor`,
  `FilteredObject.stageFunctorToForget`,
  `FilteredObject.stageFunctorMapOfLE`,
  `FilteredObject.quotientFunctor`,
  `FilteredObject.associatedGradedFunctor`,
  `GradedObject.eval`;
- best owner abstraction: the canonical cochain-complex object
  `FilteredComplex 𝒜`, recalled in Definition `12.24.1`;
- primitive data: a filtered cochain complex `K : FilteredComplex 𝒜`;
- derived API: forgetting filtration, evaluating stages, graded pieces, the stagewise cohomology
  maps, the textbook notation `F^{p} K^•` and `gr^{p} K^•`, and the induced decreasing
  filtration on `H^n(K^•)`;
- source/core/bridge triage:
  `source-facing`: `inducedCohomologyFiltration`;
  `core/canonical`: the owner type `FilteredComplex 𝒜` and the filtered-object
  stage functors together with `associatedGradedFunctor ⋙ GradedObject.eval p`;
  `bridge/view`: `underlying`, `underlyingMap`, `stage`, `stageMap`, `stageInclusion`,
    `stageMapOfLE`, `gradedPiece`, and `cohomologyMap`. -/

namespace FilteredComplex

open FilteredObject

/-- Bridge/view layer: forget the filtration on the owner object of filtered cochain complexes. -/
abbrev underlying (K : FilteredComplex 𝒜) : CochainComplex 𝒜 ℤ :=
  (FilteredObject.forget.mapHomologicalComplex (ComplexShape.up ℤ)).obj K

/-- Bridge/view layer: the morphism on underlying cochain complexes induced by a morphism of
filtered complexes. -/
abbrev underlyingMap {K L : FilteredComplex 𝒜} (α : K ⟶ L) :
    K.underlying ⟶ L.underlying :=
  (FilteredObject.forget.mapHomologicalComplex (ComplexShape.up ℤ)).map α

/-- Bridge/view layer: evaluate a filtered cochain complex at the `p`-th filtration stage. -/
abbrev stage (K : FilteredComplex 𝒜) (p : ℤ) : CochainComplex 𝒜 ℤ :=
  ((stageFunctor p).mapHomologicalComplex (ComplexShape.up ℤ)).obj K

/-- Textbook notation for the `p`-th filtration stage complex `F^p K^•`. -/
notation:max "F^{" p "} " K:max => FilteredComplex.stage K p

/-- Bridge/view layer: the morphism on `p`-th stage complexes induced by a morphism of filtered
complexes. -/
abbrev stageMap {K L : FilteredComplex 𝒜} (α : K ⟶ L) (p : ℤ) :
    K.stage p ⟶ L.stage p :=
  ((stageFunctor p).mapHomologicalComplex (ComplexShape.up ℤ)).map α

/-- Bridge/view layer: the canonical inclusion of the `p`-th filtration stage complex into the
underlying complex. -/
abbrev stageInclusion (K : FilteredComplex 𝒜) (p : ℤ) :
    K.stage p ⟶ K.underlying :=
  (NatTrans.mapHomologicalComplex (stageFunctorToForget p) (ComplexShape.up ℤ)).app K

/-- The canonical map from the `q`-th filtration stage complex to the `p`-th stage complex for
`p ≤ q`. -/
abbrev stageMapOfLE (K : FilteredComplex 𝒜) {p q : ℤ}
    (hpq : p ≤ q) : K.stage q ⟶ K.stage p :=
  (NatTrans.mapHomologicalComplex (stageFunctorMapOfLE hpq)
    (ComplexShape.up ℤ)).app K

/-- The canonical comparison map `F^p K^• ⟶ F^p K^•` is the identity. -/
theorem stageMapOfLE_refl (K : FilteredComplex 𝒜) (p : ℤ) :
    K.stageMapOfLE (show p ≤ p by rfl) = 𝟙 (K.stage p) := by
  ext n
  change
    Subobject.ofLE
        ((show FilteredObject 𝒜 from K.X n).filtration.obj p)
        ((show FilteredObject 𝒜 from K.X n).filtration.obj p)
        _ =
      𝟙 (Subobject.underlying.obj ((show FilteredObject 𝒜 from K.X n).filtration.obj p))
  rw [Subobject.ofLE_refl]

/-- Successive stage comparisons compose to the direct comparison. -/
theorem stageMapOfLE_comp (K : FilteredComplex 𝒜) {p q r : ℤ}
    (hpq : p ≤ q) (hqr : q ≤ r) :
    K.stageMapOfLE hqr ≫ K.stageMapOfLE hpq = K.stageMapOfLE (le_trans hpq hqr) := by
  have h :=
    congrArg
      (fun α ↦ (NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app K)
      (stageFunctorMapOfLE_comp hpq hqr)
  simpa [stageMapOfLE, NatTrans.mapHomologicalComplex_comp] using h

-- Proof sketch: check the equality degreewise after postcomposing with the inclusion
-- `((K.X n).filtration.obj q).arrow`; use `Subobject.ofLE_arrow`.
/-- The inclusion `F^q K^• ⟶ K^•` factors through `F^p K^• ⟶ K^•` whenever `p ≤ q`. -/
theorem stageMapOfLE_comp_stageInclusion (K : FilteredComplex 𝒜) {p q : ℤ}
    (hpq : p ≤ q) :
    stageMapOfLE K hpq ≫ stageInclusion K p = stageInclusion K q := by
  have h :=
    congrArg
      (fun α ↦ (NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app K)
      (stageFunctorMapOfLE_comp_stageFunctorToForget hpq)
  simpa [stageMapOfLE, stageInclusion, NatTrans.mapHomologicalComplex_comp] using h

section Graded

variable [HasZeroMorphisms 𝒜] [HasCokernels 𝒜]

/-- The associated graded complex `gr(K^•)` of a filtered complex. -/
noncomputable abbrev associatedGraded (K : FilteredComplex 𝒜) :
    CochainComplex (GradedObject ℤ 𝒜) ℤ :=
  (associatedGradedFunctor.mapHomologicalComplex (ComplexShape.up ℤ)).obj K

/-- The morphism on associated graded complexes induced by a morphism of filtered complexes. -/
noncomputable abbrev associatedGradedMap {K L : FilteredComplex 𝒜} (α : K ⟶ L) :
    K.associatedGraded ⟶ L.associatedGraded :=
  (associatedGradedFunctor.mapHomologicalComplex (ComplexShape.up ℤ)).map α

section GradedHomology

variable [CategoryWithHomology (GradedObject ℤ 𝒜)]

noncomputable instance associatedGraded_hasHomology (K : FilteredComplex 𝒜) (n : ℤ) :
    HomologicalComplex.HasHomology K.associatedGraded n :=
  inferInstanceAs
    (HomologicalComplex.HasHomology
      ((associatedGradedFunctor.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) n)

end GradedHomology

/-- The `p`-th graded piece `gr^p(K^•) = F^p K^• / F^{p + 1} K^•` of a filtered complex. -/
noncomputable abbrev gradedPiece (K : FilteredComplex 𝒜) (p : ℤ) :
    CochainComplex 𝒜 ℤ :=
  ((associatedGradedFunctor ⋙ GradedObject.eval p).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K

/-- Textbook notation for the graded-piece complex `gr^p(K^•)`. -/
notation:max "gr^{" p "} " K:max => FilteredComplex.gradedPiece K p

/-- The morphism induced on the `p`-th graded-piece complexes by a morphism of filtered
complexes. -/
noncomputable abbrev gradedPieceMap {K L : FilteredComplex 𝒜} (α : K ⟶ L) (p : ℤ) :
    gradedPiece K p ⟶ gradedPiece L p :=
  ((associatedGradedFunctor ⋙ GradedObject.eval p).mapHomologicalComplex
    (ComplexShape.up ℤ)).map α

end Graded

section CohomologyMap

variable [CategoryWithHomology 𝒜]

private noncomputable instance stage_hasHomology (K : FilteredComplex 𝒜) (p n : ℤ) :
    HomologicalComplex.HasHomology (stage K p) n :=
  inferInstanceAs
    (HomologicalComplex.HasHomology
      (((stageFunctor p).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) n)

private noncomputable instance underlying_hasHomology (K : FilteredComplex 𝒜) (n : ℤ) :
    HomologicalComplex.HasHomology (underlying K) n :=
  inferInstanceAs
    (HomologicalComplex.HasHomology
      ((FilteredObject.forget.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) n)

/-- The map on degree-`n` cohomology induced by the inclusion `F^p K^• ⟶ K^•`. -/
noncomputable abbrev cohomologyMap (K : FilteredComplex 𝒜) (p n : ℤ) :
    (stage K p).homology n ⟶ (underlying K).homology n :=
  HomologicalComplex.homologyMap (stageInclusion K p) n

-- Proof sketch: apply `HomologicalComplex.homologyMap_comp` to
-- `stageMapOfLE_comp_inclusion`.
/-- The cohomology map from `F^q K^•` to `H^n(K^•)` factors through the one from `F^p K^•` when
`p ≤ q`. -/
private theorem cohomologyMap_factorization (K : FilteredComplex 𝒜) {p q n : ℤ}
    (hpq : p ≤ q) :
    K.cohomologyMap q n =
      HomologicalComplex.homologyMap (K.stageMapOfLE hpq) n ≫ K.cohomologyMap p n := by
  rw [cohomologyMap, ← HomologicalComplex.homologyMap_comp, stageMapOfLE_comp_stageInclusion]

end CohomologyMap

section CohomologyFiltration

variable [HasImages 𝒜] [CategoryWithHomology 𝒜]

-- Proof sketch: use `cohomologyMap_factorization` and `Limits.imageSubobject_comp_le` to compare
-- the images for `q` and `p`.
/-- The images of the stagewise cohomology maps form a decreasing filtration. -/
private theorem inducedCohomologyFiltration_antitone (K : FilteredComplex 𝒜)
    (n : ℤ) : Antitone (fun p : ℤ ↦ imageSubobject (K.cohomologyMap p n)) := by
  intro p q hpq
  change imageSubobject (K.cohomologyMap q n) ≤ imageSubobject (K.cohomologyMap p n)
  rw [cohomologyMap_factorization K hpq]
  exact imageSubobject_comp_le _ _

/-- Definition 12.24.5: for a filtered complex `(K^•, F)` in an abelian category, the induced
filtration on `H^n(K^•)` is the decreasing filtration defined by
`F^p H^n(K^•) = \operatorname{Im}(H^n(F^p K^•) \to H^n(K^•))`. -/
noncomputable def inducedCohomologyFiltration (K : FilteredComplex 𝒜)
    (n : ℤ) : DecreasingFiltration (K.underlying.homology n) where
  toFun p := imageSubobject (K.cohomologyMap p n)
  monotone' := by
    intro p q hpq
    exact inducedCohomologyFiltration_antitone K n hpq

-- Proof sketch: unfold `inducedCohomologyFiltration`; the statement is exactly its defining
-- formula.
/-- The `p`-th stage of the induced cohomology filtration is the image of the map
`H^n(F^p K^•) ⟶ H^n(K^•)`. -/
theorem inducedCohomologyFiltration_obj (K : FilteredComplex 𝒜) (n p : ℤ) :
    (K.inducedCohomologyFiltration n).obj p = imageSubobject (K.cohomologyMap p n) := rfl

end CohomologyFiltration

end FilteredComplex

/-- Chapter `15` source-facing vocabulary: a filtered cochain complex is the same owner object as
the chapter-level filtered complex. This stable abbreviation is kept because it is used
pervasively downstream when the cochain-complex viewpoint is primary. -/
abbrev FilteredCochainComplex (𝒜 : Type u) [Category.{v} 𝒜] [HasZeroMorphisms 𝒜] :=
  FilteredComplex 𝒜

namespace FilteredCochainComplex

/-- Bridge/view layer: forget the source-facing name and return the canonical owner object from
Chapter `12`. -/
abbrev toFilteredComplex {𝒜 : Type u} [Category.{v} 𝒜] [HasZeroMorphisms 𝒜]
    (K : FilteredCochainComplex 𝒜) : FilteredComplex 𝒜 :=
  K

/-- Bridge/view layer: forget the filtration on a filtered cochain complex. -/
abbrev underlying {𝒜 : Type u} [Category.{v} 𝒜] [HasZeroMorphisms 𝒜]
    (K : FilteredCochainComplex 𝒜) : CochainComplex 𝒜 ℤ :=
  FilteredComplex.underlying K

/-- Bridge/view layer: evaluate a filtered cochain complex at the `p`-th filtration stage. -/
abbrev stage {𝒜 : Type u} [Category.{v} 𝒜] [HasZeroMorphisms 𝒜]
    (K : FilteredCochainComplex 𝒜) (p : ℤ) : CochainComplex 𝒜 ℤ :=
  FilteredComplex.stage K p

/-- Bridge/view layer: the canonical inclusion of the `p`-th stage into the underlying cochain
complex. -/
abbrev stageInclusion {𝒜 : Type u} [Category.{v} 𝒜] [HasZeroMorphisms 𝒜]
    (K : FilteredCochainComplex 𝒜) (p : ℤ) : K.stage p ⟶ K.underlying :=
  FilteredComplex.stageInclusion K p

/-- Bridge/view layer: the canonical comparison map `F^q K^• ⟶ F^p K^•` for `p ≤ q`. -/
abbrev stageMapOfLE {𝒜 : Type u} [Category.{v} 𝒜] [HasZeroMorphisms 𝒜]
    (K : FilteredCochainComplex 𝒜) {p q : ℤ} (hpq : p ≤ q) : K.stage q ⟶ K.stage p :=
  FilteredComplex.stageMapOfLE K hpq

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [HasZeroMorphisms 𝒜] [HasCokernels 𝒜]

/-- Bridge/view layer: the `p`-th graded-piece cochain complex of a filtered cochain complex. -/
noncomputable abbrev gradedPiece (K : FilteredCochainComplex 𝒜) (p : ℤ) :
    CochainComplex 𝒜 ℤ :=
  FilteredComplex.gradedPiece K p

end

end FilteredCochainComplex

end CategoryTheory

/-! ### Lemma_12_24_6 (from Chap12) -/
open CategoryTheory
open CategoryTheory.Limits
open scoped SpectralSequence

noncomputable section

universe v u

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

namespace CohomologicalSpectralSequence

variable [LocallySmall 𝒜] [WellPowered 𝒜] [HasWidePullbacks 𝒜] [HasCoproducts 𝒜]
  [InitialMonoClass 𝒜]

/-- Lemma 12.24.6 (1): in every bidegree, the limit term is the quotient
`E_∞^{p,q} = Z_∞^{p,q} / B_∞^{p,q}`. -/
theorem infinityPage_def
    (E : CohomologicalSpectralSequence 𝒜 0) (pq : ℤ × ℤ) :
    (E.toPageOneSpectralSequence).infinityPage pq =
      cokernel
        (Subobject.ofLE
          ((E.toPageOneSpectralSequence).boundaryInfinity pq)
          ((E.toPageOneSpectralSequence).cycleInfinity pq)
          ((E.toPageOneSpectralSequence).boundaryInfinity_le_cycleInfinity pq)) := by
  simpa using
    SpectralSequence.infinityPage_def E.toPageOneSpectralSequence pq

end CohomologicalSpectralSequence

namespace FilteredComplex

variable [LocallySmall 𝒜] [WellPowered 𝒜] [HasWidePullbacks 𝒜] [HasCoproducts 𝒜]
  [InitialMonoClass 𝒜]

/-
Domain-style sampling for Lemma `12.24.6` in the filtered-complex layer.
- primary domain: the `E_∞`-comparison between the induced cohomology filtration and the infinity
  page of an associated cohomological spectral sequence;
- sampled owner declarations:
  `FilteredComplex.inducedCohomologyFiltration`,
  `SpectralSequence.infinityPage`,
  `IsAssociatedToFilteredComplex`,
  `CategoryTheory.IsSubquotient`;
- best owner abstraction:
  the graded piece of `K.inducedCohomologyFiltration n` and the canonical infinity-page object
  `(E.toPageOneSpectralSequence).infinityPage (p, n - p)`;
- primitive data: a filtered complex `K`, an associated spectral sequence `E`, and the indices
  `n`, `p`;
- derived API: the source-facing subquotient comparison below;
- source/core/bridge triage:
  `source-facing`: `cohomologyGradedPiece_isSubquotient_limitTerm`;
  `core/canonical`: `inducedCohomologyFiltration`, `infinityPage`,
    `IsAssociatedToFilteredComplex`;
  `bridge/view`: the subquotient comparison induced by the always-true inclusions
    `(12.24.6.2)` and `(12.24.6.1)`.

The weak-convergence equalities belong to the stronger isomorphism criterion of
`FilteredComplex.weaklyConvergesToCohomology_iff`; they are not primitive input for the
unconditional subquotient statement here. -/

/-- Lemma 12.24.6 (2): for an associated cohomological spectral sequence, the always-true
inclusions `(12.24.6.2)` and `(12.24.6.1)` make the graded piece `gr^p H^n(K^•)` of the induced
cohomology filtration a subquotient of the antidiagonal limit term `E_∞^{p,n-p}`. -/
theorem cohomologyGradedPiece_isSubquotient_limitTerm
    (K : FilteredComplex 𝒜) (E : CohomologicalSpectralSequence 𝒜 0)
    [IsAssociatedToFilteredComplex K E]
    (n p : ℤ) :
    IsSubquotient ((K.inducedCohomologyFiltration n).gradedPiece p)
      ((E.toPageOneSpectralSequence).infinityPage (p, n - p)) := sorry

end FilteredComplex

end CategoryTheory

/-! ### Definition_12_24_7 (from Chap12) -/
open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory
namespace CohomologicalSpectralSequence

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] {r₀ : ℤ}

/- Definition 12.24.7 stays in the source-facing property layer for the canonical owner
`CohomologicalSpectralSequence 𝒜 r₀`.
Sampled domain declarations:
- `CategoryTheory.CohomologicalSpectralSequence`;
- `CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageX`;
- `CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageD`;
- `CategoryTheory.FilteredComplex.convergesToCohomology`.
Best owner abstraction: the mathlib owner `CategoryTheory.CohomologicalSpectralSequence 𝒜 r₀`.
Primitive data here are only the owner pages and their differentials. The source-facing predicates
below are stated directly from that owner data. The derived set
`initialPageAntidiagonalSupport` is only a bridge/view of that owner data, not a second owner.
Source/core/bridge triage:
- `source-facing`: `IsRegular`, `IsCoregular`, `IsBounded`, `IsBoundedBelow`, `IsBoundedAbove`;
- `core/canonical`: `CohomologicalSpectralSequence 𝒜 r₀`;
- `bridge/view`: `initialPageAntidiagonalSupport` and its order-boundedness reformulations on each
  initial-page antidiagonal. -/

/-- The support on the initial-page antidiagonal of total degree `n`. -/
def initialPageAntidiagonalSupport (E : CohomologicalSpectralSequence 𝒜 r₀) (n : ℤ) : Set ℤ :=
  { p : ℤ | ¬ IsZero ((E.page r₀).X (p, n - p)) }

/-- Definition 12.24.7 (1): a cohomological spectral sequence is regular if for every bidegree
`(p,q)` there is a page after which all outgoing differentials
`d_r^{p,q} : E_r^{p,q} ⟶ E_r^{p+r,q-r+1}` vanish. -/
def IsRegular (E : CohomologicalSpectralSequence 𝒜 r₀) : Prop :=
  ∀ p q : ℤ, ∃ b : ℤ, ∀ ⦃r : ℤ⦄ (hr : r₀ ≤ r), b ≤ r →
    (E.page r).d (p, q) (p + r, q - r + 1) = 0

/-- Definition 12.24.7 (2): a cohomological spectral sequence is coregular if for every bidegree
`(p,q)` there is a page after which all incoming differentials
`d_r^{p-r,q+r-1} : E_r^{p-r,q+r-1} ⟶ E_r^{p,q}` vanish. -/
def IsCoregular (E : CohomologicalSpectralSequence 𝒜 r₀) : Prop :=
  ∀ p q : ℤ, ∃ b : ℤ, ∀ ⦃r : ℤ⦄ (hr : r₀ ≤ r), b ≤ r →
    (E.page r).d (p - r, q + r - 1) (p, q) = 0

/-- Definition 12.24.7 (3): a cohomological spectral sequence is bounded if on each total degree
`n` only finitely many entries `E_{r₀}^{p,n-p}` on the initial page are nonzero. -/
def IsBounded (E : CohomologicalSpectralSequence 𝒜 r₀) : Prop :=
  ∀ n : ℤ, (E.initialPageAntidiagonalSupport n).Finite

/-- Definition 12.24.7 (4): a cohomological spectral sequence is bounded below if on each total
degree `n` the initial-page support on the antidiagonal `p + q = n` is bounded above;
equivalently, the entries `E_{r₀}^{p,n-p}` vanish for all sufficiently large `p`. -/
def IsBoundedBelow (E : CohomologicalSpectralSequence 𝒜 r₀) : Prop :=
  ∀ n : ℤ, ∃ b : ℤ, ∀ ⦃p : ℤ⦄, b ≤ p → IsZero ((E.page r₀).X (p, n - p))

/-- Definition 12.24.7 (5): a cohomological spectral sequence is bounded above if on each total
degree `n` the initial-page support on the antidiagonal `p + q = n` is bounded below;
equivalently, the entries `E_{r₀}^{p,n-p}` vanish for all sufficiently small `p`. -/
def IsBoundedAbove (E : CohomologicalSpectralSequence 𝒜 r₀) : Prop :=
  ∀ n : ℤ, ∃ b : ℤ, ∀ ⦃p : ℤ⦄, p ≤ b → IsZero ((E.page r₀).X (p, n - p))

/-- The support-boundedness reformulation of `IsBoundedBelow`: on each total degree `n`, the
initial-page antidiagonal support is bounded above exactly when the initial entries vanish for all
sufficiently large `p`. -/
theorem isBoundedBelow_iff_bddAbove
    (E : CohomologicalSpectralSequence 𝒜 r₀) :
    IsBoundedBelow E ↔
      ∀ n : ℤ, BddAbove (E.initialPageAntidiagonalSupport n) := by
  constructor
  · intro hE n
    have hE' : ∀ n : ℤ, ∃ b : ℤ, ∀ ⦃p : ℤ⦄, b ≤ p → IsZero ((E.page r₀).X (p, n - p)) := by
      simpa [IsBoundedBelow] using hE
    rcases hE' n with ⟨b, hb⟩
    refine bddAbove_def.mpr ⟨b - 1, ?_⟩
    intro p hp
    have hmem : ¬ IsZero ((E.page r₀).X (p, n - p)) := hp
    by_contra hp'
    have : b ≤ p := by omega
    exact hmem (hb this)
  · intro hE n
    rcases bddAbove_def.mp (hE n) with ⟨b, hb⟩
    refine ⟨b + 1, ?_⟩
    intro p hp
    by_contra hzero
    have hp' : p ∈ E.initialPageAntidiagonalSupport n := by
      simpa using hzero
    have : p ≤ b := hb p hp'
    omega

/-- The support-boundedness reformulation of `IsBoundedAbove`: on each total degree `n`, the
initial-page antidiagonal support is bounded below exactly when the initial entries vanish for all
sufficiently small `p`. -/
theorem isBoundedAbove_iff_bddBelow
    (E : CohomologicalSpectralSequence 𝒜 r₀) :
    IsBoundedAbove E ↔
      ∀ n : ℤ, BddBelow (E.initialPageAntidiagonalSupport n) := by
  constructor
  · intro hE n
    have hE' : ∀ n : ℤ, ∃ b : ℤ, ∀ ⦃p : ℤ⦄, p ≤ b → IsZero ((E.page r₀).X (p, n - p)) := by
      simpa [IsBoundedAbove] using hE
    rcases hE' n with ⟨b, hb⟩
    refine bddBelow_def.mpr ⟨b + 1, ?_⟩
    intro p hp
    have hmem : ¬ IsZero ((E.page r₀).X (p, n - p)) := hp
    by_contra hp'
    have : p ≤ b := by omega
    exact hmem (hb this)
  · intro hE n
    rcases bddBelow_def.mp (hE n) with ⟨b, hb⟩
    refine ⟨b - 1, ?_⟩
    intro p hp
    by_contra hzero
    have hp' : p ∈ E.initialPageAntidiagonalSupport n := by
      simpa using hzero
    have : b ≤ p := hb p hp'
    omega

end CohomologicalSpectralSequence
end CategoryTheory

/-! ### Lemma_12_24_8 (from Chap12) -/
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory
namespace CohomologicalSpectralSequence

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] {r₀ : ℤ}

/- Domain-style sampling for Lemma 12.24.8:
- primary domain: regularity/coregularity and boundedness for cohomological spectral sequences;
- sampled owner declarations:
  `CategoryTheory.CohomologicalSpectralSequence`,
  `CategoryTheory.SpectralSequence.cycle`,
  `CategoryTheory.SpectralSequence.boundary`,
  `CategoryTheory.CohomologicalSpectralSequence.IsRegular`,
  `CategoryTheory.CohomologicalSpectralSequence.IsCoregular`;
- best owner abstraction: the canonical owner `CohomologicalSpectralSequence 𝒜 r₀`, together with
  its page-`E_{r₀}` reindexing to the chapter owner `SpectralSequence.cycle`/`boundary`;
- primitive data: the owner pages `(E.page r).X (p, q)`, their differentials `(E.page r).d`, and
  the page-to-page isomorphisms `E.iso`;
- derived API in this file: the source-facing recursive pieces `Z_r^{p,q}` and `B_r^{p,q}` on the
  initial page, the stabilization characterizations of regularity/coregularity, and the boundedness
  implications.
Source/core/bridge triage:
- `source-facing`: the recursive pieces `cycle`, `boundary` and the predicates `IsRegular`,
  `IsCoregular`, `IsBounded`, `IsBoundedBelow`, `IsBoundedAbove`;
- `core/canonical`: the spectral sequence `E : CohomologicalSpectralSequence 𝒜 r₀`;
- `bridge/view`: the reindexing `toInitialPageSpectralSequence` from the initial page `E_{r₀}` to
  the page-`E₁` owner used by `SpectralSequence.cycle` and `SpectralSequence.boundary`. -/

/-- Bridge/view layer: reindex a cohomological spectral sequence from its initial page `E_{r₀}`
as a page-`E₁` spectral sequence so that the canonical recursive pieces `Z_r` and `B_r` are
reused from `SpectralSequence.cycle` and `SpectralSequence.boundary` instead of being duplicated
locally. -/
abbrev toInitialPageSpectralSequence (E : CohomologicalSpectralSequence 𝒜 r₀) :
    SpectralSequence 𝒜
      (fun r ↦ ComplexShape.up' (⟨r₀ + r - 1, 1 - (r₀ + r - 1)⟩ : ℤ × ℤ)) 1 where
  page r hr := E.page (r₀ + r - 1) (by omega)
  iso r r' pq hrr' hr := by
    simpa using E.iso (r₀ + r - 1) (r₀ + r' - 1) pq (by omega) (by omega)

/-- The page-`E₁` owner index corresponding to the actual page number `r ≥ r₀`. -/
private def initialPageNumber (r₀ r : ℤ) (hr : r₀ ≤ r) : ℕ+ :=
  ⟨Int.toNat (r - r₀ + 1), by omega⟩

/-- The source-facing cycle piece `Z_r^{p,q}` on the initial-page entry corresponding to
`E_{r₀}^{p,q}` under the canonical reindexing to a page-`E₁` spectral sequence. -/
abbrev cycle (E : CohomologicalSpectralSequence 𝒜 r₀) (pq : ℤ × ℤ)
    (r : ℤ) (hr : r₀ ≤ r) :=
  E.toInitialPageSpectralSequence.cycle pq (initialPageNumber r₀ r hr)

/-- The source-facing boundary piece `B_r^{p,q}` on the initial-page entry corresponding to
`E_{r₀}^{p,q}` under the canonical reindexing to a page-`E₁` spectral sequence. -/
abbrev boundary (E : CohomologicalSpectralSequence 𝒜 r₀) (pq : ℤ × ℤ)
    (r : ℤ) (hr : r₀ ≤ r) :=
  E.toInitialPageSpectralSequence.boundary pq (initialPageNumber r₀ r hr)

/-- Lemma 12.24.8 (1): a cohomological spectral sequence is regular exactly when, for every
bidegree `(p,q)`, the source-facing cycle pieces `Z_r^{p,q}` eventually stabilize. -/
theorem isRegular_iff_eventually_cycle_eq
    (E : CohomologicalSpectralSequence 𝒜 r₀) :
    IsRegular E ↔
      ∀ p q : ℤ, ∃ b : ℤ, ∀ ⦃r : ℤ⦄ (hr : r₀ ≤ r), b ≤ r →
        E.cycle (p, q) r hr = E.cycle (p, q) (r + 1) (by omega) := by
  sorry

/-- Lemma 12.24.8 (2): a cohomological spectral sequence is coregular exactly when, for every
bidegree `(p,q)`, the source-facing boundary pieces `B_r^{p,q}` eventually stabilize. -/
theorem isCoregular_iff_eventually_boundary_eq
    (E : CohomologicalSpectralSequence 𝒜 r₀) :
    IsCoregular E ↔
      ∀ p q : ℤ, ∃ b : ℤ, ∀ ⦃r : ℤ⦄ (hr : r₀ ≤ r), b ≤ r →
        E.boundary (p, q) r hr = E.boundary (p, q) (r + 1) (by omega) := by
  sorry

section

variable (E : CohomologicalSpectralSequence 𝒜 r₀)

-- Proof sketch: boundedness on each initial antidiagonal is equivalent to having both an upper and
-- a lower eventual vanishing bound on that antidiagonal; translate between the finite-support
-- condition of `IsBounded` and the two one-sided eventual-vanishing conditions.
/-- Lemma 12.24.8 (3): a cohomological spectral sequence is bounded exactly when it is both
bounded below and bounded above. -/
theorem isBounded_iff_isBoundedBelow_and_isBoundedAbove :
    IsBounded E ↔ IsBoundedBelow E ∧ IsBoundedAbove E := by
  constructor
  · intro hE
    refine ⟨(isBoundedBelow_iff_bddAbove E).2 ?_, (isBoundedAbove_iff_bddBelow E).2 ?_⟩
    · intro n
      exact (Set.finite_iff_bddBelow_bddAbove.mp (hE n)).2
    · intro n
      exact (Set.finite_iff_bddBelow_bddAbove.mp (hE n)).1
  · rintro ⟨hbelow, habove⟩ n
    exact (Set.finite_iff_bddBelow_bddAbove.2
      ⟨((isBoundedAbove_iff_bddBelow E).1 habove) n,
        ((isBoundedBelow_iff_bddAbove E).1 hbelow) n⟩)

-- Proof sketch: the page transition isomorphism identifies `E_{s+1}^{p,q}` with the homology of
-- the short complex extracted from the `s`th page, so vanishing of `E_s^{p,q}` forces vanishing
-- of the same bidegree on every later page by induction.
/-- If an entry on the initial page is zero, then the corresponding entry on every later page is
zero. -/
theorem isZero_pageObj_of_isZero_initialPageObj
    {pq : ℤ × ℤ} {r : ℤ}
    (h₀ : IsZero ((E.page r₀).X pq)) (hr : r₀ ≤ r) :
    IsZero ((E.page r).X pq) := by
  induction r, hr using Int.le_induction with
  | base =>
      exact h₀
  | succ s hs hsZero =>
      let c : ComplexShape (ℤ × ℤ) := ComplexShape.up' (⟨s, 1 - s⟩ : ℤ × ℤ)
      refine IsZero.of_iso ?_ (E.iso s (s + 1) pq).symm
      simpa [HomologicalComplex.homology] using
        (ShortComplex.isZero_homology_of_isZero_X₂
          ((E.page s).sc' (c.prev pq) pq (c.next pq))
          hsZero)

-- Proof sketch: if the initial page is eventually zero for large `p` on each antidiagonal, then
-- for fixed `(p,q)` the outgoing targets `E_r^{p + r, q - r + 1}` are zero for all sufficiently
-- large `r`, so the outgoing differentials vanish and the spectral sequence is regular.
/-- Lemma 12.24.8 (4): a bounded-below cohomological spectral sequence is regular. -/
theorem isRegular_of_isBoundedBelow
    (hE : IsBoundedBelow E) : IsRegular E := by
  intro p q
  rcases hE (p + q + 1) with ⟨b, hb⟩
  refine ⟨b - p, ?_⟩
  intro r hr hbr
  have hp : b ≤ p + r := by
    omega
  have hq : p + q + 1 - (p + r) = q - r + 1 := by
    omega
  have h₀ : IsZero ((E.page r₀).X (p + r, q - r + 1)) := by
    simpa [hq] using hb hp
  have hzero : IsZero ((E.page r).X (p + r, q - r + 1)) :=
    isZero_pageObj_of_isZero_initialPageObj E h₀ hr
  exact hzero.eq_zero_of_tgt _

-- Proof sketch: if the initial page is eventually zero for small `p` on each antidiagonal, then
-- for fixed `(p,q)` the sources `E_r^{p - r, q + r - 1}` of the incoming differentials are zero
-- for all sufficiently large `r`, so those differentials vanish and the spectral sequence is
-- coregular.
/-- Lemma 12.24.8 (5): a bounded-above cohomological spectral sequence is coregular. -/
theorem isCoregular_of_isBoundedAbove
    (hE : IsBoundedAbove E) : IsCoregular E := by
  intro p q
  rcases hE (p + q - 1) with ⟨b, hb⟩
  refine ⟨p - b, ?_⟩
  intro r hr hbr
  have hp : p - r ≤ b := by
    omega
  have hq : p + q - 1 - (p - r) = q + r - 1 := by
    omega
  have h₀ : IsZero ((E.page r₀).X (p - r, q + r - 1)) := by
    simpa [hq] using hb hp
  have hzero : IsZero ((E.page r).X (p - r, q + r - 1)) :=
    isZero_pageObj_of_isZero_initialPageObj E h₀ hr
  exact hzero.eq_zero_of_src _

end

end CohomologicalSpectralSequence
end CategoryTheory
