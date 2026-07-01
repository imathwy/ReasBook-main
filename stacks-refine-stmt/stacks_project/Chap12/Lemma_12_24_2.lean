import stacks_project.Chap12.Definition_12_24_5

-- Declarations for this item will be appended below by the statement pipeline.

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
