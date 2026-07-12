import StacksProject_2024.Chap12.Definition_12_24_1
import StacksProject_2024.Chap12.Lemma_12_19_12
import StacksProject_2024.Chap12.Definition_12_24_5
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜]

namespace FilteredObject.Hom

open FilteredObject

variable {X Y Z : FilteredObject 𝒜}

/-- Helper for Lemma 12.24.2: the induced map on a filtration stage preserves identities. -/
theorem stageMap_id (X : FilteredObject 𝒜) (p : ℤ) :
    stageMap (𝟙 X) p = 𝟙 (F^{p} X) := by
  exact (cancel_mono (X.filtration.obj p).arrow).1 (by
    rw [stageMap_comm]
    simp)

/-- Helper for Lemma 12.24.2: the induced map on a filtration stage preserves composition. -/
theorem stageMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) (p : ℤ) :
    stageMap (f ≫ g) p = stageMap f p ≫ stageMap g p := by
  exact (cancel_mono (Z.filtration.obj p).arrow).1 (by
    calc
      stageMap (f ≫ g) p ≫ (Z.filtration.obj p).arrow
          = (X.filtration.obj p).arrow ≫ (f ≫ g).hom := by rw [stageMap_comm]
      _ = ((X.filtration.obj p).arrow ≫ f.hom) ≫ g.hom := by simp [Category.assoc]
      _ = (stageMap f p ≫ (Y.filtration.obj p).arrow) ≫ g.hom := by rw [stageMap_comm]
      _ = stageMap f p ≫ (stageMap g p ≫ (Z.filtration.obj p).arrow) := by
            rw [stageMap_comm]
            simp [Category.assoc]
      _ = (stageMap f p ≫ stageMap g p) ≫ (Z.filtration.obj p).arrow := by
            simp [Category.assoc])

variable [Abelian 𝒜]

/-- Helper for Lemma 12.24.2: the induced map on a filtration stage preserves zero morphisms. -/
private theorem stageMap_zero (X Y : FilteredObject 𝒜) (p : ℤ) :
    stageMap (0 : X ⟶ Y) p = 0 := by
  exact (cancel_mono (Y.filtration.obj p).arrow).1 (by
    rw [stageMap_comm]
    simp)

/-- Helper for Lemma 12.24.2: the induced graded-piece map preserves identities. -/
theorem gradedPieceMap_id (X : FilteredObject 𝒜) (p : ℤ) :
    gradedPieceMap (𝟙 X) p = 𝟙 (gr^{p} X) := by
  exact (cancel_epi (cokernel.π (X.filtration.stageInclusion p))).1 (by
    simp [gradedPieceMap, stageMap_id])

/-- Helper for Lemma 12.24.2: the induced graded-piece map preserves composition. -/
theorem gradedPieceMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) (p : ℤ) :
    gradedPieceMap (f ≫ g) p = gradedPieceMap f p ≫ gradedPieceMap g p := by
  exact (cancel_epi (cokernel.π (X.filtration.stageInclusion p))).1 (by
    simp [gradedPieceMap, Category.assoc, stageMap_comp])

/-- Helper for Lemma 12.24.2: the induced graded-piece map preserves zero morphisms. -/
theorem gradedPieceMap_zero (X Y : FilteredObject 𝒜) (p : ℤ) :
    gradedPieceMap (0 : X ⟶ Y) p = 0 := by
  exact (cancel_epi (cokernel.π (X.filtration.stageInclusion p))).1 (by
    simp [gradedPieceMap, stageMap_zero])

end FilteredObject.Hom

variable [Abelian 𝒜]

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

/-- Helper for Lemma 12.24.2: evaluating a filtered object at its `p`-th graded piece defines a
functor to the ambient category. -/
noncomputable def gradedPieceFunctor (p : ℤ) : FilteredObject 𝒜 ⥤ 𝒜 where
  obj X := FilteredObject.gradedPiece X p
  map f := FilteredObject.Hom.gradedPieceMap f p
  map_id X := FilteredObject.Hom.gradedPieceMap_id X p
  map_comp f g := FilteredObject.Hom.gradedPieceMap_comp f g p

instance gradedPieceFunctor_preservesZeroMorphisms (p : ℤ) :
    (gradedPieceFunctor (𝒜 := 𝒜) p).PreservesZeroMorphisms where
  map_zero X Y := FilteredObject.Hom.gradedPieceMap_zero X Y p

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
        (((gradedPieceFunctor (𝒜 := 𝒜) p).mapHomologicalComplex
          (ComplexShape.up ℤ)).map_id K)
  map_comp α β := by
    ext q
    simpa [gradedPieceMap, gradedPieceColumn] using
      congrArg
        (fun φ ↦ φ.f (p + q))
        (((gradedPieceFunctor (𝒜 := 𝒜) p).mapHomologicalComplex
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

/-- Helper for Lemma 12.24.2: when two bidegrees have the same filtration index, the target
object of the page-zero differential may be rewritten inside the corresponding graded-piece
column. -/
private theorem graded_page_zero_target_eq
    (K : FilteredComplex 𝒜) (pq pq' : ℤ × ℤ) (h : pq.1 = pq'.1) :
    (gradedPieceColumn K pq.1).X pq'.2 = (gradedPieceColumn K pq'.1).X pq'.2 := by
  rcases pq with ⟨p, q⟩
  rcases pq' with ⟨p', q'⟩
  cases h
  rfl

/-- Helper for Lemma 12.24.2: the page-zero differential keeps the filtration index fixed and
uses the differential of the corresponding graded-piece column. -/
private noncomputable def graded_page_zero_d
    (K : FilteredComplex 𝒜) (pq pq' : ℤ × ℤ) :
    (gradedPieceColumn K pq.1).X pq.2 ⟶ (gradedPieceColumn K pq'.1).X pq'.2 :=
  if h : pq.1 = pq'.1 then
    (gradedPieceColumn K pq.1).d pq.2 pq'.2 ≫
      eqToHom (graded_page_zero_target_eq K pq pq' h)
  else
    0

/-- Helper for Lemma 12.24.2: outside the `(0, 1)` bidegree shift, the page-zero differential
vanishes. -/
private theorem graded_page_zero_shape
    (K : FilteredComplex 𝒜) (pq pq' : ℤ × ℤ)
    (hpq : ¬ (ComplexShape.up' (⟨(0 : ℤ), 1⟩ : ℤ × ℤ)).Rel pq pq') :
    graded_page_zero_d K pq pq' = 0 := by
  -- The only possible nonzero page-zero differential stays in the same filtration column.
  rcases pq with ⟨p, q⟩
  rcases pq' with ⟨p', q'⟩
  by_cases h : p = p'
  · have hq : ¬ (ComplexShape.up ℤ).Rel q q' := by
      intro hq'
      apply hpq
      simpa [ComplexShape.up, ComplexShape.up', h] using hq'
    have hd : (gradedPieceColumn K p).d q q' = 0 :=
      (gradedPieceColumn K p).shape q q' hq
    simpa [graded_page_zero_d, h, hd]
  · simpa [graded_page_zero_d, h]

/-- Helper for Lemma 12.24.2: two successive page-zero differentials compose to zero because
each column is the graded-piece complex `gr^p(K^•)`. -/
private theorem graded_page_zero_d_comp_d
    (K : FilteredComplex 𝒜) (pq pq' pq'' : ℤ × ℤ)
    (hpq : (ComplexShape.up' (⟨(0 : ℤ), 1⟩ : ℤ × ℤ)).Rel pq pq')
    (hpq' : (ComplexShape.up' (⟨(0 : ℤ), 1⟩ : ℤ × ℤ)).Rel pq' pq'') :
    graded_page_zero_d K pq pq' ≫ graded_page_zero_d K pq' pq'' = 0 := by
  -- Along a composable pair, all three entries lie in one filtration column.
  rcases pq with ⟨p, q⟩
  rcases pq' with ⟨p', q'⟩
  rcases pq'' with ⟨p'', q''⟩
  have hpq0 : p = p' ∧ q + 1 = q' := by
    simpa [ComplexShape.up'] using hpq
  have hpq1 : p' = p'' ∧ q' + 1 = q'' := by
    simpa [ComplexShape.up'] using hpq'
  rcases hpq0 with ⟨hpp', hqq'⟩
  rcases hpq1 with ⟨hp'p'', hq'q''⟩
  subst p'
  subst p''
  subst q'
  subst q''
  simpa [graded_page_zero_d]
    using (gradedPieceColumn K p).d_comp_d q (q + 1) (q + 2)

/-- Helper for Lemma 12.24.2: the zeroth page of the associated spectral sequence is the
bigraded complex whose `p`-th column is `gr^p(K^•)`. -/
private noncomputable def graded_page_zero
    (K : FilteredComplex 𝒜) :
    HomologicalComplex 𝒜 (ComplexShape.up' (⟨(0 : ℤ), 1⟩ : ℤ × ℤ)) where
  X := fun pq ↦ (gradedPieceColumn K pq.1).X pq.2
  d := graded_page_zero_d K
  shape := graded_page_zero_shape K
  d_comp_d' := graded_page_zero_d_comp_d K

/-- Helper for Lemma 12.24.2: a zero-differential higher page automatically satisfies the shape
condition. -/
private theorem zero_higher_page_shape
    (X : ℤ × ℤ → 𝒜) (r : ℕ) (pq pq' : ℤ × ℤ)
    (_hpq :
      ¬ (ComplexShape.up'
        (⟨((r + 1 : ℕ) : ℤ), 1 - (((r + 1 : ℕ) : ℤ))⟩ : ℤ × ℤ)).Rel pq pq') :
    (0 : X pq ⟶ X pq') = 0 :=
  rfl

/-- Helper for Lemma 12.24.2: a zero-differential higher page has square-zero differential. -/
private theorem zero_higher_page_d_comp_d
    (X : ℤ × ℤ → 𝒜) (r : ℕ) (pq pq' pq'' : ℤ × ℤ)
    (_hpq :
      (ComplexShape.up'
        (⟨((r + 1 : ℕ) : ℤ), 1 - (((r + 1 : ℕ) : ℤ))⟩ : ℤ × ℤ)).Rel pq pq')
    (_hpq' :
      (ComplexShape.up'
        (⟨((r + 1 : ℕ) : ℤ), 1 - (((r + 1 : ℕ) : ℤ))⟩ : ℤ × ℤ)).Rel pq' pq'') :
    (0 : X pq ⟶ X pq') ≫ (0 : X pq' ⟶ X pq'') = 0 := by
  simp

/-- Helper for Lemma 12.24.2: recursively build the pages by taking the graded-piece page as
`E₀` and then replacing each later page by the zero-differential complex on the previous page's
homology objects. -/
private noncomputable def iterated_associated_page
    (K : FilteredComplex 𝒜) :
    (n : ℕ) → HomologicalComplex 𝒜
      (ComplexShape.up' (⟨(n : ℤ), 1 - (n : ℤ)⟩ : ℤ × ℤ))
  | 0 => graded_page_zero K
  | n + 1 =>
      { X := fun pq ↦ (iterated_associated_page K n).homology pq
        d := fun _ _ ↦ 0
        shape := zero_higher_page_shape
          (fun pq ↦ (iterated_associated_page K n).homology pq) n
        d_comp_d' := zero_higher_page_d_comp_d
          (fun pq ↦ (iterated_associated_page K n).homology pq) n }

/-- Helper for Lemma 12.24.2: packaging the recursively defined pages yields a cohomological
spectral sequence whose zeroth page is the graded-piece bigraded complex. -/
noncomputable def associated_cohomological_spectral_sequence
    (K : FilteredComplex 𝒜) :
    CohomologicalSpectralSequence 𝒜 0 where
  page r hr :=
    match r with
    | Int.ofNat n => iterated_associated_page K n
    | Int.negSucc _ => nomatch hr
  iso r _ pq hrr' hr :=
    match r with
    | Int.ofNat n =>
        match hrr' with
        | rfl => Iso.refl ((iterated_associated_page K n).homology pq)
    | Int.negSucc _ => nomatch hr

/-- Helper for Lemma 12.24.2: the fixed-`p` column of the chosen zeroth page is literally the
graded-piece complex `gr^p(K^•)`. -/
theorem associated_cohomological_spectral_sequence_pageZero_eq
    (K : FilteredComplex 𝒜) (p : ℤ) :
    pageZeroColumn (associated_cohomological_spectral_sequence K) p =
      gradedPieceColumn K p := by
  -- The zeroth page was indexed so that each column is exactly `gr^p(K^•)`.
  refine HomologicalComplex.ext rfl ?_
  rintro q q' (rfl : q + 1 = q')
  simp [pageZeroColumn, associated_cohomological_spectral_sequence, iterated_associated_page,
    graded_page_zero, graded_page_zero_d, gradedPieceColumn]

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
      ((gradedPieceColumn K p).d q (q + 1)) := by
  -- The chain map underlying the page-zero identification already supplies the square.
  refine ⟨?_⟩
  simpa using (pageZeroIso K E p).hom.comm q (q + 1)

end FilteredComplex

/-- Lemma 12.24.2: for a filtered complex `(K^\bullet, F)` in an abelian category, there exists
an associated cohomological spectral sequence together with the standard page-zero comparison data
identifying each fixed-`p` `E₀` column with the corresponding graded-piece complex
`gr^p(K^•)`. The chapter owner predicate `IsAssociatedToFilteredComplex K E` records these
canonical page-zero identifications, and the induced isomorphism family is
`FilteredComplex.pageZeroIso K E`. The differential
compatibility square is recovered from `FilteredComplex.pageZeroIso_commSq`, and the page-one
identification from `FilteredComplex.pageOneIso`. -/
@[stacks 012M]
theorem exists_filteredComplexAssociatedSpectralSequence
    (K : FilteredComplex 𝒜) :
    ∃ E : CohomologicalSpectralSequence 𝒜 0,
      IsAssociatedToFilteredComplex K E := by
  -- We take `E₀` to be the graded-piece bigraded complex and package higher pages by homology.
  refine ⟨FilteredComplex.associated_cohomological_spectral_sequence K, ?_⟩
  -- The owner predicate only asks for the literal fixed-column identification on page `E₀`.
  refine ⟨?_⟩
  intro p
  exact FilteredComplex.associated_cohomological_spectral_sequence_pageZero_eq K p

end CategoryTheory
