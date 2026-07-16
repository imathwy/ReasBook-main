import Mathlib
import stacks_proof.stacks_project.Chap12.Definition_12_24_9
import stacks_proof.stacks_project.Chap12.Lemma_12_24_11
import stacks_proof.stacks_project.Chap13.Remark_13_26_15
import stacks_proof.stacks_project.Chap15.Lemma_15_92_22
import stacks_proof.stacks_project.Chap15.Remark_15_92_11

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe u

attribute [local instance] HasDerivedCategory.standard

namespace DerivedCategory

section

variable {A : Type u} [CommRing A]
variable [LocallySmall.{0} (ModuleCat A)] [WellPowered.{0} (ModuleCat A)]
variable [HasWidePullbacks (ModuleCat A)] [HasCoproducts (ModuleCat A)]
variable [InitialMonoClass (ModuleCat A)]

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat A)
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)

/- Domain-style sampling for Example `15.92.23`.
- primary domain: cohomological spectral sequences in `ModuleCat A` computing the cohomology of
  the derived completion of an object of `D(A)`;
- sampled owner/canonical declarations in this domain:
  `CohomologicalSpectralSequence`,
  `CohomologicalSpectralSequence.IsBounded`,
  `FilteredComplex.convergesToCohomology`,
  `DerivedCategory.derivedCompletionOf`;
- best owner abstraction: the cohomological spectral sequence
  `E : CohomologicalSpectralSequence (ModuleCat A) 0`, with the Chapter `12` convergence owner
  `F.convergesToCohomology E` on an associated filtered complex `F`;
- primitive data: only `E` and the auxiliary filtered-complex witness `F` occurring in the
  convergence clause;
- derived API: the `E₂`-page identification, pagewise derived-completeness, and the abutment
  identification with `H^*(K^∧)`;
- source/core/bridge triage:
  `source-facing`: `ConvergesToDerivedCompletionCohomology` and
    `IsDerivedCompletionCohomologySpectralSequence`;
  `core/canonical`: `CohomologicalSpectralSequence`,
    `CohomologicalSpectralSequence.IsBounded`,
    `FilteredComplex.convergesToCohomology`, and `DerivedCategory.derivedCompletionOf`;
  `bridge/view`: the auxiliary filtered complex in the convergence clause together with the
    internal page-two and abutment abbreviations. -/

/-- The `E₂`-term `H^i((H^j(K)[0])^∧)` of Example `15.92.23`. -/
private abbrev derivedCompletionCohomologyPageTwo
    (I : Ideal A) (hI : I.FG) (K : DMod) (i j : ℤ) : ModuleCat A :=
  (H i).obj (((single₀).obj ((H j).obj K))^∧[I, hI])

/-- The abutment term `H^n(K^∧)` of Example `15.92.23`. -/
private abbrev derivedCompletionCohomologyAbutment
    (I : Ideal A) (hI : I.FG) (K : DMod) (n : ℤ) : ModuleCat A :=
  (H n).obj (K^∧[I, hI])

/-- A cohomological spectral sequence converges to the derived-completion cohomology of `K` if it
is associated to a filtered complex whose cohomology identifies with `H^*(K^∧)` and which
satisfies the Chapter `12` convergence owner. -/
def ConvergesToDerivedCompletionCohomology
    (E : CohomologicalSpectralSequence (ModuleCat A) 0)
    (I : Ideal A) (hI : I.FG) (K : DMod) : Prop :=
  ∃ (F : FilteredComplex (ModuleCat A)) (_ : IsAssociatedToFilteredComplex F E),
    F.convergesToCohomology E ∧
      ∀ n : ℤ,
        Nonempty (F.underlying.homology n ≅ derivedCompletionCohomologyAbutment I hI K n)

/-- A cohomological spectral sequence over `ModuleCat A` is a derived-completion cohomology
spectral sequence for `K ∈ D(A)` if it is bounded, every page `E_r` for `r ≥ 2` consists of
modules that are derived complete with respect to `I`, its `E₂`-page is
`H^i((H^j(K)[0])^∧)`, and it converges to `H^{i + j}(K^∧)`. -/
def IsDerivedCompletionCohomologySpectralSequence
    (E : CohomologicalSpectralSequence (ModuleCat A) 0)
    (I : Ideal A) (hI : I.FG) (K : DMod) : Prop :=
  CohomologicalSpectralSequence.IsBounded E ∧
    (∀ i j : ℤ,
      Nonempty ((E.page 2).X (i, j) ≅ derivedCompletionCohomologyPageTwo I hI K i j)) ∧
    (∀ r : ℕ, 2 ≤ r → ∀ i j : ℤ,
      ((E.page r).X (i, j)).IsDerivedCompleteWithRespectTo I) ∧
    ConvergesToDerivedCompletionCohomology E I hI K

/-- A derived-completion cohomology spectral sequence is bounded. -/
theorem IsDerivedCompletionCohomologySpectralSequence.isBounded
    {E : CohomologicalSpectralSequence (ModuleCat A) 0}
    {I : Ideal A} {hI : I.FG} {K : DMod}
    (hE : IsDerivedCompletionCohomologySpectralSequence E I hI K) :
    CohomologicalSpectralSequence.IsBounded E :=
  hE.1

/-- The second page of a derived-completion cohomology spectral sequence computes the cohomology
of the derived completions of the cohomology modules of `K`. -/
theorem IsDerivedCompletionCohomologySpectralSequence.pageTwoIso
    {E : CohomologicalSpectralSequence (ModuleCat A) 0}
    {I : Ideal A} {hI : I.FG} {K : DMod}
    (hE : IsDerivedCompletionCohomologySpectralSequence E I hI K)
    (i j : ℤ) :
    Nonempty ((E.page 2).X (i, j) ≅ (H i).obj (((single₀).obj ((H j).obj K))^∧[I, hI])) :=
  hE.2.1 i j

/-- Every page from `E₂` onward of a derived-completion cohomology spectral sequence consists of
modules that are derived complete with respect to `I`. -/
theorem IsDerivedCompletionCohomologySpectralSequence.page_isDerivedComplete
    {E : CohomologicalSpectralSequence (ModuleCat A) 0}
    {I : Ideal A} {hI : I.FG} {K : DMod}
    (hE : IsDerivedCompletionCohomologySpectralSequence E I hI K)
    (r : ℕ) (hr : 2 ≤ r) (i j : ℤ) :
    ((E.page r).X (i, j)).IsDerivedCompleteWithRespectTo I :=
  hE.2.2.1 r hr i j

/-- A derived-completion cohomology spectral sequence converges to the cohomology of the derived
completion of `K`. -/
theorem IsDerivedCompletionCohomologySpectralSequence.converges
    {E : CohomologicalSpectralSequence (ModuleCat A) 0}
    {I : Ideal A} {hI : I.FG} {K : DMod}
    (hE : IsDerivedCompletionCohomologySpectralSequence E I hI K) :
    ConvergesToDerivedCompletionCohomology E I hI K :=
  hE.2.2.2

/-- Helper for Example 15.92.23: a chosen abutment comparison for an associated filtered complex
packages directly into the convergence predicate for derived-completion cohomology. -/
private theorem convergesToDerivedCompletionCohomology_of_data
    {E : CohomologicalSpectralSequence (ModuleCat A) 0}
    {F : FilteredComplex (ModuleCat A)}
    (I : Ideal A) (hI : I.FG) (K : DMod)
    [IsAssociatedToFilteredComplex F E]
    (hconv : F.convergesToCohomology E)
    (habutment : ∀ n : ℤ,
      Nonempty (F.underlying.homology n ≅ derivedCompletionCohomologyAbutment I hI K n)) :
    ConvergesToDerivedCompletionCohomology E I hI K := by
  -- The convergence predicate is exactly the filtered-complex convergence witness plus the chosen
  -- abutment identifications.
  refine ⟨F, inferInstance, hconv, ?_⟩
  intro n
  exact habutment n

/-- Helper for Example 15.92.23: once boundedness, the `E₂`-page identification, pagewise
derived-completeness, and the abutment package are available, the target predicate is just their
conjunction. -/
private theorem isDerivedCompletionCohomologySpectralSequence_of_data
    {E : CohomologicalSpectralSequence (ModuleCat A) 0}
    {I : Ideal A} {hI : I.FG} {K : DMod}
    (hbounded : CohomologicalSpectralSequence.IsBounded E)
    (hpageTwo : ∀ i j : ℤ,
      Nonempty ((E.page 2).X (i, j) ≅ derivedCompletionCohomologyPageTwo I hI K i j))
    (hcomplete : ∀ r : ℕ, 2 ≤ r → ∀ i j : ℤ,
      ((E.page r).X (i, j)).IsDerivedCompleteWithRespectTo I)
    (hconv : ConvergesToDerivedCompletionCohomology E I hI K) :
    IsDerivedCompletionCohomologySpectralSequence E I hI K := by
  -- The target owner is a four-field conjunction, so we package the verified components directly.
  exact ⟨hbounded, hpageTwo, hcomplete, hconv⟩

/-- Helper for Example 15.92.23: the source filtration is the canonical truncation filtration
`F^p = τ_{\le -p}` on the chosen cochain-complex representative of `K`. -/
private abbrev truncationFilteredPreimage (K : DMod) : FilteredCochainComplex (ModuleCat A) :=
  (DerivedCategory.Q.objPreimage K).truncationFiltration

/-- Helper for Example 15.92.23: the truncation filtration on `DerivedCategory.Q.objPreimage K`
has finite filtrations in every degree. -/
private theorem truncationFilteredPreimage_hasFiniteFiltrations (K : DMod) :
    (truncationFilteredPreimage K).HasFiniteFiltrations := by
  -- This is exactly the Chapter `13` finite-filtration result for the truncation filtration.
  simpa [truncationFilteredPreimage] using
    (CochainComplex.truncationFiltration_hasFiniteFiltrations
      (DerivedCategory.Q.objPreimage K))

/-- Helper for Example 15.92.23: applying Lemma `15.92.22` to the canonical truncation filtration
on `DerivedCategory.Q.objPreimage K` produces the unrenumbered source spectral sequence together
with its boundedness, convergence, page-one formula, and abutment comparison. -/
private theorem exists_associatedSpectralSequence_of_truncationFilteredPreimage
    (I : Ideal A) (hI : I.FG) (K : DMod) :
    ∃ (E : CohomologicalSpectralSequence (ModuleCat A) 0)
      (F : FilteredComplex (ModuleCat A))
      (_ : IsAssociatedToFilteredComplex F E)
      (pageOneIso : ∀ p q : ℤ,
        (E.page 1).X (p, q) ≅
          (H (p + q)).obj
            (((DerivedCategory.Q).obj (gr^{p} truncationFilteredPreimage K))^∧[I, hI]))
      (targetIso : ∀ n : ℤ,
        F.underlying.homology n ≅ derivedCompletionCohomologyAbutment I hI K n),
      (∀ r : ℕ, 1 ≤ r → ∀ p q : ℤ,
        ((E.page r).X (p, q)).IsDerivedCompleteWithRespectTo I) ∧
      CohomologicalSpectralSequence.IsBounded E ∧
      F.convergesToCohomology E := by
  -- Apply Lemma `15.92.22` to the source-faithful truncation filtration.
  obtain ⟨E, F, hAssoc, hpageOne, htarget, hcomplete, hfinite⟩ :=
    exists_derivedCompletion_associatedSpectralSequence I hI (truncationFilteredPreimage K)
  -- The Chapter `13` finiteness theorem upgrades the returned package to boundedness and
  -- convergence.
  obtain ⟨hbounded, hconv⟩ :=
    hfinite (truncationFilteredPreimage_hasFiniteFiltrations K)
  refine ⟨E, F, hAssoc, ?_, ?_, hcomplete, hbounded, hconv⟩
  · intro p q
    simpa [truncationFilteredPreimage] using hpageOne p q
  · intro n
    -- Transport the abutment from the chosen `Q.objPreimage` model back to `K`.
    simpa [derivedCompletionCohomologyAbutment, truncationFilteredPreimage] using
      (htarget n ≪≫
        (H n).mapIso
          ((DerivedCategory.derivedCompletion I hI).mapIso
            (DerivedCategory.Q.objObjPreimageIso K)))

/-- Helper for Example 15.92.23: each stage of the truncation filtration on the chosen preimage
complex is canonically the corresponding upper truncation `τ_{\le -p}`. -/
private theorem truncationFilteredPreimage_stage_factors_ιTruncLE
    (K : DMod) (p : ℤ) :
    ∃ φ : (truncationFilteredPreimage K).stage p ⟶
        (DerivedCategory.Q.objPreimage K).truncLE (-p),
      φ ≫ (DerivedCategory.Q.objPreimage K).ιTruncLE (-p) =
        (truncationFilteredPreimage K).stageInclusion p ∧ IsIso φ := by
  -- This is exactly the truncation-stage identification from Remark `13.26.15` specialized to
  -- the canonical preimage complex representing `K`.
  simpa [truncationFilteredPreimage] using
    (CochainComplex.truncationFiltration_stageInclusion_factors_ιTruncLE
      (DerivedCategory.Q.objPreimage K) p)

/-- Helper for Example 15.92.23: choose the canonical stage comparison
`F^p(Q.objPreimage K) ≅ τ_{\le -p}(Q.objPreimage K)`. -/
private noncomputable def truncationFilteredPreimage_stageIsoTruncLE
    (K : DMod) (p : ℤ) :
    (truncationFilteredPreimage K).stage p ≅
      (DerivedCategory.Q.objPreimage K).truncLE (-p) :=
  let φ := Classical.choose (truncationFilteredPreimage_stage_factors_ιTruncLE K p)
  letI : IsIso φ := (Classical.choose_spec (truncationFilteredPreimage_stage_factors_ιTruncLE K p)).2
  asIso φ

/-- Helper for Example 15.92.23: the chosen stage comparison factors the filtration inclusion
through `ιTruncLE` on the nose. -/
private theorem truncationFilteredPreimage_stageIsoTruncLE_hom_comp_ιTruncLE
    (K : DMod) (p : ℤ) :
    (truncationFilteredPreimage_stageIsoTruncLE K p).hom ≫
        (DerivedCategory.Q.objPreimage K).ιTruncLE (-p) =
      (truncationFilteredPreimage K).stageInclusion p := by
  -- Unpack the chosen factorization of the stage inclusion.
  exact (Classical.choose_spec (truncationFilteredPreimage_stage_factors_ιTruncLE K p)).1

/-- Helper for Example 15.92.23: the adjacent map `τ_{\le j - 1} ⟶ τ_{\le j}` on the chosen
preimage complex is obtained by the standard one-step truncation comparison. -/
private theorem preimageTruncLEStep_isStrictlyLE
    (K : DMod) (j : ℤ) :
    ((DerivedCategory.Q.objPreimage K).truncLE (j - 1)).IsStrictlyLE j := by
  -- The object `τ_{\le j - 1}` is already strictly bounded above in degree `j - 1`, hence also
  -- in degree `j`.
  exact
    ((DerivedCategory.Q.objPreimage K).truncLE (j - 1)).isStrictlyLE_of_le (j - 1) j (by omega)

/-- Helper for Example 15.92.23: the canonical one-step upper-truncation map
`τ_{\le j - 1}(Q.objPreimage K) ⟶ τ_{\le j}(Q.objPreimage K)`. -/
private noncomputable def preimageTruncLEStep
    (K : DMod) (j : ℤ) :
    (DerivedCategory.Q.objPreimage K).truncLE (j - 1) ⟶
      (DerivedCategory.Q.objPreimage K).truncLE j :=
  letI := preimageTruncLEStep_isStrictlyLE K j
  inv (((DerivedCategory.Q.objPreimage K).truncLE (j - 1)).ιTruncLE j) ≫
    CochainComplex.truncLEMap ((DerivedCategory.Q.objPreimage K).ιTruncLE (j - 1)) j

/-- Helper for Example 15.92.23: the one-step upper-truncation map composes with `ιTruncLE j` to
the earlier inclusion `ιTruncLE (j - 1)`. -/
private theorem preimageTruncLEStep_comp_ιTruncLE
    (K : DMod) (j : ℤ) :
    preimageTruncLEStep K j ≫ (DerivedCategory.Q.objPreimage K).ιTruncLE j =
      (DerivedCategory.Q.objPreimage K).ιTruncLE (j - 1) := by
  -- Rewrite the textbook one-step map by the naturality square for `ιTruncLE`, then cancel the
  -- inserted inverse.
  dsimp [preimageTruncLEStep]
  rw [Category.assoc,
    (CochainComplex.ιTruncLE_naturality
      ((DerivedCategory.Q.objPreimage K).ιTruncLE (j - 1)) j).symm]
  simp [Category.assoc]

/-- Helper for Example 15.92.23: after identifying the two neighboring filtration stages with
`τ_{\le j - 1}` and `τ_{\le j}`, the stage map becomes the canonical one-step truncation map. -/
private theorem truncationFilteredPreimage_stageMap_comp_stageIsoTruncLE
    (K : DMod) (j : ℤ) :
    (truncationFilteredPreimage K).stageMapOfLE (show -j ≤ -j + 1 by omega) ≫
        (truncationFilteredPreimage_stageIsoTruncLE K (-j)).hom =
      (truncationFilteredPreimage_stageIsoTruncLE K (-j + 1)).hom ≫
        preimageTruncLEStep K j := by
  -- Compare both morphisms after postcomposing with `ιTruncLE j`; the source side is the
  -- filtration compatibility square, and the target side is the one-step truncation factorization.
  apply (cancel_mono ((DerivedCategory.Q.objPreimage K).ιTruncLE j)).1
  calc
    ((truncationFilteredPreimage K).stageMapOfLE (show -j ≤ -j + 1 by omega) ≫
        (truncationFilteredPreimage_stageIsoTruncLE K (-j)).hom) ≫
          (DerivedCategory.Q.objPreimage K).ιTruncLE j
      = (truncationFilteredPreimage K).stageMapOfLE (show -j ≤ -j + 1 by omega) ≫
          (truncationFilteredPreimage K).stageInclusion (-j) := by
            rw [Category.assoc,
              truncationFilteredPreimage_stageIsoTruncLE_hom_comp_ιTruncLE]
    _ = (truncationFilteredPreimage K).stageInclusion (-j + 1) := by
      simpa using
        (FilteredComplex.stageMapOfLE_comp_stageInclusion
          (K := truncationFilteredPreimage K) (p := -j) (q := -j + 1) (by omega))
    _ = (truncationFilteredPreimage_stageIsoTruncLE K (-j + 1)).hom ≫
          (DerivedCategory.Q.objPreimage K).ιTruncLE (j - 1) := by
            rw [truncationFilteredPreimage_stageIsoTruncLE_hom_comp_ιTruncLE]
            simp
    _ = ((truncationFilteredPreimage_stageIsoTruncLE K (-j + 1)).hom ≫
          preimageTruncLEStep K j) ≫ (DerivedCategory.Q.objPreimage K).ιTruncLE j := by
            rw [Category.assoc, preimageTruncLEStep_comp_ιTruncLE]

/-- Helper for Example 15.92.23: fixing the second index `q` turns the `E₁`-page into an ordinary
cochain complex in the first index. -/
private def associatedPageOneComplex
    (E : CohomologicalSpectralSequence (ModuleCat A) 0) (q : ℤ) :
    CochainComplex (ModuleCat A) ℤ where
  X p := (E.page 1).X (p, q)
  d p p' := (E.page 1).d (p, q) (p', q)
  shape p p' hpp' := by
    -- Fixing `q` rewrites the ambient bidegree shape to the ordinary cochain shape in `p`.
    have hpq :
        ¬ (ComplexShape.up' (⟨(1 : ℤ), 0⟩ : ℤ × ℤ)).Rel (p, q) (p', q) := by
      simpa [ComplexShape.up'] using hpp'
    exact (E.page 1).shape (p, q) (p', q) hpq
  d_comp_d' p p' p'' hpp' hp'p'' := by
    -- The square-zero relation is inherited verbatim from the ambient `E₁` page.
    exact (E.page 1).d_comp_d (p, q) (p', q) (p'', q)

/-- Helper for Example 15.92.23: the short-complex view of the fixed-`q` `E₁`-slice agrees with
the ambient short complex at bidegree `(p, q)`. -/
private noncomputable def associatedPageOneComplexScIso
    (E : CohomologicalSpectralSequence (ModuleCat A) 0) (p q : ℤ) :
    (associatedPageOneComplex E q).sc' (p - 1) p (p + 1) ≅
      (E.page 1).sc' (p - 1, q) (p, q) (p + 1, q) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [associatedPageOneComplex])
    (by simp [associatedPageOneComplex])

/-- Helper for Example 15.92.23: the `p`-th homology of the fixed-`q` `E₁`-slice is the ambient
page-one homology object at bidegree `(p, q)`. -/
private noncomputable def associatedPageOneComplex_homologyIso
    (E : CohomologicalSpectralSequence (ModuleCat A) 0) (p q : ℤ) :
    (associatedPageOneComplex E q).homology p ≅ (E.page 1).homology (p, q) :=
  let hprevSlice : (ComplexShape.up ℤ).prev p = p - 1 :=
    ComplexShape.prev_eq' (ComplexShape.up ℤ) (by simp [ComplexShape.up, ComplexShape.up'])
  let hnextSlice : (ComplexShape.up ℤ).next p = p + 1 :=
    ComplexShape.next_eq' (ComplexShape.up ℤ) (by simp [ComplexShape.up, ComplexShape.up'])
  let hprevPage :
      (ComplexShape.up' (⟨(1 : ℤ), 0⟩ : ℤ × ℤ)).prev (p, q) = (p - 1, q) :=
    ComplexShape.prev_eq' (ComplexShape.up' (⟨(1 : ℤ), 0⟩ : ℤ × ℤ))
      (by simp [ComplexShape.up'])
  let hnextPage :
      (ComplexShape.up' (⟨(1 : ℤ), 0⟩ : ℤ × ℤ)).next (p, q) = (p + 1, q) :=
    ComplexShape.next_eq' (ComplexShape.up' (⟨(1 : ℤ), 0⟩ : ℤ × ℤ))
      (by simp [ComplexShape.up'])
  -- The fixed-`q` slice keeps exactly the same differential data as the ambient page-one complex.
  (associatedPageOneComplex E q).homologyIsoSc' (p - 1) p (p + 1) hprevSlice hnextSlice ≪≫
    ShortComplex.homologyMapIso (associatedPageOneComplexScIso E p q) ≪≫
    ((E.page 1).homologyIsoSc' (p - 1, q) (p, q) (p + 1, q) hprevPage hnextPage).symm

/-- Helper for Example 15.92.23: any comparison between a fixed-`q` `E₁`-slice and an ordinary
cochain complex yields the corresponding `E₂`-page identification by taking `p`-th homology. -/
private theorem associated_pageTwo_iso_of_pageOne_complex_iso
    (E : CohomologicalSpectralSequence (ModuleCat A) 0) (p q : ℤ)
    (C : CochainComplex (ModuleCat A) ℤ)
    (e : associatedPageOneComplex E q ≅ C) :
    Nonempty ((E.page 2).X (p, q) ≅ C.homology p) := by
  refine ⟨?_⟩
  -- First identify the ambient `E₂` term with page-one homology, then transport through the
  -- fixed-`q` slice and the chosen complex comparison.
  exact
    (E.iso 1 2 (p, q)).symm ≪≫
      (associatedPageOneComplex_homologyIso E p q).symm ≪≫
        HomologicalComplex.homologyMapIso e p

/-- Helper for Example 15.92.23: after identifying the adjacent truncation-filtration stages with
`τ_{\le j - 1}` and `τ_{\le j}`, the graded piece `gr^{-j}` is the cokernel of the canonical
one-step truncation map on the chosen preimage complex. -/
private theorem qobj_gradedPiece_truncationFilteredPreimage_iso_qobj_cokernel_preimageTruncLEStep
    (K : DMod) (j : ℤ) :
    Nonempty ((DerivedCategory.Q).obj (gr^{-j} truncationFilteredPreimage K) ≅
      (DerivedCategory.Q).obj (cokernel (preimageTruncLEStep K j))) := by
  have hle : -j ≤ -j + 1 := by
    omega
  let eCokernel :
      gr^{-j} truncationFilteredPreimage K ≅ cokernel (preimageTruncLEStep K j) := by
    -- The graded piece is the cokernel of the stage map, and `cokernel.mapIso` rewrites that
    -- map through the chosen identifications with adjacent upper truncations.
    simpa [FilteredComplex.gradedPiece, DecreasingFiltration.gradedPiece] using
      (cokernel.mapIso
        ((truncationFilteredPreimage K).stageMapOfLE hle)
        (preimageTruncLEStep K j)
        (truncationFilteredPreimage_stageIsoTruncLE K (-j + 1))
        (truncationFilteredPreimage_stageIsoTruncLE K (-j))
        (truncationFilteredPreimage_stageMap_comp_stageIsoTruncLE K j))
  -- Apply the quotient functor to the concrete cokernel comparison.
  exact ⟨DerivedCategory.Q.mapIso eCokernel⟩

/-- Helper for Example 15.92.23: the raw page-one term at coordinates `(-j, i + 2j)` can already
be rewritten using the concrete truncation-step cokernel model of `gr^{-j}`. -/
private theorem raw_pageOne_iso_qobj_cokernel_preimageTruncLEStep
    (I : Ideal A) (hI : I.FG) (K : DMod)
    {S : CohomologicalSpectralSequence (ModuleCat A) 0}
    (hpageOne : ∀ p q : ℤ,
      (S.page 1).X (p, q) ≅
        (H (p + q)).obj
          (((DerivedCategory.Q).obj (gr^{p} truncationFilteredPreimage K))^∧[I, hI]))
    (i j : ℤ) :
    Nonempty ((S.page 1).X (-j, i + 2 * j) ≅
      (H (i + j)).obj
        (((DerivedCategory.Q).obj (cokernel (preimageTruncLEStep K j)))^∧[I, hI])) := by
  obtain ⟨eGraded⟩ :=
    qobj_gradedPiece_truncationFilteredPreimage_iso_qobj_cokernel_preimageTruncLEStep K j
  refine ⟨?_⟩
  -- First normalize the index arithmetic in the raw page-one formula, then transport the
  -- graded-piece term along the concrete cokernel identification.
  exact
    (by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (hpageOne (-j) (i + 2 * j))) ≪≫
      (H (i + j)).mapIso ((DerivedCategory.derivedCompletion I hI).mapIso eGraded)

/-- Helper for Example 15.92.23: truncating `τ_{\le j}(Q.objPreimage K)` once more at `j - 1`
gives the standard short exact sequence whose third term is the cokernel of that one-step upper
truncation map. -/
private theorem truncLE_step_shortExact_on_upper_stage
    (K : DMod) (j : ℤ) :
    (((DerivedCategory.Q.objPreimage K).truncLE j).shortComplexTruncLE (j - 1)).ShortExact := by
  -- The adjacent truncation sequence is already packaged by the canonical cochain-complex owner.
  simpa using
    (((DerivedCategory.Q.objPreimage K).truncLE j).shortComplexTruncLE_shortExact (j - 1))

/-- Helper for Example 15.92.23: the cokernel term in the one-step truncation short exact
sequence of `τ_{\le j}(Q.objPreimage K)` is quasi-isomorphic to the upper truncation piece
`τ_{\ge j}(τ_{\le j}(Q.objPreimage K))`. -/
private theorem truncLE_step_cokernel_quasiIso_truncGE_stage
    (K : DMod) (j : ℤ) :
    QuasiIso
      (((DerivedCategory.Q.objPreimage K).truncLE j).shortComplexTruncLEX₃ToTruncGE
        (j - 1) j (by omega)) :=
  -- The comparison from the short-exact-sequence cokernel to the upper truncation piece is the
  -- canonical complementary-truncation quasi-isomorphism.
  inferInstance

/-- Helper for Example 15.92.23: the owner truncation-step short exact sequence on
`τ_{\le j}(Q.objPreimage K)` uses the canonical inclusion
`τ_{\le j - 1}(τ_{\le j}(Q.objPreimage K)) ⟶ τ_{\le j}(Q.objPreimage K)` as its first
morphism. -/
private theorem truncLE_step_shortExact_on_upper_stage_f_eq
    (K : DMod) (j : ℤ) :
    (((DerivedCategory.Q.objPreimage K).truncLE j).shortComplexTruncLE (j - 1)).f =
      (((DerivedCategory.Q.objPreimage K).truncLE j).ιTruncLE (j - 1)) := by
  -- Unfolding the owner short complex shows that its first morphism is literally `ιTruncLE`.
  rfl

/-- Helper for Example 15.92.23: after applying the quotient functor, the owner truncation-step
cokernel is canonically the upper truncation piece
`τ_{\ge j}(τ_{\le j}(Q.objPreimage K))`. -/
private theorem qobj_truncLE_step_owner_cokernel_iso_truncGE_stage
    (K : DMod) (j : ℤ) :
    Nonempty
      ((DerivedCategory.Q).obj
          (((((DerivedCategory.Q.objPreimage K).truncLE j).shortComplexTruncLE
              (j - 1))).X₃) ≅
        (DerivedCategory.Q).obj
          (((DerivedCategory.Q.objPreimage K).truncLE j).truncGE j)) := by
  -- Apply `Q` to the owner quasi-isomorphism from the short-exact-sequence cokernel to the
  -- complementary upper truncation piece.
  refine ⟨asIso (DerivedCategory.Q.map ?_)⟩
  exact
    (((DerivedCategory.Q.objPreimage K).truncLE j).shortComplexTruncLEX₃ToTruncGE
      (j - 1) j (by omega))

/-- Helper for Example 15.92.23: the concrete cokernel of the adjacent upper-truncation map
represents the canonical shifted cohomology object `H^j(K)[-j]` in the derived category. -/
private theorem qobj_cokernel_preimageTruncLEStep_iso_shiftedCohomology
    (K : DMod) (j : ℤ) :
    Nonempty ((DerivedCategory.Q).obj (cokernel (preimageTruncLEStep K j)) ≅
      shiftedCohomology (ModuleCat A) K j) := by
  -- TODO: compare the short exact sequence
  -- `0 → τ_{\le j - 1}(Q.objPreimage K) → τ_{\le j}(Q.objPreimage K) → cokernel(step) → 0`
  -- with the canonical short exact sequence on `τ_{\le j}(Q.objPreimage K)` supplied by
  -- `truncLE_step_shortExact_on_upper_stage` and the quasi-isomorphism
  -- `truncLE_step_cokernel_quasiIso_truncGE_stage`. The remaining blocker is the explicit
  -- comparison between `preimageTruncLEStep K j` and the transported short-exact-sequence map so
  -- that `DerivedCategory.triangleOfSES.map` can be applied and the third vertex identified with
  -- `_root_.truncLE_step_termIso K (j - 1)`.
  sorry

/-- Helper for Example 15.92.23: after commuting derived completion past the shift hidden in
`shiftedCohomology`, the degree `i + j` homology becomes the displayed degree `i` page-two term.
-/
private theorem shiftedCohomology_completion_homology_iso_pageTwo
    (I : Ideal A) (hI : I.FG) (K : DMod) (i j : ℤ) :
    Nonempty ((H (i + j)).obj ((shiftedCohomology (ModuleCat A) K j)^∧[I, hI]) ≅
      derivedCompletionCohomologyPageTwo I hI K i j) := by
  refine ⟨?_⟩
  let eShiftedSingle :
      ((shiftedCohomology (ModuleCat A) K j)⟦j⟧) ≅ (single₀).obj ((H j).obj K) := by
    -- Rewrite the source-faithful shifted cohomology object as the degree-zero single object.
    simpa [shiftedCohomology] using
      (((DerivedCategory.singleFunctors (ModuleCat A)).shiftIso j 0 j (by simp)).app
        ((H j).obj K))
  let eCompletedShift :
      (((shiftedCohomology (ModuleCat A) K j)^∧[I, hI])⟦j⟧) ≅
        (((single₀).obj ((H j).obj K))^∧[I, hI]) :=
    -- First commute derived completion past the shift, then replace the shifted single object by
    -- the degree-zero single object.
    (((DerivedCategory.derivedCompletion I hI).commShiftIso j).app
      (shiftedCohomology (ModuleCat A) K j)).symm ≪≫
      (DerivedCategory.derivedCompletion I hI).mapIso eShiftedSingle
  let eHomologyShift :
      (H (i + j)).obj ((shiftedCohomology (ModuleCat A) K j)^∧[I, hI]) ≅
        (H i).obj ((((shiftedCohomology (ModuleCat A) K j)^∧[I, hI])⟦j⟧)) :=
    -- Reindex the homology degree across the shift by `j`.
    (((H 0).shiftIso j i (i + j) (add_comm j i)).app
      ((shiftedCohomology (ModuleCat A) K j)^∧[I, hI])).symm
  -- Compose the homology-of-shift comparison with the completed shift identification.
  exact eHomologyShift ≪≫ (H i).mapIso eCompletedShift

/-- Helper for Example 15.92.23: after replacing the concrete truncation-step cokernel by the
canonical shifted cohomology object, the raw page-one term is exactly the displayed page-two term
`H^i((H^j(K)[0])^∧)`. -/
private theorem raw_pageOne_iso_derivedCompletionCohomologyPageTwo
    (I : Ideal A) (hI : I.FG) (K : DMod)
    {S : CohomologicalSpectralSequence (ModuleCat A) 0}
    (hpageOne : ∀ p q : ℤ,
      (S.page 1).X (p, q) ≅
        (H (p + q)).obj
          (((DerivedCategory.Q).obj (gr^{p} truncationFilteredPreimage K))^∧[I, hI]))
    (i j : ℤ) :
    Nonempty ((S.page 1).X (-j, i + 2 * j) ≅
      derivedCompletionCohomologyPageTwo I hI K i j) := by
  obtain ⟨ePageOne⟩ :=
    raw_pageOne_iso_qobj_cokernel_preimageTruncLEStep I hI K hpageOne i j
  obtain ⟨eShifted⟩ :=
    qobj_cokernel_preimageTruncLEStep_iso_shiftedCohomology K j
  obtain ⟨ePageTwo⟩ :=
    shiftedCohomology_completion_homology_iso_pageTwo I hI K i j
  refine ⟨?_⟩
  -- Transport the raw page-one identification across the concrete cokernel-to-shifted-cohomology
  -- comparison, then normalize the shifted completed homology to the displayed page-two term.
  exact
    ePageOne ≪≫
      (H (i + j)).mapIso ((DerivedCategory.derivedCompletion I hI).mapIso eShifted) ≪≫
        ePageTwo

/-- Helper for Example 15.92.23: the linear change of variables
`(i, j) ↦ (-j, i + 2j)` turns the page-`r - 1` cohomological shape into the page-`r` shape. -/
private theorem neg_swap_rel_iff
    (r i j i' j' : ℤ) :
    (ComplexShape.up' (⟨r - 1, 2 - r⟩ : ℤ × ℤ)).Rel (-j, i + 2 * j) (-j', i' + 2 * j') ↔
      (ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)).Rel (i, j) (i', j') := by
  -- The coordinate transform was chosen so that the old differential of bidegree
  -- `(r - 1, -r + 2)` becomes the new cohomological bidegree `(r, -r + 1)`.
  simp [ComplexShape.up']
  omega

/-- Helper for Example 15.92.23: for each positive page `r`, the renumbered positive-page object
has entries `S_{r-1}^{-j, i + 2j}` and the same differentials in the transformed coordinates. -/
private def renumberedPositivePage
    (S : CohomologicalSpectralSequence (ModuleCat A) 0) (r : ℤ) (hr : 1 ≤ r) :
    HomologicalComplex (ModuleCat A)
      (ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)) where
  X pq := (S.page (r - 1) (by omega)).X (-pq.2, pq.1 + 2 * pq.2)
  d pq pq' := (S.page (r - 1) (by omega)).d (-pq.2, pq.1 + 2 * pq.2) (-pq'.2, pq'.1 + 2 * pq'.2)
  shape pq pq' hpq := by
    -- Rewrite the transformed source and target bidegrees back to the original page.
    apply (S.page (r - 1) (by omega)).shape
    intro hrel
    exact hpq ((neg_swap_rel_iff r pq.1 pq.2 pq'.1 pq'.2).1 hrel)
  d_comp_d' pq pq' pq'' hpq hpq' := by
    -- After the coordinate change, square-zero is inherited verbatim from the old page.
    exact
      (S.page (r - 1) (by omega)).d_comp_d
        (-pq.2, pq.1 + 2 * pq.2)
        (-pq'.2, pq'.1 + 2 * pq'.2)
        (-pq''.2, pq''.1 + 2 * pq''.2)

/-- Helper for Example 15.92.23: after the neg-swap coordinate change, the displayed `E'_2` term
is already the raw page-one term of the source spectral sequence. -/
private theorem renumbered_pageTwo_iso_of_raw_pageOne_neg_swap
    (I : Ideal A) (hI : I.FG) (K : DMod)
    {S : CohomologicalSpectralSequence (ModuleCat A) 0}
    (hpageTwo : ∀ i j : ℤ,
      Nonempty ((S.page 1).X (-j, i + 2 * j) ≅
        derivedCompletionCohomologyPageTwo I hI K i j))
    (i j : ℤ) :
    Nonempty (((renumberedPositivePage S 2 (by omega)).X (i, j)) ≅
      derivedCompletionCohomologyPageTwo I hI K i j) := by
  -- The affine coordinate change at page `r = 2` is definitionally the old page `1`.
  simpa [renumberedPositivePage] using hpageTwo i j

/-- Helper for Example 15.92.23: the remaining owner-level renumbering step is to package the
positive-page transport `E'_r^{i,j} = S_{r-1}^{-j, i + 2j}` as an actual cohomological spectral
sequence with an associated filtered-complex witness. -/
private theorem exists_renumbered_from_raw_pageOne_neg_swap
    (I : Ideal A) (hI : I.FG) (K : DMod)
    {S : CohomologicalSpectralSequence (ModuleCat A) 0}
    {F : FilteredComplex (ModuleCat A)}
    [IsAssociatedToFilteredComplex F S]
    (hpageTwo : ∀ i j : ℤ,
      Nonempty ((S.page 1).X (-j, i + 2 * j) ≅
        derivedCompletionCohomologyPageTwo I hI K i j))
    (hcomplete : ∀ r : ℕ, 1 ≤ r → ∀ p q : ℤ,
      ((S.page r).X (p, q)).IsDerivedCompleteWithRespectTo I)
    (hbounded : CohomologicalSpectralSequence.IsBounded S)
    (hconv : F.convergesToCohomology S)
    (habutment : ∀ n : ℤ,
      Nonempty (F.underlying.homology n ≅ derivedCompletionCohomologyAbutment I hI K n)) :
    ∃ (E : CohomologicalSpectralSequence (ModuleCat A) 0)
      (F' : FilteredComplex (ModuleCat A))
      (_ : IsAssociatedToFilteredComplex F' E),
      (∀ i j : ℤ,
        Nonempty ((E.page 2).X (i, j) ≅ derivedCompletionCohomologyPageTwo I hI K i j)) ∧
      (∀ r : ℕ, 2 ≤ r → ∀ i j : ℤ,
        ((E.page r).X (i, j)).IsDerivedCompleteWithRespectTo I) ∧
      CohomologicalSpectralSequence.IsBounded E ∧
      F'.convergesToCohomology E ∧
      (∀ n : ℤ,
        Nonempty (F'.underlying.homology n ≅ derivedCompletionCohomologyAbutment I hI K n)) := by
  -- TODO: use the shifted-exact-couple/page-zero-extension bridge to turn the positive-page
  -- transport isolated by `renumberedPositivePage` into an owner-level spectral sequence starting
  -- at page `0`. The renumbered `E'_2` identification is already isolated by
  -- `renumbered_pageTwo_iso_of_raw_pageOne_neg_swap`; the remaining blocker is the owner-level
  -- page-zero extension producing an associated filtered complex and the page-one/previous-page
  -- homology comparison required by Remark `12.22.6` (Variant), not the coordinate arithmetic on
  -- the positive pages.
  let _ := hpageTwo
  let _ := hcomplete
  let _ := hbounded
  let _ := hconv
  let _ := habutment
  sorry

/-- Helper for Example 15.92.23: the source-faithful renumbering step should produce a
cohomological spectral sequence whose `E₂`-page is `H^i((H^j(K)[0])^∧)` and whose abutment is
`H^{i + j}(K^∧)`. -/
private theorem exists_page_two_shifted_derivedCompletion_spectral_sequence
    (I : Ideal A) (hI : I.FG) (K : DMod) :
    ∃ (E : CohomologicalSpectralSequence (ModuleCat A) 0)
      (F : FilteredComplex (ModuleCat A))
      (_ : IsAssociatedToFilteredComplex F E),
      (∀ i j : ℤ,
        Nonempty ((E.page 2).X (i, j) ≅ derivedCompletionCohomologyPageTwo I hI K i j)) ∧
      (∀ r : ℕ, 2 ≤ r → ∀ i j : ℤ,
        ((E.page r).X (i, j)).IsDerivedCompleteWithRespectTo I) ∧
      CohomologicalSpectralSequence.IsBounded E ∧
      F.convergesToCohomology E ∧
      (∀ n : ℤ,
        Nonempty (F.underlying.homology n ≅ derivedCompletionCohomologyAbutment I hI K n)) := by
  -- Route correction: the proof now factors through two isolated owner-level bridges. First,
  -- rewrite the raw page-one term to the displayed target `H^i((H^j(K)[0])^∧)`. Then package the
  -- coordinate change `E'_r^{i,j} = S_{r-1}^{-j, i + 2j}` with its filtered-complex witness.
  obtain ⟨S, F, hAssoc, hpageOne, habutment, hcomplete, hbounded, hconv⟩ :=
    exists_associatedSpectralSequence_of_truncationFilteredPreimage I hI K
  letI : IsAssociatedToFilteredComplex F S := hAssoc
  have hpageTwo :
      ∀ i j : ℤ,
        Nonempty ((S.page 1).X (-j, i + 2 * j) ≅
          derivedCompletionCohomologyPageTwo I hI K i j) :=
    raw_pageOne_iso_derivedCompletionCohomologyPageTwo I hI K hpageOne
  exact
    exists_renumbered_from_raw_pageOne_neg_swap I hI K hpageTwo hcomplete hbounded hconv
      (fun n ↦ habutment n)

-- Proof sketch: apply Lemma `15.92.22` to the filtration `F^p K = τ_{≤ -p} K`, identify the
-- graded piece `gr^p(K)` with `H^{-p}(K)[p]`, and then renumber by `p = -j` and `q = i + 2j`.
-- The boundedness, derived-completeness of the pages, and convergence to `H^*(K^∧)` are inherited
-- from Lemma `15.92.22` after this reindexing.
/-- Example 15.92.23: for a finitely generated ideal `I ⊆ A` and any object `K ∈ D(A)`, there
is a bounded cohomological spectral sequence of bigraded derived-complete `A`-modules whose
`E_2^{i,j}`-term is `H^i(H^j(K)^∧)` and which converges to `H^{i + j}(K^∧)`. The differentials
are those of a cohomological spectral sequence, so they have bidegree `(r, -r + 1)`. -/
@[stacks 0BKE]
theorem exists_derivedCompletion_cohomology_spectralSequence
    (I : Ideal A) (hI : I.FG) (K : DMod) :
    ∃ E : CohomologicalSpectralSequence (ModuleCat A) 0,
      IsDerivedCompletionCohomologySpectralSequence E I hI K := by
  -- Route correction: isolate the genuinely missing step as the page-shifted reformulation of
  -- Lemma `15.92.22`, and keep the final theorem as pure packaging of that source-faithful data.
  obtain ⟨E, F, hAssoc, hpageTwo, hcomplete, hbounded, hconv, habutment⟩ :=
    exists_page_two_shifted_derivedCompletion_spectral_sequence I hI K
  letI : IsAssociatedToFilteredComplex F E := hAssoc
  -- Once the renumbered spectral-sequence data is chosen, the target statement is immediate.
  refine ⟨E, ?_⟩
  refine isDerivedCompletionCohomologySpectralSequence_of_data
    (I := I) (hI := hI) (K := K) hbounded hpageTwo hcomplete ?_
  exact convergesToDerivedCompletionCohomology_of_data
    (I := I) (hI := hI) (K := K) hconv habutment

end

end DerivedCategory
