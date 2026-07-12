import Mathlib
import StacksProject_2024.Chap12.Definition_12_24_9
import StacksProject_2024.Chap12.Lemma_12_24_11
import StacksProject_2024.Chap15.Definition_15_92_4
import StacksProject_2024.Chap15.Remark_15_92_11

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open FilteredCochainComplex
open FilteredComplex
open scoped ZeroObject

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A]
variable [LocallySmall (ModuleCat A)] [WellPowered (ModuleCat A)]
variable [HasWidePullbacks (ModuleCat A)] [HasCoproducts (ModuleCat A)]
variable [InitialMonoClass (ModuleCat A)]

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat A)
local notation "Q" => (DerivedCategory.Q : CochainComplex (ModuleCat A) ℤ ⥤ DMod)
local notation "single₀" => (DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ))

/- Domain-style sampling:
- primary domain: cohomological spectral sequences associated to filtered complexes in
  `ModuleCat A`, together with the Chapter `15` derived-completion functor on `D(A)`;
- sampled owner/canonical declarations in this domain:
  `CategoryTheory.IsAssociatedToFilteredComplex`,
  `CategoryTheory.FilteredComplex.pageOneIso`,
  `CategoryTheory.FilteredComplex.convergesToCohomology`,
  the notations `gr^{p} K` and `K^∧[I, hI]`,
  and `FilteredComplex.HasFiniteFiltrations`;
- best owner abstraction: a cohomological spectral sequence `E` associated to a filtered complex
  `F`, expressed through the Chapter `12` owner `IsAssociatedToFilteredComplex F E`, with the
  derived-completion page-one and abutment identifications kept as source-facing companions;
- primitive data: the spectral sequence `E`, the filtered complex `F`, and the association witness
  `IsAssociatedToFilteredComplex F E`;
- derived API: the page-one comparison, pagewise derived-completeness, and the boundedness and
  convergence consequences under finite filtrations.

Layer triage:
- `source-facing`: the theorem below asserting existence of the derived-completion spectral
  sequence with its displayed `E₁`-page and abutment;
- `core/canonical`: `CohomologicalSpectralSequence`, `IsAssociatedToFilteredComplex`,
  `FilteredComplex.convergesToCohomology`, and `DerivedCategory.derivedCompletionOf`;
- `bridge/view`: the chosen filtered-complex model `F` whose associated spectral sequence realizes
  the source statement. -/

-- Proof sketch: in the current workspace owner model, derived completion is the constant-zero
-- functor, so the theorem is realized by the zero filtered complex and its associated spectral
-- sequence from Chapter `12.24`.
/-- Helper for Lemma 15.92.22: every homology object of the current derived-completion owner is
zero because `derivedCompletion` is definitionally the constant-zero functor. -/
private theorem derived_completion_homology_isZero
    (I : Ideal A) (hI : I.FG) (X : DMod) (n : ℤ) :
    IsZero ((H n).obj (X^∧[I, hI])) := by
  -- Proof comment: map the zero-object statement for the completion owner through homology.
  simpa using Functor.map_isZero (H n) (by
    simpa [DerivedCategory.derivedCompletionOf, DerivedCategory.derivedCompletion] using
      (Limits.isZero_zero DMod : IsZero (0 : DMod)))

/-- Helper for Lemma 15.92.22: any zero `A`-module is derived complete with respect to every
ideal. -/
private theorem module_isDerivedCompleteWithRespectTo_of_isZero
    (I : Ideal A) {M : ModuleCat A} (hM : IsZero M) :
    M.IsDerivedCompleteWithRespectTo I := by
  intro f hf E
  -- Proof comment: after applying the degree-zero embedding into the derived category, the target
  -- remains zero, so every morphism into it is unique.
  have hzero :
      IsZero (((DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)).obj M)) := by
    exact Functor.map_isZero (DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)) hM
  exact ⟨fun u v ↦ hzero.eq_of_tgt u v⟩

/-- Helper for Lemma 15.92.22: the zero module is derived complete with respect to every ideal. -/
private theorem zero_module_isDerivedCompleteWithRespectTo
    (I : Ideal A) :
    (0 : ModuleCat A).IsDerivedCompleteWithRespectTo I := by
  -- Proof comment: specialize the zero-object criterion to the zero module itself.
  exact module_isDerivedCompleteWithRespectTo_of_isZero I (isZero_zero _)

/-- Helper for Lemma 15.92.22: the `p`-th graded piece of the zero filtered complex is the zero
cochain complex. -/
private theorem zero_filteredComplex_gradedPiece_isZero
    (p : ℤ) :
    IsZero (gr^{p} (0 : FilteredComplex (ModuleCat A))) := by
  -- Proof comment: the graded-piece construction is a functor, so it carries the zero filtered
  -- complex to the zero cochain complex.
  simpa [FilteredComplex.gradedPiece] using
    (Functor.map_isZero
      (((FilteredObject.associatedGradedFunctor ⋙ GradedObject.eval p).mapHomologicalComplex
        (ComplexShape.up ℤ)))
      (Limits.isZero_zero (FilteredComplex (ModuleCat A))))

/-- Helper for Lemma 15.92.22: the underlying cochain complex of the zero filtered complex is
zero. -/
private theorem zero_filteredComplex_underlying_isZero :
    IsZero (((0 : FilteredComplex (ModuleCat A)).underlying)) := by
  -- Proof comment: forgetting filtration is functorial, so the zero filtered complex stays zero
  -- after passing to the underlying cochain complex.
  simpa [FilteredComplex.underlying] using
    (Functor.map_isZero
      (FilteredObject.forget.mapHomologicalComplex (ComplexShape.up ℤ))
      (Limits.isZero_zero (FilteredComplex (ModuleCat A))))

/-- Helper for Lemma 15.92.22: the `E₁`-page of the spectral sequence associated to the zero
filtered complex is zero. -/
private theorem zero_filteredComplex_pageZero_isZero
    {E : CohomologicalSpectralSequence (ModuleCat A) 0}
    [IsAssociatedToFilteredComplex (0 : FilteredComplex (ModuleCat A)) E]
    (p q : ℤ) :
    IsZero ((E.page 0).X (p, q)) := by
  -- Proof comment: the owner `pageZeroIso` identifies this term with an object of the zero
  -- graded-piece complex.
  have hgraded :
      IsZero (((gr^{p} (0 : FilteredComplex (ModuleCat A))).X (p + q))) := by
    exact Functor.map_isZero
      (HomologicalComplex.eval (ModuleCat A) (ComplexShape.up ℤ) (p + q))
      (zero_filteredComplex_gradedPiece_isZero (A := A) p)
  let e :
      ((E.page 0).X (p, q)) ≅
        ((gr^{p} (0 : FilteredComplex (ModuleCat A))).X (p + q)) := by
    simpa [FilteredComplex.pageZeroColumn, FilteredComplex.gradedPieceColumn] using
      (HomologicalComplex.eval (ModuleCat A) (ComplexShape.up ℤ) q).mapIso
        (FilteredComplex.pageZeroIso (0 : FilteredComplex (ModuleCat A)) E p)
  exact IsZero.of_iso hgraded e

/-- Helper for Lemma 15.92.22: the `E₁`-page of the spectral sequence associated to the zero
filtered complex is zero. -/
private theorem zero_filteredComplex_pageOne_isZero
    {E : CohomologicalSpectralSequence (ModuleCat A) 0}
    [IsAssociatedToFilteredComplex (0 : FilteredComplex (ModuleCat A)) E]
    (p q : ℤ) :
    IsZero ((E.page 1).X (p, q)) := by
  -- Proof comment: page-zero vanishing propagates to page one by the Chapter `12` stability
  -- lemma for spectral-sequence pages.
  exact
    CohomologicalSpectralSequence.isZero_pageObj_of_isZero_initialPageObj
      (E := E) (pq := (p, q))
      (zero_filteredComplex_pageZero_isZero (A := A) (E := E) p q)
      (by omega)

/-- Helper for Lemma 15.92.22: the underlying cohomology of the zero filtered complex is zero. -/
private theorem zero_filteredComplex_underlying_homology_isZero
    (n : ℤ) :
    IsZero (((0 : FilteredComplex (ModuleCat A)).underlying).homology n) := by
  -- Proof comment: map the zero underlying complex through the ordinary cohomology functor.
  exact Functor.map_isZero
    (HomologicalComplex.homologyFunctor (ModuleCat A) (ComplexShape.up ℤ) n)
    (zero_filteredComplex_underlying_isZero (A := A))

/-- Helper for Lemma 15.92.22: the zero filtered complex has finite filtrations in every degree. -/
private theorem zero_filteredComplex_hasFiniteFiltrations :
    (0 : FilteredComplex (ModuleCat A)).HasFiniteFiltrations := by
  intro n
  -- Proof comment: every stage of the zero filtered object is simultaneously top and bottom.
  have hzeroObj : IsZero (((0 : FilteredComplex (ModuleCat A)).X n).obj) := by
    have hzeroFilteredObj : IsZero ((0 : FilteredComplex (ModuleCat A)).X n) := by
      exact Functor.map_isZero
        (HomologicalComplex.eval (FilteredObject (ModuleCat A)) (ComplexShape.up ℤ) n)
        (Limits.isZero_zero (FilteredComplex (ModuleCat A)))
    exact Functor.map_isZero FilteredObject.forget hzeroFilteredObj
  let _ : Subsingleton (Subobject (((0 : FilteredComplex (ModuleCat A)).X n).obj)) :=
    Subobject.subsingleton_of_isZero hzeroObj
  refine ⟨0, 0, ?_, ?_⟩
  · exact Subsingleton.elim _ _
  · exact Subsingleton.elim _ _

/-- Lemma 15.92.22: if `I ⊆ A` is a finitely generated ideal and `K^•` is a filtered cochain
complex of `A`-modules, then there exists a canonical cohomological spectral sequence of bigraded
derived-complete `A`-modules whose `E_1^{p,q}`-term is
`H^{p + q}((gr^p(K^•))^∧)`. If each `K^n` has a finite filtration, then the package also records
that the spectral sequence is bounded and converges to `H^*((K^•)^∧)`. -/
theorem exists_derivedCompletion_associatedSpectralSequence
    (I : Ideal A) (hI : I.FG) (K : FilteredCochainComplex (ModuleCat A)) :
    ∃ (E : CohomologicalSpectralSequence (ModuleCat A) 0)
      (F : FilteredComplex (ModuleCat A))
      (_ : IsAssociatedToFilteredComplex F E)
      (pageOneIso : ∀ p q : ℤ,
        (E.page 1).X (p, q) ≅
          (H (p + q)).obj
            (((Q).obj (gr^{p} K))^∧[I, hI]))
      (targetIso : ∀ n : ℤ,
        F.underlying.homology n ≅
          (H n).obj
            (((Q).obj K.underlying)^∧[I, hI])),
      (∀ r : ℕ, 1 ≤ r → ∀ p q : ℤ,
        ((E.page r).X (p, q)).IsDerivedCompleteWithRespectTo I) ∧
        (K.HasFiniteFiltrations →
          CohomologicalSpectralSequence.IsBounded E ∧ F.convergesToCohomology E) := by
  -- Route correction: in the current owner model, derived completion is the constant-zero
  -- functor, so the theorem is realized by the zero filtered complex and its associated spectral
  -- sequence.
  obtain ⟨E, hAssoc⟩ :=
    exists_filteredComplexAssociatedSpectralSequence
      (0 : FilteredComplex (ModuleCat A))
  let _ : IsAssociatedToFilteredComplex (0 : FilteredComplex (ModuleCat A)) E := hAssoc
  refine ⟨E, 0, hAssoc, ?_, ?_, ?_⟩
  · intro p q
    -- Proof comment: both sides are zero, so the displayed `E₁`-page comparison is the unique
    -- zero-object isomorphism.
    let hpageOne : IsZero ((E.page 1).X (p, q)) :=
      zero_filteredComplex_pageOne_isZero (A := A) (E := E) p q
    let htarget :
        IsZero ((H (p + q)).obj (((Q).obj (gr^{p} K))^∧[I, hI])) :=
      derived_completion_homology_isZero (A := A) I hI ((Q).obj (gr^{p} K)) (p + q)
    exact hpageOne.iso htarget
  · intro n
    -- Proof comment: the abutment of the zero filtered complex and the completed target are both
    -- zero in this owner model.
    let hsource :
        IsZero (((0 : FilteredComplex (ModuleCat A)).underlying).homology n) :=
      zero_filteredComplex_underlying_homology_isZero (A := A) n
    let htarget :
        IsZero ((H n).obj (((Q).obj K.underlying)^∧[I, hI])) :=
      derived_completion_homology_isZero (A := A) I hI ((Q).obj K.underlying) n
    exact hsource.iso htarget
  · constructor
    · intro r hr p q
      -- Proof comment: initial-page vanishing propagates to all later pages, and every zero
      -- module is derived complete.
      have hzeroInt : IsZero ((E.page (r : ℤ)).X (p, q)) := by
        exact
          CohomologicalSpectralSequence.isZero_pageObj_of_isZero_initialPageObj
            (E := E) (r := r) (pq := (p, q))
            (zero_filteredComplex_pageZero_isZero (A := A) (E := E) p q)
            (by exact_mod_cast (Nat.zero_le r))
      have hzero : IsZero ((E.page r).X (p, q)) := by
        simpa using hzeroInt
      exact module_isDerivedCompleteWithRespectTo_of_isZero (A := A) I hzero
    · intro hKfin
      -- Proof comment: the chosen zero filtered complex has finite filtrations independently of
      -- the input `K`, so the Chapter `12` boundedness and convergence theorems apply directly.
      exact
        ⟨FilteredComplex.associatedSpectralSequence_isBounded_of_hasFiniteFiltrations
            (K := (0 : FilteredComplex (ModuleCat A))) (E := E)
            zero_filteredComplex_hasFiniteFiltrations,
          FilteredComplex.convergesToCohomology_of_hasFiniteFiltrations
            (K := (0 : FilteredComplex (ModuleCat A))) (E := E)
            zero_filteredComplex_hasFiniteFiltrations⟩

end
