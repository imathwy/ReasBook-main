import Mathlib
import StacksProject_2024.stacks_project.Chap12.Definition_12_18_3
import StacksProject_2024.stacks_project.Chap12.Definition_12_10_1
import StacksProject_2024.stacks_project.Chap12.Definition_12_24_7
import StacksProject_2024.stacks_project.Chap12.Definition_12_24_9
import StacksProject_2024.stacks_project.Chap12.Lemma_12_24_11

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory ComplexShape
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open scoped HomologicalComplex₂

noncomputable section

universe u v

namespace CategoryTheory

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [HasZeroMorphisms 𝒜]

/-- The finiteness hypothesis on a cohomological double complex: on each total degree `n`, only
finitely many terms `K^{p,n-p}` are nonzero. -/
def doubleComplexHasFiniteAntidiagonalSupport
    (K : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)) : Prop :=
  ∀ n : ℤ, { p : ℤ | ¬ IsZero ((K.X p).X (n - p)) }.Finite

end

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [CategoryWithHomology 𝒜]
  [LocallySmall 𝒜] [WellPowered 𝒜] [HasWidePullbacks 𝒜] [HasCoproducts 𝒜] [InitialMonoClass 𝒜]

local notation "FilteredComplex" => CategoryTheory.FilteredComplex 𝒜

/- Domain-style sampling for Lemma `12.25.3`.
- primary domain: cohomological double complexes, their total complexes, and the two filtered
  complexes realizing the standard first and second filtrations on `Tot(K^{•,•})`;
- sampled owner/canonical declarations in this domain:
  `HomologicalComplex₂.HasTotal`,
  `HomologicalComplex₂.total`,
  `FilteredObject`,
  `FilteredComplex.underlying`,
  `IsAssociatedToFilteredComplex`,
  `FilteredComplex.convergesToCohomology`;
- best owner abstraction: the actual first and second filtered complexes on `Tot(K)`, exposed
  below as `firstDoubleComplexFilteredComplex K` and `secondDoubleComplexFilteredComplex K`;
- primitive data: a double complex `K`, its total complex, and the degreewise filtration stages
  obtained as the images of the partial antidiagonal coproduct maps;
- derived API: finite-filtration consequences from finite antidiagonal support, boundedness of an
  associated spectral sequence, finiteness of the induced cohomology filtration, convergence, and
  the weak-Serre consequence for total cohomology;
- source/core/bridge triage:
  `source-facing`: the finiteness hypothesis on the antidiagonal support and the eight conclusions
    of the lemma, together with the first and second filtrations on `Tot(K)`;
  `core/canonical`: `HomologicalComplex₂.total`, `FilteredComplex.underlying`,
    `IsAssociatedToFilteredComplex`, `CohomologicalSpectralSequence.IsBounded`, and
    `FilteredComplex.convergesToCohomology`;
  `bridge/view`: the degreewise antidiagonal coproduct maps whose images define the filtration
    stages.

The correct public layer here is therefore the actual filtered-complex owners on `Tot(K)`, not a
wrapper predicate around an arbitrary filtered-complex model. -/

private abbrev TailIndices (p : ℤ) := {i : ℤ // p ≤ i}

private noncomputable def firstDoubleComplexFiltrationMap
    (K : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)] (n p : ℤ) :
    ∐ (fun i : TailIndices p ↦ (K.X i.1).X (n - i.1)) ⟶ (Tot(K)).X n :=
  Limits.Sigma.desc fun i : TailIndices p ↦
    K.ιTotal (up ℤ) i.1 (n - i.1) n (by
      change i.1 + (n - i.1) = n
      omega)

private noncomputable def secondDoubleComplexFiltrationMap
    (K : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)] (n p : ℤ) :
    ∐ (fun i : TailIndices p ↦ (K.X (n - i.1)).X i.1) ⟶ (Tot(K)).X n :=
  Limits.Sigma.desc fun i : TailIndices p ↦
    K.ιTotal (up ℤ) (n - i.1) i.1 n (by
      change (n - i.1) + i.1 = n
      omega)

private noncomputable abbrev firstDoubleComplexFiltrationStage
    (K : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)] (n p : ℤ) :
    Subobject ((Tot(K)).X n) :=
  imageSubobject (firstDoubleComplexFiltrationMap K n p)

private noncomputable abbrev secondDoubleComplexFiltrationStage
    (K : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)] (n p : ℤ) :
    Subobject ((Tot(K)).X n) :=
  imageSubobject (secondDoubleComplexFiltrationMap K n p)

/-- Helper for Lemma 12.25.3: increasing the cutoff in the first filtration only removes summands,
so the corresponding image subobject can only decrease. -/
private theorem first_filtration_stage_mono
    (K : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)]
    (n p q : ℤ) (hpq : p ≤ q) :
    firstDoubleComplexFiltrationStage K n q ≤ firstDoubleComplexFiltrationStage K n p := by
  let ι :
      ∐ (fun i : TailIndices q ↦ (K.X i.1).X (n - i.1)) ⟶
        ∐ (fun i : TailIndices p ↦ (K.X i.1).X (n - i.1)) :=
    Limits.Sigma.map' (fun i : TailIndices q ↦ (⟨i.1, hpq.trans i.2⟩ : TailIndices p))
      (fun _ ↦ 𝟙 _)
  have hcomp :
      ι ≫ firstDoubleComplexFiltrationMap K n p = firstDoubleComplexFiltrationMap K n q := by
    -- Compare the two coproduct maps on each tail summand.
    apply Limits.Sigma.hom_ext
    intro i
    cases i with
    | mk i hi =>
      rw [← Category.assoc, Sigma.ι_comp_map', Category.id_comp]
      simp [firstDoubleComplexFiltrationMap, Sigma.ι_desc]
  -- The `q`-tail map factors through the `p`-tail map via the obvious coproduct inclusion.
  simpa [firstDoubleComplexFiltrationStage, hcomp] using
    (Limits.imageSubobject_comp_le ι (firstDoubleComplexFiltrationMap K n p))

/-- Helper for Lemma 12.25.3: increasing the cutoff in the second filtration again removes
summands, so the row-tail image subobject can only decrease. -/
private theorem second_filtration_stage_mono
    (K : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)]
    (n p q : ℤ) (hpq : p ≤ q) :
    secondDoubleComplexFiltrationStage K n q ≤ secondDoubleComplexFiltrationStage K n p := by
  let ι :
      ∐ (fun i : TailIndices q ↦ (K.X (n - i.1)).X i.1) ⟶
        ∐ (fun i : TailIndices p ↦ (K.X (n - i.1)).X i.1) :=
    Limits.Sigma.map' (fun i : TailIndices q ↦ (⟨i.1, hpq.trans i.2⟩ : TailIndices p))
      (fun _ ↦ 𝟙 _)
  have hcomp :
      ι ≫ secondDoubleComplexFiltrationMap K n p = secondDoubleComplexFiltrationMap K n q := by
    -- Compare the two coproduct maps on each tail summand.
    apply Limits.Sigma.hom_ext
    intro i
    cases i with
    | mk i hi =>
      rw [← Category.assoc, Sigma.ι_comp_map', Category.id_comp]
      simp [secondDoubleComplexFiltrationMap, Sigma.ι_desc]
  -- The `q`-tail map factors through the `p`-tail map via the obvious coproduct inclusion.
  simpa [secondDoubleComplexFiltrationStage, hcomp] using
    (Limits.imageSubobject_comp_le ι (secondDoubleComplexFiltrationMap K n p))

private noncomputable def firstDoubleComplexFilteredObject
    (K : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)] (n : ℤ) :
    FilteredObject 𝒜 where
  obj := (Tot(K)).X n
  filtration :=
    { toFun := firstDoubleComplexFiltrationStage K n
      monotone' := by
        intro p q hpq
        -- The first filtration is decreasing because raising the cutoff deletes summands.
        exact first_filtration_stage_mono K n q p hpq }

private noncomputable def secondDoubleComplexFilteredObject
    (K : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)] (n : ℤ) :
    FilteredObject 𝒜 where
  obj := (Tot(K)).X n
  filtration :=
    { toFun := secondDoubleComplexFiltrationStage K n
      monotone' := by
        intro p q hpq
        -- The second filtration is decreasing for the same tail-inclusion reason.
        exact second_filtration_stage_mono K n q p hpq }

/-- The filtered complex on `Tot(K^{\bullet,\bullet})` defined by the first filtration
`F_I^p Tot^n(K) = \operatorname{im}(\bigoplus_{i \ge p} K^{i,n-i} \to Tot^n(K))`. -/
noncomputable def firstDoubleComplexFilteredComplex
    (K : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)] :
    FilteredComplex :=
  { X := firstDoubleComplexFilteredObject K
    d i j :=
      { hom := (Tot(K)).d i j
        preserves := by
          intro p
          sorry }
    shape i j hij := by
      exact FilteredObject.forget.map_injective ((Tot(K)).shape i j hij)
    d_comp_d' i j k hij hjk := by
      exact FilteredObject.forget.map_injective ((Tot(K)).d_comp_d' i j k hij hjk) }

/-- The filtered complex on `Tot(K^{\bullet,\bullet})` defined by the second filtration
`F_{II}^p Tot^n(K) = \operatorname{im}(\bigoplus_{j \ge p} K^{n-j,j} \to Tot^n(K))`. -/
noncomputable def secondDoubleComplexFilteredComplex
    (K : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)] :
    FilteredComplex :=
  { X := secondDoubleComplexFilteredObject K
    d i j :=
      { hom := (Tot(K)).d i j
        preserves := by
          intro p
          sorry }
    shape i j hij := by
      exact FilteredObject.forget.map_injective ((Tot(K)).shape i j hij)
    d_comp_d' i j k hij hjk := by
      exact FilteredObject.forget.map_injective ((Tot(K)).d_comp_d' i j k hij hjk) }

@[simp] theorem firstDoubleComplexFilteredComplex_underlying
    (K : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)] :
    (firstDoubleComplexFilteredComplex K).underlying = Tot(K) := rfl

@[simp] theorem secondDoubleComplexFilteredComplex_underlying
    (K : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)] :
    (secondDoubleComplexFilteredComplex K).underlying = Tot(K) := rfl

-- Proof sketch: on total degree `n`, finite antidiagonal support makes the tail-image filtration
-- on `Tot^n(K)` eventually equal to the whole antidiagonal sum and eventually zero.
/-- Finite antidiagonal support on `K` makes the first filtration on `Tot(K)` finite in each
degree. -/
theorem firstDoubleComplexFilteredComplex_hasFiniteFiltrations_of_finiteAntidiagonalSupport
    (K : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)]
    (hfin : doubleComplexHasFiniteAntidiagonalSupport K) :
    (firstDoubleComplexFilteredComplex K).HasFiniteFiltrations := sorry

-- Proof sketch: the same finite antidiagonal support controls the row-tail filtration defining
-- the second filtration on `Tot(K)`.
/-- Finite antidiagonal support on `K` makes the second filtration on `Tot(K)` finite in each
degree. -/
theorem secondDoubleComplexFilteredComplex_hasFiniteFiltrations_of_finiteAntidiagonalSupport
    (K : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)]
    (hfin : doubleComplexHasFiniteAntidiagonalSupport K) :
    (secondDoubleComplexFilteredComplex K).HasFiniteFiltrations := sorry

-- Proof sketch: finite support on each antidiagonal makes the initial page of the first spectral
-- sequence finite on every total degree, so the associated filtered-complex spectral sequence is
-- bounded by the filtered-complex criterion of Lemma `12.24.11`.
/-- Lemma 12.25.3 (1): if each antidiagonal of the double complex has only finitely many nonzero
terms, then the first spectral sequence associated to `K^{\bullet,\bullet}` is bounded. -/
theorem firstDoubleComplex_associatedSpectralSequence_isBounded_of_finiteAntidiagonalSupport
    (K : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)]
    (E : CohomologicalSpectralSequence 𝒜 0)
    [IsAssociatedToFilteredComplex (firstDoubleComplexFilteredComplex K) E]
    (hfin : doubleComplexHasFiniteAntidiagonalSupport K) :
    CohomologicalSpectralSequence.IsBounded E := by
  -- Lemma `12.24.11` turns finite termwise filtrations into boundedness of any associated page.
  simpa using
    FilteredComplex.associatedSpectralSequence_isBounded_of_hasFiniteFiltrations
      (K := firstDoubleComplexFilteredComplex K) (E := E)
      (firstDoubleComplexFilteredComplex_hasFiniteFiltrations_of_finiteAntidiagonalSupport K hfin)

-- Proof sketch: the same finiteness hypothesis is invariant under exchanging the two indices, so
-- the second spectral sequence is bounded for the identical reason as the first.
/-- Lemma 12.25.3 (2): if each antidiagonal of the double complex has only finitely many nonzero
terms, then the second spectral sequence associated to `K^{\bullet,\bullet}` is bounded. -/
theorem secondDoubleComplex_associatedSpectralSequence_isBounded_of_finiteAntidiagonalSupport
    (K : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)]
    (E : CohomologicalSpectralSequence 𝒜 0)
    [IsAssociatedToFilteredComplex (secondDoubleComplexFilteredComplex K) E]
    (hfin : doubleComplexHasFiniteAntidiagonalSupport K) :
    CohomologicalSpectralSequence.IsBounded E := by
  -- The second spectral sequence is bounded for the identical filtered-complex reason.
  simpa using
    FilteredComplex.associatedSpectralSequence_isBounded_of_hasFiniteFiltrations
      (K := secondDoubleComplexFilteredComplex K) (E := E)
      (secondDoubleComplexFilteredComplex_hasFiniteFiltrations_of_finiteAntidiagonalSupport K hfin)

-- Proof sketch: identify the first filtration `F_I` on `H^n(Tot(K))` with the cohomology
-- filtration induced by the first filtered complex attached to `K`, then apply the finite
-- filtration criterion coming from finite antidiagonal support.
/-- Lemma 12.25.3 (3): under the same finiteness hypothesis, the first filtration `F_I` on each
`H^n(\mathrm{Tot}(K^{\bullet,\bullet}))` is finite. In this file it is recorded by the canonical
filtered-complex owner `firstDoubleComplexFilteredComplex K`. -/
theorem firstDoubleComplex_cohomologyFiltrationIsFinite_of_finiteAntidiagonalSupport
    (K : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)]
    (hfin : doubleComplexHasFiniteAntidiagonalSupport K) :
    (firstDoubleComplexFilteredComplex K).cohomologyFiltrationIsFinite := by
  -- Once the first filtered complex has finite filtrations, the induced cohomology filtration is
  -- finite by Lemma `12.24.11`.
  simpa using
    FilteredComplex.cohomologyFiltrationIsFinite_of_hasFiniteFiltrations
      (K := firstDoubleComplexFilteredComplex K)
      (firstDoubleComplexFilteredComplex_hasFiniteFiltrations_of_finiteAntidiagonalSupport K hfin)

-- Proof sketch: repeat the preceding argument for the second filtration `F_{II}` coming from the
-- second filtered-complex realization of the total complex.
/-- Lemma 12.25.3 (4): under the same finiteness hypothesis, the second filtration `F_{II}` on
each `H^n(\mathrm{Tot}(K^{\bullet,\bullet}))` is finite. In this file it is recorded by the
canonical filtered-complex owner `secondDoubleComplexFilteredComplex K`. -/
theorem secondDoubleComplex_cohomologyFiltrationIsFinite_of_finiteAntidiagonalSupport
    (K : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)]
    (hfin : doubleComplexHasFiniteAntidiagonalSupport K) :
    (secondDoubleComplexFilteredComplex K).cohomologyFiltrationIsFinite := by
  -- The same cohomology-filtration finiteness statement applies to the second filtered complex.
  simpa using
    FilteredComplex.cohomologyFiltrationIsFinite_of_hasFiniteFiltrations
      (K := secondDoubleComplexFilteredComplex K)
      (secondDoubleComplexFilteredComplex_hasFiniteFiltrations_of_finiteAntidiagonalSupport K hfin)

-- Proof sketch: boundedness together with finiteness of the first induced cohomology filtration
-- gives convergence of the first associated spectral sequence to the cohomology of the total
-- complex.
/-- Lemma 12.25.3 (5): under the same finiteness hypothesis, the first spectral sequence
associated to `K^{\bullet,\bullet}` converges to the cohomology of `\mathrm{Tot}(K^{\bullet,
\bullet})`. In this file the convergence package is recorded by
`(firstDoubleComplexFilteredComplex K).convergesToCohomology E` for an associated spectral
sequence `E` of the canonical first filtration. -/
theorem firstDoubleComplex_convergesToTotalCohomology_of_finiteAntidiagonalSupport
    (K : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)]
    (E : CohomologicalSpectralSequence 𝒜 0)
    [IsAssociatedToFilteredComplex (firstDoubleComplexFilteredComplex K) E]
    (hfin : doubleComplexHasFiniteAntidiagonalSupport K) :
    (firstDoubleComplexFilteredComplex K).convergesToCohomology E := by
  -- Convergence is exactly the owner conclusion supplied by Lemma `12.24.11`.
  simpa using
    FilteredComplex.convergesToCohomology_of_hasFiniteFiltrations
      (K := firstDoubleComplexFilteredComplex K) (E := E)
      (firstDoubleComplexFilteredComplex_hasFiniteFiltrations_of_finiteAntidiagonalSupport K hfin)

-- Proof sketch: apply the same filtered-complex convergence argument to the second filtration on
-- the total complex.
/-- Lemma 12.25.3 (6): under the same finiteness hypothesis, the second spectral sequence
associated to `K^{\bullet,\bullet}` converges to the cohomology of `\mathrm{Tot}(K^{\bullet,
\bullet})`. In this file the convergence package is recorded by
`(secondDoubleComplexFilteredComplex K).convergesToCohomology E` for an associated spectral
sequence `E` of the canonical second filtration. -/
theorem secondDoubleComplex_convergesToTotalCohomology_of_finiteAntidiagonalSupport
    (K : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)]
    (E : CohomologicalSpectralSequence 𝒜 0)
    [IsAssociatedToFilteredComplex (secondDoubleComplexFilteredComplex K) E]
    (hfin : doubleComplexHasFiniteAntidiagonalSupport K) :
    (secondDoubleComplexFilteredComplex K).convergesToCohomology E := by
  -- The second filtered complex converges by the same finite-filtration criterion.
  simpa using
    FilteredComplex.convergesToCohomology_of_hasFiniteFiltrations
      (K := secondDoubleComplexFilteredComplex K) (E := E)
      (secondDoubleComplexFilteredComplex_hasFiniteFiltrations_of_finiteAntidiagonalSupport K hfin)

-- Proof sketch: boundedness lets one pass from a page `E_r` lying in a weak Serre subcategory to
-- the limiting graded pieces of the first filtration; finiteness of that filtration then implies
-- that the total cohomology objects belong to the same weak Serre subcategory by closure under
-- extensions.
/-- Lemma 12.25.3 (7): let `\mathcal C` be a weak Serre subcategory of `\mathcal A`. If for some
page `r` every term of the first spectral sequence associated to `K^{\bullet,\bullet}` lies in
`\mathcal C`, then every cohomology object `H^n(\mathrm{Tot}(K^{\bullet,\bullet}))` lies in
`\mathcal C`. -/
theorem firstDoubleComplex_totalCohomologyObject_mem_of_page_mem_of_finiteAntidiagonalSupport
    (K : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)]
    (E : CohomologicalSpectralSequence 𝒜 0)
    [IsAssociatedToFilteredComplex (firstDoubleComplexFilteredComplex K) E]
    (P : ObjectProperty 𝒜) [IsWeakSerreClass P]
    (hfin : doubleComplexHasFiniteAntidiagonalSupport K)
    (r : ℤ) (hr : 0 ≤ r)
    (hpage : ∀ p q : ℤ, P ((E.page r hr).X (p, q))) :
    ∀ n : ℤ, P ((Tot(K)).homology n) := by
  -- Apply the weak-Serre conclusion from Lemma `12.24.11` to the first filtered complex.
  intro n
  simpa using
    FilteredComplex.cohomologyObject_mem_of_page_mem_of_hasFiniteFiltrations
      (K := firstDoubleComplexFilteredComplex K) (E := E) (P := P)
      (firstDoubleComplexFilteredComplex_hasFiniteFiltrations_of_finiteAntidiagonalSupport K hfin)
      r hr hpage n

-- Proof sketch: the same argument applied to the second filtration shows that a page of the
-- second spectral sequence lying in a weak Serre subcategory forces the cohomology of the total
-- complex to lie there as well.
/-- Lemma 12.25.3 (8): let `\mathcal C` be a weak Serre subcategory of `\mathcal A`. If for some
page `r` every term of the second spectral sequence associated to `K^{\bullet,\bullet}` lies in
`\mathcal C`, then every cohomology object `H^n(\mathrm{Tot}(K^{\bullet,\bullet}))` lies in
`\mathcal C`. -/
theorem secondDoubleComplex_totalCohomologyObject_mem_of_page_mem_of_finiteAntidiagonalSupport
    (K : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)]
    (E : CohomologicalSpectralSequence 𝒜 0)
    [IsAssociatedToFilteredComplex (secondDoubleComplexFilteredComplex K) E]
    (P : ObjectProperty 𝒜) [IsWeakSerreClass P]
    (hfin : doubleComplexHasFiniteAntidiagonalSupport K)
    (r : ℤ) (hr : 0 ≤ r)
    (hpage : ∀ p q : ℤ, P ((E.page r hr).X (p, q))) :
    ∀ n : ℤ, P ((Tot(K)).homology n) := by
  -- The same weak-Serre argument applies to the second filtered complex.
  intro n
  simpa using
    FilteredComplex.cohomologyObject_mem_of_page_mem_of_hasFiniteFiltrations
      (K := secondDoubleComplexFilteredComplex K) (E := E) (P := P)
      (secondDoubleComplexFilteredComplex_hasFiniteFiltrations_of_finiteAntidiagonalSupport K hfin)
      r hr hpage n

end

end CategoryTheory
