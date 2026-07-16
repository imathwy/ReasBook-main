import Mathlib
import stacks_proof.stacks_project.Chap12.Lemma_12_24_3
import stacks_proof.stacks_project.Chap12.Definition_12_24_9
import stacks_proof.stacks_project.Chap12.Lemma_12_24_11
import stacks_proof.stacks_project.Chap13.Lemma_13_13_8
import stacks_proof.stacks_project.Chap13.Lemma_13_16_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

section SpectralSequences

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]
  [LocallySmall ℬ] [WellPowered ℬ] [HasWidePullbacks ℬ] [HasCoproducts ℬ]
  [InitialMonoClass ℬ] [HasDerivedCategory.{w} ℬ]

open FilteredComplex

/- Domain-style sampling:
- primary domain: filtered complexes in `ℬ`, their associated cohomological spectral sequences,
  and the right-derived cohomology of the graded pieces and the underlying complex of a bounded-
  below filtered complex in `𝒜`;
- sampled owner declarations:
  `IsAssociatedToFilteredComplex`,
  `FilteredComplex.pageOneIso`,
  `FilteredComplex.cohomologyFiltrationIsFinite`,
  `FilteredComplex.convergesToCohomology`,
  `SpectralSequence.Hom`,
  `rightDerivedValueMap`;
- best owner abstraction:
  `source-facing`: Lemma `13.26.14`, i.e. existence of the filtered right-derived spectral
    sequence with its `E₁`-page, boundedness, convergence, finite abutment filtrations,
    functoriality, and choice-independence for pages `r ≥ 1`;
  `core/canonical`: `FilteredComplex`, `IsAssociatedToFilteredComplex`,
    `FilteredComplex.pageOneIso`, `FilteredComplex.cohomologyFiltrationIsFinite`,
    `FilteredComplex.convergesToCohomology`, `SpectralSequence.Hom`, `rightDerivedValue`, and
    `rightDerivedValueMap`;
  `bridge/view`: the source-facing `E₁`-page and abutment isomorphisms expressed against
    `DerivedCategory.homologyFunctor`.
- primitive data: a filtered-complex model `M` in `ℬ`, its associated spectral sequence `E`, and
  the page-one and abutment comparison isomorphisms;
- derived API: boundedness, finite abutment filtrations, convergence, the morphisms induced by a
  map `K ⟶ L`, and the choice-independence isomorphisms on pages `r ≥ 1`;
  the finite-filtration witness on `M` is auxiliary proof data internal to the construction.

The public surface should therefore keep a single existence theorem on the canonical filtered-
complex/spectral-sequence owners, with direct `pageOneIso` and `targetIso` bridge data and the
canonical Chapter `12` boundedness/convergence package recorded on the same returned owners, plus
separate companion theorems for functoriality and choice-independence. The former local split into
a page-one existence theorem and a second abutment theorem weakened the source semantics and hid
the owner-level page-one surface. -/

local notation "Qis" => HomotopyCategory.quasiIso 𝒜 (up ℤ)
local notation "Qh" => HomotopyCategory.quotient 𝒜 (up ℤ)
local notation "H" => DerivedCategory.homologyFunctor ℬ

variable (T : 𝒜 ⥤ ℬ) [T.Additive]

local notation "KtoD" => mapHomotopyCategoryToDerived T

local instance gradedPiece_hasPointwiseRightDerivedFunctorAt
    (K : FilteredComplex 𝒜)
    (hgr : ∀ p : ℤ,
      Functor.HasPointwiseRightDerivedFunctorAt KtoD Qis ((Qh).obj (gr^{p} K)))
    (p : ℤ) :
    Functor.HasPointwiseRightDerivedFunctorAt KtoD Qis ((Qh).obj (gr^{p} K)) :=
  hgr p

local instance underlying_hasPointwiseRightDerivedFunctorAt
    (K : FilteredComplex 𝒜)
    (hKder : Functor.HasPointwiseRightDerivedFunctorAt KtoD Qis ((Qh).obj K.underlying)) :
    Functor.HasPointwiseRightDerivedFunctorAt KtoD Qis ((Qh).obj K.underlying) :=
  hKder

private theorem zero_le_of_one_le {r : ℤ} (hr : 1 ≤ r) : 0 ≤ r :=
  le_trans (by decide : (0 : ℤ) ≤ 1) hr

-- Proof sketch: choose a filtered quasi-isomorphism `K^• ⟶ I^•` to a bounded-below filtered
-- complex of filtered injectives, apply `T` termwise, and take the associated spectral sequence
-- of the resulting filtered complex in `ℬ`. Chapter `12` then supplies the owner-level page-one,
-- boundedness, finite-filtration, and convergence package, while the derived-functor comparison
-- identifies the page-one terms with `R^{p + q}T(gr^p(K^•))` and the abutment with `R^*T(K^•)`.
/-- Lemma 13.26.14: for a left exact functor `T : \mathcal A ⥤ \mathcal B` and a bounded-below
filtered complex `K^•` with finite filtrations, there exists an associated cohomological spectral
sequence whose `E_1`-page is `R^{p + q}T(\mathrm{gr}^p(K^•))`, which is bounded, converges to
`R^*T(K^•)`, and induces finite filtrations on the abutment objects; the returned
`pageOneIso`/`abutmentIso` data make the source-facing comparisons explicit on the theorem surface,
while the boundedness, finite abutment filtration, and convergence package is recorded through the
canonical Chapter `12` owners rather than by returning extra construction witnesses. -/
@[stacks 015W]
theorem exists_filteredRightDerivedSpectralSequence
    [PreservesFiniteLimits T]
    (K : FilteredComplex 𝒜) (hKfin : K.HasFiniteFiltrations)
    (hKplus : CochainComplex.plus 𝒜 K.underlying)
    (hgr : ∀ p : ℤ,
      Functor.HasPointwiseRightDerivedFunctorAt KtoD Qis ((Qh).obj (gr^{p} K)))
    (hKder : Functor.HasPointwiseRightDerivedFunctorAt KtoD Qis ((Qh).obj K.underlying)) :
    ∃ (M : FilteredComplex ℬ)
      (E : CohomologicalSpectralSequence ℬ 0) (_ : IsAssociatedToFilteredComplex M E)
      (pageOneIso : ∀ p q : ℤ,
        (E.page 1).X (p, q) ≅
          (H (p + q)).obj
            (rightDerivedValue Qis KtoD ((Qh).obj (gr^{p} K))))
      (abutmentIso : ∀ n : ℤ,
        M.underlying.homology n ≅
          (H n).obj
            (rightDerivedValue Qis KtoD ((Qh).obj K.underlying))),
      CohomologicalSpectralSequence.IsBounded E ∧
        M.cohomologyFiltrationIsFinite ∧
        M.convergesToCohomology E := sorry

-- Proof sketch: choose filtered injective models for `K` and `L`, use Lemma `13.26.11` to lift
-- a morphism `K ⟶ L` to a map between the chosen filtered injective models in the filtered
-- homotopy category, apply `T` termwise, and pass to the associated spectral-sequence morphism.
/-- The spectral sequence of Lemma `13.26.14` is functorial in the filtered complex `K^•`. -/
theorem exists_filteredRightDerivedSpectralSequenceMap
    [PreservesFiniteLimits T]
    {K L : FilteredComplex 𝒜}
    (hgrK : ∀ p : ℤ,
      Functor.HasPointwiseRightDerivedFunctorAt KtoD Qis ((Qh).obj (gr^{p} K)))
    (hgrL : ∀ p : ℤ,
      Functor.HasPointwiseRightDerivedFunctorAt KtoD Qis ((Qh).obj (gr^{p} L)))
    (α : K ⟶ L)
    {M : FilteredComplex ℬ} {E : CohomologicalSpectralSequence ℬ 0}
    (hE : IsAssociatedToFilteredComplex M E)
    (pageOneIsoK : ∀ p q : ℤ,
      (E.page 1).X (p, q) ≅
        (H (p + q)).obj
          (rightDerivedValue Qis KtoD ((Qh).obj (gr^{p} K))))
    {M' : FilteredComplex ℬ} {E' : CohomologicalSpectralSequence ℬ 0}
    (hE' : IsAssociatedToFilteredComplex M' E')
    (pageOneIsoL : ∀ p q : ℤ,
      (E'.page 1).X (p, q) ≅
        (H (p + q)).obj
          (rightDerivedValue Qis KtoD ((Qh).obj (gr^{p} L)))) :
    ∃ φ : E ⟶ E',
      ∀ p q : ℤ,
        CommSq
          ((φ.hom 1).f (p, q))
          (pageOneIsoK p q).hom
          (pageOneIsoL p q).hom
          ((H (p + q)).map
            (rightDerivedValueMap Qis KtoD ((Qh).map (gradedPieceMap α p)))) := sorry

-- Proof sketch: apply the functoriality theorem to the identity map on `K`, once in each
-- direction between two choices. The resulting page-one comparison is the identity under the
-- common `E₁`-identifications, and from page `1` onward the induced morphisms are isomorphisms.
/-- For `r ≥ 1`, the pages and differentials of the spectral sequence of Lemma `13.26.14` do not
depend on the choice of filtered injective model. -/
theorem exists_filteredRightDerivedSpectralSequenceIso_of_sameSource
    [PreservesFiniteLimits T]
    (K : FilteredComplex 𝒜)
    (hgr : ∀ p : ℤ,
      Functor.HasPointwiseRightDerivedFunctorAt KtoD Qis ((Qh).obj (gr^{p} K)))
    {M : FilteredComplex ℬ} {E : CohomologicalSpectralSequence ℬ 0}
    (hE : IsAssociatedToFilteredComplex M E)
    (pageOneIso : ∀ p q : ℤ,
      (E.page 1).X (p, q) ≅
        (H (p + q)).obj
          (rightDerivedValue Qis KtoD ((Qh).obj (gr^{p} K))))
    {M' : FilteredComplex ℬ} {E' : CohomologicalSpectralSequence ℬ 0}
    (hE' : IsAssociatedToFilteredComplex M' E')
    (pageOneIso' : ∀ p q : ℤ,
      (E'.page 1).X (p, q) ≅
        (H (p + q)).obj
          (rightDerivedValue Qis KtoD ((Qh).obj (gr^{p} K)))) :
    ∃ φ : E ⟶ E',
      (∀ p q : ℤ,
        CommSq
          ((φ.hom 1).f (p, q))
          (pageOneIso p q).hom
          (pageOneIso' p q).hom
          (𝟙 _)) ∧
      ∀ (r : ℤ) (hr : 1 ≤ r) (p q : ℤ),
        IsIso ((φ.hom r (zero_le_of_one_le hr)).f (p, q)) := sorry

end SpectralSequences

end CategoryTheory
