import StacksProject_2024.Chap12.Lemma_12_24_13
import StacksProject_2024.Chap15.Definition_15_59_13

open scoped BigOperators
open scoped DerivedTensorProduct
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

namespace CategoryTheory
namespace FilteredComplex

/-
Domain-style sampling for Lemma `15.64.1`.
- primary domain: associated spectral sequences of filtered cochain complexes of `R`-modules and
  the derived-category realization of filtered tensor models, together with the Chapter `12`
  convergence criteria for filtered complexes;
- sampled owner/canonical declarations in this domain:
  `FilteredComplex.exists_filteredComplexAssociatedSpectralSequence`,
  `FilteredComplex.pageOneIso`,
  `FilteredComplex.convergesToCohomology_of_hasFiniteFiltrations`,
  `FilteredComplex.convergesToCohomology`,
  `FilteredComplex.associatedSpectralSequence_convergesToCohomology_of_eventual_stage_cohomology`,
  `DerivedCategory.homologyFunctorFactors`;
- best owner abstraction: a chosen associated spectral sequence `E` of the canonical filtered
  complex `T`, together with the canonical derived-category realization
  `DerivedCategory.Q.obj T.underlying`;
- primitive data: a filtered tensor model `T` for `K^\bullet ⊗_R^{\mathbf L} L^\bullet`
  together with its derived-category representation isomorphism and its `E₁`-page identification;
- derived API: the page-one composite with `FilteredComplex.pageOneIso`, the homology comparison
  induced from the representation isomorphism by `DerivedCategory.homologyFunctorFactors`, and the
  boundedness, finiteness, and convergence consequences supplied by Lemmas `12.24.11` and
  `12.24.13`;
- source/core/bridge triage:
  `source-facing`: the Künneth spectral-sequence statement with displayed `E₁`-page;
  `core/canonical`: associated spectral sequences of `T` and the Chapter `12`
    convergence predicates on `FilteredComplex`;
  `bridge/view`: generic transfer lemmas from filtered-complex stage hypotheses to the owner
    predicates on `T`.

The numbered item is therefore `source-facing`: the main declaration below keeps the Künneth
page-one data visible and takes the actual derived-category representation of the tensor product as
primitive input, while the generic stage-control transfer results remain companion lemmas on the
canonical `FilteredComplex` owner.
-/

variable {𝒜 : Type u} [Category 𝒜] [Abelian 𝒜]

end FilteredComplex

section

variable {R : Type u} [CommRing R]

attribute [local instance] HasDerivedCategory.standard

variable [LocallySmall (ModuleCat R)] [WellPowered (ModuleCat R)]
  [HasWidePullbacks (ModuleCat R)] [HasCoproducts (ModuleCat R)]
  [InitialMonoClass (ModuleCat R)]

open FilteredCochainComplex
open FilteredComplex

local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)

-- Proof sketch: choose an associated spectral sequence `E` for `T`; the displayed `E₁`-page is
-- obtained by composing the owner isomorphism `FilteredComplex.pageOneIso` with the supplied
-- Künneth page-one identification for `gr^p(T^•)`, and return that composite directly as the
-- source-facing `pageOneIso` witness. The abutment comparison identifying `H^n(T^•)` with
-- `H^n(K^• ⊗_R^{\mathbf L} L^\bullet)` is derived from the primitive representation isomorphism
-- `modelRepresentation` via `DerivedCategory.homologyFunctorFactors`. Under the source-facing
-- stage acyclicity and stage quasi-isomorphism hypotheses on `T`, apply the Chapter `12` owner
-- theorems for boundedness, finiteness of the induced cohomology filtration, abutment, and
-- convergence on the canonical filtered-complex owner `T` after transporting those hypotheses
-- through the generic bridge theorems of Lemma `12.24.13`.
/-- Lemma 15.64.1: let `T^\bullet` be a filtered cochain complex of `R`-modules representing
`K^\bullet ⊗_R^{\mathbf L} L^\bullet` through a chosen derived-category isomorphism
`Q(T^\bullet) ≅ Q(K^\bullet) \otimes_R^{\mathbf L} Q(L^\bullet)`, with `E₁`-page
`\bigoplus_{i + j = p} H^{p + q}(\operatorname{gr}^i K^\bullet ⊗_R^{\mathbf L}
\operatorname{gr}^j L^\bullet)`. Then there exists an associated spectral sequence for
`T^\bullet`, and the theorem returns both the corresponding canonical family of `E₁`-page
identifications with the displayed Künneth direct sum; the abutment comparison
`H^n(T^\bullet) ≅ H^n(K^\bullet ⊗_R^{\mathbf L} L^\bullet)` is derived from the chosen
representation isomorphism. If the stage complexes `F^p T^\bullet` are eventually acyclic and the
stage inclusions `F^p T^\bullet ⟶ T^\bullet` are eventually quasi-isomorphisms, then the same
associated spectral sequence is bounded, the induced cohomology filtration is finite, and it both
abuts to and converges to the cohomology of `T^\bullet`. -/
theorem exists_kunnethFilteredTensorAssociatedSpectralSequence
    (T K L : FilteredCochainComplex (ModuleCat R))
    (modelRepresentation :
      DerivedCategory.Q.obj T.underlying ≅
        ((DerivedCategory.Q.obj K.underlying) ⊗[R]^L
          DerivedCategory.Q.obj L.underlying))
    (modelPageOneIso : ∀ p q : ℤ,
      (T.gradedPiece p).homology (p + q) ≅
        ∐ fun i : ℤ ↦
          (H (p + q)).obj
            ((DerivedCategory.Q.obj (K.gradedPiece i)) ⊗[R]^L
              (DerivedCategory.Q.obj (L.gradedPiece (p - i))))) :
    ∃ (E : CohomologicalSpectralSequence (ModuleCat R) 0)
      (_ : IsAssociatedToFilteredComplex T E)
      (abutmentIso : ∀ n : ℤ,
        T.underlying.homology n ≅
          (H n).obj
            ((DerivedCategory.Q.obj K.underlying) ⊗[R]^L
              DerivedCategory.Q.obj L.underlying))
      (pageOneIso : ∀ p q : ℤ,
        (E.page 1).X (p, q) ≅
          ∐ fun i : ℤ ↦
            (H (p + q)).obj
              ((DerivedCategory.Q.obj (K.gradedPiece i)) ⊗[R]^L
                (DerivedCategory.Q.obj (L.gradedPiece (p - i))))),
      (∃ p₀ : ℤ, ∀ ⦃p : ℤ⦄ (_ : p₀ ≤ p), (F^{p} T).Acyclic) →
        (∃ p₁ : ℤ, ∀ ⦃p : ℤ⦄ (_ : p ≤ p₁), QuasiIso (T.stageInclusion p)) →
          CohomologicalSpectralSequence.IsBounded E ∧
            T.cohomologyFiltrationIsFinite ∧
            T.abutsToCohomology ∧
            T.convergesToCohomology E := by
  sorry

end

end CategoryTheory
