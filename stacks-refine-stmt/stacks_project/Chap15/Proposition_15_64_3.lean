import Mathlib
import stacks_project.Chap15.Lemma_15_64_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open scoped DerivedTensorProduct
open CategoryTheory

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

/-
Domain-style sampling for Proposition `15.64.3`.
- primary domain: filtered derived tensor products of cochain complexes of `R`-modules and the
  associated cohomological spectral sequences of Chapter `12`;
- sampled owner/canonical declarations in this domain:
  `FilteredCochainComplex.exists_filteredFreeResolution`,
  `FilteredComplex.pageOneIso`,
  `FilteredComplex.exists_filteredComplexAssociatedSpectralSequence`,
  `exists_kunnethFilteredTensorAssociatedSpectralSequence`;
- best owner abstraction: the primitive source-facing data is a filtered tensor model
  `T^•` for `K^• ⊗_R^{\mathbf L} L^•` together with its canonical `E₁`-page identification, while
  the associated spectral-sequence package is derived API owned by
  `exists_kunnethFilteredTensorAssociatedSpectralSequence`;
- primitive vs. derived: the filtered tensor model and its stage-control bridge are primitive,
  whereas the associated spectral sequence, page-one comparison on `(E.page 1).X`, boundedness,
  finiteness, the chosen-`E` abutment predicate `T.abutsToCohomologyWith E`, and the comparison
  with the derived tensor-product cohomology are derived from the Chapter `12` owners;
- source/core/bridge triage:
  `source-facing`: the proposition below, asserting existence of a filtered tensor model together
    with the displayed Künneth spectral sequence;
  `core/canonical`: `FilteredComplex`, `IsAssociatedToFilteredComplex`, and
    `exists_kunnethFilteredTensorAssociatedSpectralSequence`;
  `bridge/view`: the internal theorem `exists_kunnethFilteredTensorModel`, which isolates the
    primitive tensor-model existence needed to invoke the canonical owner theorem.

The public statement therefore stays source-facing, but its spectral-sequence part should be
derived by reusing the upstream owner theorem rather than packaged again as parallel primitive
data in this file.
-/
section

variable {R : Type u} [CommRing R]
variable [LocallySmall (ModuleCat R)] [WellPowered (ModuleCat R)]
  [CategoryTheory.Limits.HasWidePullbacks (ModuleCat R)]
  [CategoryTheory.Limits.HasCoproducts (ModuleCat R)]
  [CategoryTheory.Limits.InitialMonoClass (ModuleCat R)]

open FilteredCochainComplex
open FilteredComplex

local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)

-- Proof sketch: choose filtered free K-flat resolutions of `K` and `L` as in Lemma `15.64.2`,
-- form the filtered total tensor complex `Tot(P^• ⊗_R Q^•)`, and identify its graded pieces with
-- the derived tensor products of the graded pieces of `K` and `L`. Eventual acyclicity and
-- eventual quasi-isomorphism for the filtrations of `K` and `L` transfer to the corresponding
-- stage hypotheses for the filtered tensor model.
private theorem exists_kunnethFilteredTensorModel
    (K L : FilteredCochainComplex (ModuleCat R)) :
    ∃ (T : FilteredCochainComplex (ModuleCat R))
      (representationIso :
        DerivedCategory.Q.obj T.underlying ≅
          ((DerivedCategory.Q.obj K.underlying) ⊗[R]^L
            DerivedCategory.Q.obj L.underlying))
      (modelPageOneIso : ∀ p q : ℤ,
        (gr^{p} T).homology (p + q) ≅
          ∐ fun i : ℤ ↦
            (H (p + q)).obj
              ((DerivedCategory.Q.obj (gr^{i} K)) ⊗[R]^L
                (DerivedCategory.Q.obj (gr^{p - i} L)))),
      (∃ pK₀ : ℤ, ∀ ⦃p : ℤ⦄ (_ : pK₀ ≤ p), (F^{p} K).Acyclic) →
        (∃ pK₁ : ℤ, ∀ ⦃p : ℤ⦄ (_ : p ≤ pK₁), QuasiIso (K.stageInclusion p)) →
          (∃ pL₀ : ℤ, ∀ ⦃p : ℤ⦄ (_ : pL₀ ≤ p), (F^{p} L).Acyclic) →
            (∃ pL₁ : ℤ, ∀ ⦃p : ℤ⦄ (_ : p ≤ pL₁), QuasiIso (L.stageInclusion p)) →
              (∃ pT₀ : ℤ, ∀ ⦃p : ℤ⦄ (_ : pT₀ ≤ p), (F^{p} T).Acyclic) ∧
                ∃ pT₁ : ℤ, ∀ ⦃p : ℤ⦄ (_ : p ≤ pT₁), QuasiIso (T.stageInclusion p) := by
  sorry

-- Proof sketch: choose filtered free K-flat resolutions of `K` and `L` as in Lemma `15.64.2`,
-- form the filtered total tensor complex `Tot(P^• ⊗_R Q^•)`, and use Lemma `15.64.1` plus the
-- standard filtered-double-complex construction from this section. The resulting `E₁`-page is the
-- canonical composite of `FilteredComplex.pageOneIso` with the model identification, while the
-- representation isomorphism `Q(T^•) ≅ Q(K^•) ⊗_R^{\mathbf L} Q(L^•)` is the primitive source-facing
-- output. The same lemma supplies boundedness, finite induced filtrations, and convergence once
-- the eventual acyclicity and eventual quasi-isomorphism hypotheses on the filtrations are
-- imposed.
/-- Proposition 15.64.3: for filtered cochain complexes `K^\bullet` and `L^\bullet` of
`R`-modules, there exists a filtered cochain complex `T^\bullet` representing
`K^\bullet \otimes_R^{\mathbf L} L^\bullet` whose associated spectral sequence has
`E_1^{p,q} = \bigoplus_{i + j = p} H^{p+q}(\operatorname{gr}^i K^\bullet \otimes_R^{\mathbf L}
\operatorname{gr}^j L^\bullet)`. If the filtrations on `K^\bullet` and `L^\bullet` are
eventually acyclic above and eventually quasi-isomorphic below, then this spectral sequence is
bounded, the Chapter `12` finiteness predicate for the induced cohomology filtrations holds, and
the chosen associated spectral sequence abuts to `H^*(K^\bullet \otimes_R^{\mathbf L}
L^\bullet)` through the returned abutment comparison isomorphism. -/
theorem exists_kunneth_filteredTensorSpectralSequence
    (K L : FilteredCochainComplex (ModuleCat R)) :
    ∃ (T : FilteredCochainComplex (ModuleCat R))
      (_ :
        DerivedCategory.Q.obj T.underlying ≅
          ((DerivedCategory.Q.obj K.underlying) ⊗[R]^L
            DerivedCategory.Q.obj L.underlying))
      (E : CohomologicalSpectralSequence (ModuleCat R) 0)
      (associated : IsAssociatedToFilteredComplex T E)
      (_ : ∀ n : ℤ,
        T.underlying.homology n ≅
          (H n).obj
            ((DerivedCategory.Q.obj K.underlying) ⊗[R]^L
              DerivedCategory.Q.obj L.underlying))
      (_ : ∀ p q : ℤ,
        (E.page 1).X (p, q) ≅
          ∐ fun i : ℤ ↦
            (H (p + q)).obj
              ((DerivedCategory.Q.obj (gr^{i} K)) ⊗[R]^L
                (DerivedCategory.Q.obj (gr^{p - i} L)))),
      (∃ pK₀ : ℤ, ∀ ⦃p : ℤ⦄ (_ : pK₀ ≤ p), (F^{p} K).Acyclic) →
        (∃ pK₁ : ℤ, ∀ ⦃p : ℤ⦄ (_ : p ≤ pK₁), QuasiIso (K.stageInclusion p)) →
          (∃ pL₀ : ℤ, ∀ ⦃p : ℤ⦄ (_ : pL₀ ≤ p), (F^{p} L).Acyclic) →
            (∃ pL₁ : ℤ, ∀ ⦃p : ℤ⦄ (_ : p ≤ pL₁), QuasiIso (L.stageInclusion p)) →
              CohomologicalSpectralSequence.IsBounded E ∧
                T.cohomologyFiltrationIsFinite ∧
                T.abutsToCohomologyWith E := by
  obtain ⟨T, representationIso, modelPageOneIso, stageControl⟩ :=
    exists_kunnethFilteredTensorModel K L
  obtain ⟨E, associated, abutmentIso, pageOneIso, spectralSequenceConsequences⟩ :=
    exists_kunnethFilteredTensorAssociatedSpectralSequence
      T K L representationIso modelPageOneIso
  refine ⟨T, representationIso, E, associated, abutmentIso, pageOneIso, ?_⟩
  intro hKacyclic hKquasi hLacyclic hLquasi
  rcases stageControl hKacyclic hKquasi hLacyclic hLquasi with ⟨hTacyclic, hTquasi⟩
  rcases spectralSequenceConsequences hTacyclic hTquasi with ⟨hBounded, hFinite, _, hConverges⟩
  exact ⟨hBounded, hFinite, hConverges.2.1⟩

end

end CategoryTheory
