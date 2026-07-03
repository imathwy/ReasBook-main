import Mathlib
import Mathlib.Algebra.Homology.CochainComplexOpposite
import Mathlib.CategoryTheory.Abelian.Projective.Extend

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_64_1 (from Chap15) -/
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

/-! ### Lemma_15_64_2 (from Chap15) -/
noncomputable section

universe u

namespace CategoryTheory
namespace FilteredCochainComplex

open FilteredComplex

/- Domain-style sampling for Lemma `15.64.2`.
- primary domain: filtered cochain complexes of `R`-modules, their underlying, stage, and
  graded-piece cochain complexes, and filtered free K-flat resolutions;
- sampled owner/canonical declarations in this domain:
  `FilteredComplex (ModuleCat R)`,
  `FilteredComplex.underlying`,
  `FilteredComplex.stage`,
  `FilteredComplex.gradedPiece`,
  `FilteredComplex.underlyingMap`,
  `FilteredComplex.stageMap`,
  `FilteredComplex.gradedPieceMap`,
  `CochainComplex.IsTermwiseFree`,
  `CochainComplex.IsKFlat`;
- best owner abstraction:
  `source-facing`: `FilteredCochainComplex (ModuleCat R)` together with the Chapter `12`
    stage notation `F^{p} K` and graded-piece notation `gr^{p} K`;
  `core/canonical`: `FilteredComplex (ModuleCat R)` with `underlying`, `F^{p}(-)`, `gr^{p}(-)`,
    `underlyingMap`, `stageMap`, `gradedPieceMap`, and the Chapter `15` owner
    `CochainComplex.IsKFlat` on the resulting cochain complexes;
- primitive data: a filtered cochain complex `P`, a filtered cochain complex `K`, and a morphism
  `φ : P ⟶ K`, plus the termwise-freeness clauses on `P.underlying`, `F^{p} P`, and `gr^{p} P`;
- derived API: the owner-level K-flatness clauses on `P.underlying`, `F^{p} P`, and `gr^{p} P`,
  together with the comparison maps induced by `φ`.
- source/core/bridge triage:
  `source-facing`: `exists_filteredFreeResolution`;
  `core/canonical`: the Chapter `12` owner `FilteredComplex (ModuleCat R)`, together with
    `underlying`, `F^{p}(-)`, `gr^{p}(-)`, `underlyingMap`, `stageMap`, `gradedPieceMap`, and
    the Chapter `15` owner `CochainComplex.IsKFlat`;
  `bridge/view`: the induced comparison morphisms `underlyingMap`, `stageMap`, and
    `gradedPieceMap` attached to `φ`.

This file therefore keeps the source-facing filtered-resolution statement on
`FilteredCochainComplex (ModuleCat R)` and reuses the Chapter `12` and Chapter `15` owners
directly for the induced filtered-complex maps and the K-flatness content, without introducing a
parallel local wrapper for filtered K-flat data.
-/

section

variable {R : Type u} [CommRing R]

-- Proof sketch: construct `P^•` by the stepwise free filtered resolution described in the text,
-- starting from a basic filtered complex surjective on the cohomology of `K^•` and all
-- `F^p K^•`, then iteratively kill the remaining cohomology kernels. The resulting filtered
-- complex is termwise free on the underlying complex, on every stage, and on every graded piece;
-- these source-level freeness
-- properties supply the K-flatness content of the underlying complex, every stage, and every
-- graded piece, and the construction makes the underlying, stagewise, and graded-piece
-- comparison maps quasi-isomorphisms.
/-- Lemma `15.64.2` / Stacks `15.64.2`: every filtered complex of `R`-modules admits a morphism
from a filtered complex whose underlying complex, every filtration stage, and every graded piece
are K-flat, which is termwise free on the underlying complex, every filtration stage, and every
graded piece `gr^p(P^•)`,
and which is a quasi-isomorphism on the underlying complex as well as on every filtration stage
and graded piece. -/
lemma exists_filteredFreeResolution
    (K : FilteredCochainComplex (ModuleCat R)) :
    ∃ (P : FilteredCochainComplex (ModuleCat R)) (φ : P ⟶ K),
      P.underlying.IsKFlat ∧
      (∀ p, (F^{p} P).IsKFlat) ∧
      (∀ p, (gr^{p} P).IsKFlat) ∧
      P.underlying.IsTermwiseFree ∧
      (∀ p, (F^{p} P).IsTermwiseFree) ∧
      (∀ p, (gr^{p} P).IsTermwiseFree) ∧
      QuasiIso (underlyingMap φ) ∧
      (∀ p, QuasiIso (stageMap φ p)) ∧
      (∀ p, QuasiIso (gradedPieceMap φ p)) := sorry

end

end FilteredCochainComplex
end CategoryTheory

/-! ### Proposition_15_64_3 (from Chap15) -/
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

/-! ### Lemma_15_64_4_K_nneth_Spectral_Sequence (from Chap15) -/
open scoped BigOperators
open scoped DerivedTensorProduct
open scoped ZeroObject
open CategoryTheory

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]
variable [LocallySmall.{0} (ModuleCat R)] [WellPowered.{0} (ModuleCat R)]
  [CategoryTheory.Limits.HasWidePullbacks (ModuleCat R)]
  [CategoryTheory.Limits.HasCoproducts (ModuleCat R)]
  [CategoryTheory.Limits.InitialMonoClass (ModuleCat R)]

/- 
Domain-style sampling for Lemma `15.64.4`.
- primary domain: cohomological spectral sequences in the bounded derived category `D^b(R)`
  computing the cohomology of a derived tensor product;
- sampled owner/canonical declarations in this domain:
  `CohomologicalSpectralSequence`,
  `FilteredComplex.convergesToCohomology`,
  `exists_kunneth_filteredTensorSpectralSequence`,
  `derivedTensorProduct`;
- best owner abstraction: a cohomological spectral sequence
  `E : CohomologicalSpectralSequence (ModuleCat R) 0` together with the Chapter `12`
  convergence owner on an associated filtered complex, while the displayed `E₂`-page and
  abutment objects remain source-facing bridge abbreviations;
- primitive vs. derived:
  primitive data are the spectral sequence `E` and the associated filtered complex `F` in the
  convergence clause; the `E₂`-page and abutment comparisons are derived API expressed
  propositionally by existential/nonempty comparison isomorphisms, while boundedness and
  convergence are expressed through the canonical Chapter `12` owner `F.convergesToCohomology E`;
- source/core/bridge triage:
  `source-facing`: `IsKunnethDerivedTensorSpectralSequence`;
  `core/canonical`: `CohomologicalSpectralSequence`,
    `FilteredComplex.convergesToCohomology`, and the Chapter `15` owner theorem
    `exists_kunneth_filteredTensorSpectralSequence`;
  `bridge/view`: `boundedDerivedTensorCohomology`, `kunnethDerivedTensorPageTwo`, and the
    convergence predicate below.

The numbered item is source-facing, but its convergence clause should be phrased through the
canonical filtered-complex owner API rather than through a parallel local filtered-cochain wrapper.
-/

local notation "Mod" => ModuleCat R
local notation "DbMod" => Dᵇ(Mod)
local notation "H" => DerivedCategory.homologyFunctor Mod

/-- The abutment object `H^n(K \otimes_R^{\mathbf L} L)` for bounded derived `R`-complexes
`K, L ∈ D^b(R)`. -/
abbrev boundedDerivedTensorCohomology
    (K L : DbMod) (n : ℤ) : ModuleCat R :=
  (H n).obj (K.obj ⊗[R]^L L.obj)

/-- The `E_2^{p,q}` term
`\bigoplus_{i + j = q} \operatorname{Tor}^R_{-p}(H^i(K), H^j(L))`
of the Künneth spectral sequence, with the convention that it is zero for `p > 0`. -/
abbrev kunnethDerivedTensorPageTwo
    (K L : DbMod) (p q : ℤ) : ModuleCat R :=
  if _ : p ≤ 0 then
    ∐ fun i : ℤ ↦
      (((Tor Mod (Int.toNat (-p))).obj
          ((H i).obj K.obj)).obj
        ((H (q - i)).obj L.obj))
  else
    (0 : Mod)

/-- A cohomological spectral sequence converges to `H^*(K ⊗[R]^L L)` if it is associated to a
filtered complex whose cohomology identifies with that of the derived tensor product and which
satisfies the Chapter `12` convergence owner. -/
def ConvergesToDerivedTensorCohomology
    (E : CohomologicalSpectralSequence Mod 0) (K L : DbMod) : Prop :=
  ∃ (F : FilteredComplex Mod) (_ : IsAssociatedToFilteredComplex F E),
    F.convergesToCohomology E ∧
      ∀ n : ℤ,
        Nonempty (F.underlying.homology n ≅ boundedDerivedTensorCohomology K L n)

/-- The Künneth spectral sequence for bounded derived `R`-complexes `K` and `L`: a bounded
cohomological spectral sequence with the expected `E_2`-page and abutment. -/
def IsKunnethDerivedTensorSpectralSequence
    (E : CohomologicalSpectralSequence Mod 0) (K L : DbMod) : Prop :=
  CohomologicalSpectralSequence.IsBounded E ∧
    (∀ p q : ℤ,
      Nonempty ((E.page 2).X (p, q) ≅ kunnethDerivedTensorPageTwo K L p q)) ∧
    ConvergesToDerivedTensorCohomology E K L

-- Proof sketch: represent `K` and `L` by bounded complexes, filter them by stupid truncations,
-- and apply Proposition `15.64.3` to the resulting filtered tensor complex. The associated
-- spectral sequence is bounded by the boundedness of `K` and `L`, its `E₁`-page identifies with
-- the graded pieces `H^{-i}(K)[i]` and `H^{-j}(L)[j]`, and reindexing the page `r - 1` terms by
-- `E_r^{p,q} = (E')_{r - 1}^{-q, p + 2q}` gives the stated `E₂`-page and abutment.
/-- Lemma 15.64.4 (Künneth Spectral Sequence): for bounded derived `R`-complexes `K` and `L`,
there exists a bounded cohomological spectral sequence whose `E_2`-page is
`\bigoplus_{i + j = q} \operatorname{Tor}^R_{-p}(H^i(K), H^j(L))` and which converges to
`H^{p + q}(K \otimes_R^{\mathbf L} L)`. The differentials are those of a cohomological spectral
sequence, so they have bidegree `(r, -r + 1)`. -/
theorem exists_kunnethDerivedTensorSpectralSequence
    (K L : DbMod) :
    ∃ E : CohomologicalSpectralSequence Mod 0,
      IsKunnethDerivedTensorSpectralSequence E K L := sorry

end

end CategoryTheory

/-! ### Example_15_64_5 (from Chap15) -/
open scoped BigOperators

noncomputable section

universe u

namespace CategoryTheory

open Limits
open MonoidalCategory

section

variable {R : Type u} [CommRing R] [IsDedekindDomain R]

local notation "Mod" => ModuleCat R

-- Proof sketch: over a Dedekind domain every module has projective dimension at most one, so the
-- higher left derived functors of tensor product vanish in degrees `i ≥ 2`.
/-- Over a Dedekind domain, the higher `Tor` groups of two modules vanish above degree `1`. -/
theorem isZero_tor_of_two_le_of_dedekind_domain
    (M N : Mod) {i : ℕ} (hi : 2 ≤ i) :
    IsZero (Tor[R, i](M, N)) := sorry

end

section

attribute [local instance] HasDerivedCategory.standard

variable {R : Type u} [CommRing R] [IsDedekindDomain R]
variable [LocallySmall.{0} (ModuleCat R)] [WellPowered.{0} (ModuleCat R)]
  [HasWidePullbacks (ModuleCat R)] [HasCoproducts (ModuleCat R)]
  [InitialMonoClass (ModuleCat R)]

/- Domain-style sampling for Example `15.64.5`.
- primary domain: bounded-derived Künneth spectral sequences over a Dedekind domain and the
  resulting short exact sequence in total degree `n`;
- sampled owner declarations in this domain:
  `ShortComplex.ShortExact`,
  `boundedDerivedTensorCohomology`,
  `kunnethDerivedTensorPageTwo`,
  `exists_kunnethDerivedTensorSpectralSequence`;
- best owner abstraction: the canonical owner for the short exact sequence itself is a
  `ShortComplex (ModuleCat R)` together with `ShortComplex.ShortExact`, but the source-facing
  theorem should expose the actual edge maps on the named `E₂`-terms and abutment objects rather
  than an auxiliary short complex up to isomorphism; the terms themselves should be reused from
  the chapter bridge declarations `kunnethDerivedTensorPageTwo` and
  `boundedDerivedTensorCohomology`, not recopied locally;
- primitive vs. derived: the primitive data for the public theorem are the maps
  `ι : kunnethDerivedTensorPageTwo K L 0 n ⟶ boundedDerivedTensorCohomology K L n` and
  `π : boundedDerivedTensorCohomology K L n ⟶ kunnethDerivedTensorPageTwo K L (-1) (n + 1)`
  together with the vanishing relation `ι ≫ π = 0`; the canonical short-complex owner
  `(ShortComplex.mk ι π h).ShortExact` is then the derived exactness packaging;
- source/core/bridge triage:
  `source-facing`: the existence theorem below for the Künneth short exact sequence;
  `core/canonical`: `ShortComplex` and `ShortComplex.ShortExact`;
  `bridge/view`: `kunnethDerivedTensorPageTwo`, `boundedDerivedTensorCohomology`, and the
  spectral-sequence existence theorem `exists_kunnethDerivedTensorSpectralSequence`.

This example is source-facing, but the previous wrapper class duplicated the canonical
short-complex owner and recopied the `E₂`-page formulas already owned upstream. The theorem below
now states the same mathematics directly in the chapter's canonical vocabulary.
-/

-- Proof sketch: start with the Künneth spectral sequence from Lemma `15.64.4`; the previous
-- vanishing theorem kills all `E₂^{p,q}` with `p ≤ -2`, so only the columns `p = 0, -1` remain.
-- The resulting two-line spectral sequence degenerates at `E₂`, and the usual filtration
-- argument yields the short exact sequence in total degree `n`.
/-- Example 15.64.5: over a Dedekind domain, the Künneth spectral sequence of
Lemma `15.64.4` degenerates at the `E_2` page, yielding for every `n` a short exact sequence
`0 → ⨁_{i + j = n} H^i(K) ⊗_R H^j(L) → H^n(K ⊗_R^L L) →
⨁_{i + j = n + 1} Tor_1^R(H^i(K), H^j(L)) → 0`. -/
theorem exists_kunneth_short_exact_sequence_of_dedekind_domain
    (K L : boundedDerivedCategory (ModuleCat R)) (n : ℤ) :
    ∃ (ι :
        kunnethDerivedTensorPageTwo K L 0 n ⟶
          boundedDerivedTensorCohomology K L n)
      (π :
        boundedDerivedTensorCohomology K L n ⟶
          kunnethDerivedTensorPageTwo K L (-1) (n + 1))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := sorry

end

end CategoryTheory
