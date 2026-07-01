import Mathlib
import stacks_project.Chap12.Definition_12_24_7
import stacks_project.Chap12.Lemma_12_24_2
import stacks_project.Chap12.Definition_12_24_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open FilteredComplex

noncomputable section

universe t w v u

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [LocallySmall 𝒜] [WellPowered 𝒜]
  [HasWidePullbacks 𝒜] [HasCoproducts 𝒜] [InitialMonoClass 𝒜] [IsGrothendieckAbelian.{w} 𝒜]
  [HasDerivedCategory.{t} 𝒜]

/-
Domain-style sampling for Remark 19.13.8:
- primary domain: filtered cochain complexes and their associated cohomological spectral sequences
  in an abelian category, together with derived-category `Ext`;
- sampled owner declarations:
  `FilteredComplex.underlying`,
  `FilteredComplex.stage`,
  `FilteredComplex.gradedPiece`,
  `CategoryTheory.IsAssociatedToFilteredComplex`,
  `FilteredComplex.convergesToCohomology`;
- best owner abstraction: the Chapter 12 owner `FilteredComplex 𝒜` together with the associated
  spectral-sequence owner predicate `IsAssociatedToFilteredComplex` and the convergence owner
  `FilteredComplex.convergesToCohomology`;
- primitive data: a filtered complex `K : FilteredComplex 𝒜`, a derived object `M`, and an
  auxiliary filtered `Hom` complex together with its associated spectral sequence;
- derived API: the induced `Ext` maps and the eventual vanishing/stability hypotheses on stagewise
  `Ext`;
- source/core/bridge triage:
  `source-facing`: `EventualDerivedExtVanishesAbove`, `EventualDerivedExtStabilizesBelow`, and
    `filteredComplexExtSpectralSequence_exists`;
  `core/canonical`: `FilteredComplex 𝒜`, `IsAssociatedToFilteredComplex`, and
  `FilteredComplex.convergesToCohomology`;
  `bridge/view`: the explicit auxiliary filtered `Hom` complex appearing in
    `filteredComplexExtSpectralSequence_exists`, together with `derivedExtGroup` and
    `derivedExtGroupMap`. -/

local notation "FilteredComplex" => CategoryTheory.FilteredComplex 𝒜
local notation "AbFilteredComplex" => CategoryTheory.FilteredComplex AddCommGrpCat
local notation "D" => DerivedCategory 𝒜

/-- The derived `Ext` group `Ext^n(M, X)`, written as morphisms `M ⟶ X[n]` in the derived
category. -/
abbrev derivedExtGroup (M X : D) (n : ℤ) : AddCommGrpCat :=
  AddCommGrpCat.of (M ⟶ X⟦n⟧)

-- Proof sketch: composition in the shifted derived category is additive in the source morphism,
-- so postcomposition with the shifted map `f⟦n⟧'` defines an additive homomorphism.
/-- Postcomposition with a morphism in the shifted derived category is additive on derived
`Ext` groups. -/
theorem derivedExtGroupMap_add
    (M : D) {X Y : D} (f : X ⟶ Y) (n : ℤ)
    (α β : M ⟶ X⟦n⟧) :
    (α + β) ≫ (shiftFunctor (DerivedCategory 𝒜) n).map f =
      α ≫ (shiftFunctor (DerivedCategory 𝒜) n).map f +
        β ≫ (shiftFunctor (DerivedCategory 𝒜) n).map f := sorry

/-- The map on derived `Ext` groups induced by a morphism `X ⟶ Y` in the second variable. -/
def derivedExtGroupMap
    (M : D) {X Y : D} (f : X ⟶ Y) (n : ℤ) :
    derivedExtGroup M X n ⟶ derivedExtGroup M Y n :=
  AddCommGrpCat.ofHom <|
    AddMonoidHom.mk'
      (fun α ↦ α ≫ (shiftFunctor (DerivedCategory 𝒜) n).map f)
      (derivedExtGroupMap_add M f n)

/-- For every total degree, the groups `Ext^n(M, F^p K)` vanish for all sufficiently large
filtration indices `p`. -/
def EventualDerivedExtVanishesAbove (M : D) (K : FilteredComplex) : Prop :=
  ∀ n : ℤ, ∃ p₀ : ℤ, ∀ ⦃p : ℤ⦄, p₀ ≤ p →
    IsZero (derivedExtGroup M (DerivedCategory.Q.obj (K.stage p)) n)

/-- For every total degree, the canonical maps `Ext^n(M, F^p K) → Ext^n(M, K)` are
isomorphisms for all sufficiently small filtration indices `p`. -/
def EventualDerivedExtStabilizesBelow (M : D) (K : FilteredComplex) : Prop :=
  ∀ n : ℤ, ∃ p₁ : ℤ, ∀ ⦃p : ℤ⦄, p ≤ p₁ →
    IsIso (derivedExtGroupMap M (DerivedCategory.Q.map (K.stageInclusion p)) n)

-- Proof sketch: choose a filtered K-injective replacement `K^• ⟶ J^•` as in Lemma 19.13.7 and a
-- complex representing `M`; form the filtered Hom complex `Hom^•(M^•, J^•)` with filtration by
-- the stages `Hom^•(M^•, F^p J^•)`. Apply the filtered-complex spectral sequence from Chapter 12
-- to that filtered Hom complex, identify its `E₁`-page with `Ext^{p+q}(M, gr^p K)`, and use
-- Lemma 12.24.13 together with the two eventual Ext hypotheses to obtain boundedness and
-- convergence to `Ext^{p+q}(M, K)`.
/-- Remark 19.13.8: for a Grothendieck abelian category `𝒜`, a filtered complex `K^•`, and an
object `M` of `D(𝒜)`, there is a spectral sequence in abelian groups with
`E₁^{p,q} = Ext^{p + q}(M, gr^p(K^•))`; moreover, if `Ext^n(M, F^p K)` vanishes for `p ≫ 0` and
the canonical map `Ext^n(M, F^p K) → Ext^n(M, K)` is an isomorphism for `p ≪ 0`, then this
spectral sequence is bounded and converges to `Ext^{p + q}(M, K)`. The source-facing bridge in
this file is the explicit auxiliary filtered `Hom` complex together with the canonical owner
predicate `IsAssociatedToFilteredComplex`, the Chapter `12` convergence owner
`FilteredComplex.convergesToCohomology`, and the page-one and abutment comparison isomorphisms. -/
theorem filteredComplexExtSpectralSequence_exists
    (M : D) (K : FilteredComplex) :
    ∃ (filteredHomComplex : AbFilteredComplex)
      (E : CohomologicalSpectralSequence AddCommGrpCat 0)
      (_ : IsAssociatedToFilteredComplex filteredHomComplex E)
      (pageOneIso :
        ∀ p q : ℤ,
          (E.page 1).X (p, q) ≅
            derivedExtGroup M (DerivedCategory.Q.obj (K.gradedPiece p)) (p + q))
      (abutmentIso :
        ∀ n : ℤ,
          filteredHomComplex.underlying.homology n ≅
            derivedExtGroup M (DerivedCategory.Q.obj K.underlying) n),
      (EventualDerivedExtVanishesAbove M K →
        EventualDerivedExtStabilizesBelow M K →
        CohomologicalSpectralSequence.IsBounded E) ∧
      (EventualDerivedExtVanishesAbove M K →
        EventualDerivedExtStabilizesBelow M K →
        filteredHomComplex.convergesToCohomology E) := sorry

end CategoryTheory
