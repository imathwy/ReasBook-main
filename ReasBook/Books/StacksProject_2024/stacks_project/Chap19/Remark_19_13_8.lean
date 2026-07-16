import Mathlib
import StacksProject_2024.stacks_project.Chap12.Definition_12_24_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

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

local notation "D" => DerivedCategory 𝒜

/-- The derived `Ext` group `Ext^n(M, X)`, written as morphisms `M ⟶ X[n]` in the derived
category. -/
abbrev derivedExtGroup (M X : D) (n : ℤ) : AddCommGrpCat :=
  AddCommGrpCat.of (M ⟶ X⟦n⟧)
end CategoryTheory
