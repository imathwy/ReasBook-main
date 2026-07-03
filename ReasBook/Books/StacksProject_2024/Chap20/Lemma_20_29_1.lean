import Mathlib
import stacks_project.Chap12.Lemma_12_24_10
import stacks_project.Chap19.Remark_19_13_8
import stacks_project.Chap20.«20_14_1_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.FilteredComplex
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable (X : RingedSpace.{u})
variable [LocallySmall (RingedSpace.Modules X)] [WellPowered (RingedSpace.Modules X)]
  [HasWidePullbacks (RingedSpace.Modules X)] [HasCoproducts (RingedSpace.Modules X)]
  [InitialMonoClass (RingedSpace.Modules X)]
  [IsGrothendieckAbelian (RingedSpace.Modules X)]
  [LocallySmall (ModuleCat (globalSectionsRing X))]
  [WellPowered (ModuleCat (globalSectionsRing X))]
  [HasWidePullbacks (ModuleCat (globalSectionsRing X))]
  [HasCoproducts (ModuleCat (globalSectionsRing X))]
  [InitialMonoClass (ModuleCat (globalSectionsRing X))]

local instance instAbelianSheafModules : Abelian (RingedSpace.Modules X) :=
  SheafOfModules.instAbelian (RingedSpace.ringCatSheaf X)

local instance instHasDerivedCategorySheafModules : HasDerivedCategory (RingedSpace.Modules X) :=
  HasDerivedCategory.standard (RingedSpace.Modules X)

local instance instHasDerivedCategoryGlobalSectionsModuleCat :
    HasDerivedCategory (ModuleCat (globalSectionsRing X)) :=
  HasDerivedCategory.standard (ModuleCat (globalSectionsRing X))

local notation "ModΓX" => ModuleCat (globalSectionsRing X)
local notation "RΓ" => moduleDerivedGlobalSections X
local notation "HΓ" n => DerivedCategory.homologyFunctor ModΓX n

/- Domain-style sampling for Lemma `20.29.1`.
- primary domain: filtered complexes and their associated cohomological spectral sequences after
  applying derived global sections;
- sampled owner declarations:
  `moduleDerivedGlobalSections`,
  `IsAssociatedToFilteredComplex`,
  `FilteredComplex.pageOneIso`,
  `FilteredComplex.abutsToCohomology`;
- best owner abstraction: a filtered complex of `Γ(X, \mathcal O_X)`-modules together with the
  Chapter `12` owner predicate `IsAssociatedToFilteredComplex`;
- primitive data: the filtered complex in `ModΓX`, its associated spectral sequence, and the
  page-one/abutment comparison isomorphisms;
- derived API: the boundedness and abutment consequences of eventual stagewise control;
- source/core/bridge triage:
  `source-facing`: `moduleHypercohomology`, the two eventual stage-control predicates, and the
    existence theorem below;
  `core/canonical`: `FilteredComplex`, `CohomologicalSpectralSequence`, and
    `IsAssociatedToFilteredComplex`;
  `bridge/view`: the page-one and abutment comparison isomorphisms specialized to derived global
    sections. -/

/-- The hypercohomology module `H^n(X, K)` of a complex of `\mathcal O_X`-modules, computed by
derived global sections over the ring `Γ(X, \mathcal O_X)`. -/
abbrev moduleHypercohomology
    (K : CochainComplex (RingedSpace.Modules X) ℤ) (n : ℤ) :
    ModΓX :=
  (HΓ n).obj
    (RΓ.obj
      ((DerivedCategory.Q : CochainComplex (RingedSpace.Modules X) ℤ ⥤
        DerivedCategory (RingedSpace.Modules X)).obj K))

/-- The map on hypercohomology induced by a morphism of complexes of `\mathcal O_X`-modules. -/
abbrev moduleHypercohomologyMap
    {K L : CochainComplex (RingedSpace.Modules X) ℤ} (f : K ⟶ L) (n : ℤ) :
    moduleHypercohomology X K n ⟶ moduleHypercohomology X L n :=
  (HΓ n).map
    (RΓ.map
      ((DerivedCategory.Q : CochainComplex (RingedSpace.Modules X) ℤ ⥤
        DerivedCategory (RingedSpace.Modules X)).map f))

/-- For every cohomological degree, the stage hypercohomology `H^n(X, F^p K^•)` vanishes for all
sufficiently large filtration indices. -/
def EventualStageHypercohomologyVanishesAbove
    (K : CategoryTheory.FilteredComplex (RingedSpace.Modules X)) : Prop :=
  ∀ n : ℤ, ∃ p₀ : ℤ, ∀ ⦃p : ℤ⦄, p₀ ≤ p →
    IsZero (moduleHypercohomology X (K.stage p) n)

/-- For every cohomological degree, the canonical maps
`H^n(X, F^p K^•) → H^n(X, K^•)` are isomorphisms for all sufficiently small filtration indices.
-/
def EventualStageHypercohomologyStabilizesBelow
    (K : CategoryTheory.FilteredComplex (RingedSpace.Modules X)) : Prop :=
  ∀ n : ℤ, ∃ p₁ : ℤ, ∀ ⦃p : ℤ⦄, p ≤ p₁ →
    IsIso (moduleHypercohomologyMap X (K.stageInclusion p) n)

-- Proof sketch: choose a filtered K-injective replacement `K^• ⟶ J^•` as in Lemma `19.13.7`,
-- apply the global-sections functor degreewise to obtain a filtered complex of
-- `Γ(X, \mathcal O_X)`-modules, and take its associated spectral sequence from Chapter `12.24`.
-- Evaluating cohomology on the graded pieces gives the stated `E₁`-page, and Lemma `12.24.13`
-- supplies boundedness and convergence from the eventual vanishing and stabilization hypotheses on
-- the stage hypercohomology.
/-- Lemma 20.29.1: for a ringed space `X` and a filtered complex `\mathcal F^\bullet` of
`\mathcal O_X`-modules, there exists a canonical cohomological spectral sequence of bigraded
`Γ(X, \mathcal O_X)`-modules with `E_1^{p,q} = H^{p + q}(X, gr^p(\mathcal F^\bullet))`. If for
every `n` the stage hypercohomology `H^n(X, F^p\mathcal F^\bullet)` vanishes for `p ≫ 0` and the
canonical map `H^n(X, F^p\mathcal F^\bullet) → H^n(X, \mathcal F^\bullet)` is an isomorphism for
`p ≪ 0`, then the chosen associated spectral sequence is bounded and the underlying filtered
complex abuts to `H^*(X, \mathcal F^\bullet)`. -/
theorem exists_filteredHypercohomologySpectralSequence
    (K : CategoryTheory.FilteredComplex (RingedSpace.Modules X)) :
    ∃ (filteredComplex : CategoryTheory.FilteredComplex ModΓX)
      (spectralSequence : CohomologicalSpectralSequence ModΓX 0)
      (_ : IsAssociatedToFilteredComplex filteredComplex spectralSequence)
      (pageOneIso :
        ∀ p q : ℤ,
          (spectralSequence.page 1).X (p, q) ≅
            moduleHypercohomology X (K.gradedPiece p) (p + q))
      (targetIso :
        ∀ n : ℤ,
          filteredComplex.underlying.homology n ≅
            moduleHypercohomology X K.underlying n),
      (EventualStageHypercohomologyVanishesAbove X K →
        EventualStageHypercohomologyStabilizesBelow X K →
        CohomologicalSpectralSequence.IsBounded spectralSequence) ∧
      (EventualStageHypercohomologyVanishesAbove X K →
        EventualStageHypercohomologyStabilizesBelow X K →
        FilteredComplex.abutsToCohomology filteredComplex) := sorry

end AlgebraicGeometry.RingedSpace
