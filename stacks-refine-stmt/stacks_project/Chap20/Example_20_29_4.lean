import Mathlib
import stacks_project.Chap20.Lemma_20_29_1

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

local instance : Abelian (RingedSpace.Modules X) :=
  SheafOfModules.instAbelian (RingedSpace.ringCatSheaf X)

local instance : HasDerivedCategory (RingedSpace.Modules X) :=
  HasDerivedCategory.standard (RingedSpace.Modules X)

local instance :
    HasDerivedCategory (ModuleCat (globalSectionsRing X)) :=
  HasDerivedCategory.standard (ModuleCat (globalSectionsRing X))

/-- The `E_1^{p,q}` term for the stupid-filtration hypercohomology spectral sequence of `K^•`,
written as the hypercohomology of the single complex `K^p[-p]`. -/
abbrev stupidFiltrationHypercohomologyPageOneTerm
    (K : CochainComplex (RingedSpace.Modules X) ℤ) (p q : ℤ) :
    ModuleCat (globalSectionsRing X) :=
  moduleHypercohomology X
    ((CochainComplex.singleFunctor (RingedSpace.Modules X) p).obj (K.X p))
    (p + q)

/-- A chosen hypercohomology spectral sequence obtained from the stupid filtration
`F^p K^• = σ_{\ge p} K^•`. It records a filtered-complex model of the stupid filtration, the
associated spectral sequence data in the canonical Chapter `12` owner language, the `E_1`-page
identification, and the boundedness-abutment consequences when `K^•` is bounded below. -/
structure StupidFiltrationHypercohomologySpectralSequence
    (K : CochainComplex (RingedSpace.Modules X) ℤ) where
  /-- The filtered complex of `\mathcal O_X`-modules modeling the stupid filtration on `K^•`. -/
  filteredComplex : CategoryTheory.FilteredComplex (RingedSpace.Modules X)
  /-- The underlying complex of the chosen filtered model is `K^•`. -/
  underlyingIso :
    filteredComplex.underlying ≅ K
  /-- Each filtration stage is the brutal lower truncation `σ_{\ge p} K^•`. -/
  stageIso :
    ∀ p : ℤ, filteredComplex.stage p ≅ K.truncGE p
  /-- The chosen spectral sequence of `Γ(X, \mathcal O_X)`-modules. -/
  spectralSequence : CohomologicalSpectralSequence (ModuleCat (globalSectionsRing X)) 0
  /-- The chosen spectral sequence is associated to the filtered complex obtained from the stupid
  filtration. -/
  associated : IsAssociatedToFilteredComplex filteredComplex spectralSequence
  /-- The `E_1`-page identifies with the hypercohomology of the single complexes `K^p[-p]`,
  encoding the formula `E_1^{p,q} = H^{p+q}(X, K^p[-p])`. -/
  pageOneIso :
    ∀ p q : ℤ,
      (spectralSequence.page 1).X (p, q) ≅
        stupidFiltrationHypercohomologyPageOneTerm X K p q
  /-- If `K^•` is bounded below, then the chosen spectral sequence is bounded. -/
  bounded_of_isStrictlyGE :
    (∃ a : ℤ, K.IsStrictlyGE a) →
      CohomologicalSpectralSequence.IsBounded spectralSequence
  /-- If `K^•` is bounded below, then the chosen spectral sequence abuts to the hypercohomology
  of `K^•`. -/
  abuts_of_isStrictlyGE :
    (∃ a : ℤ, K.IsStrictlyGE a) →
      FilteredComplex.abutsToCohomology filteredComplex
  /-- The abutment identifies with the hypercohomology of the original complex. -/
  targetIso :
    ∀ n : ℤ,
      filteredComplex.underlying.homology n ≅
        moduleHypercohomology X K n

-- Proof sketch: apply Lemma `20.29.1` to the stupid filtration `F^p K^• = σ_{\ge p} K^•`, whose
-- graded pieces are the single complexes `K^p[-p]`. If `K^•` is bounded below, the stupid
-- filtration satisfies the boundedness hypotheses of the filtered hypercohomology construction,
-- which then gives boundedness and abutment to `H^*(X, K^•)`.
/-- Example 20.29.4: for a complex `K^•` of `\mathcal O_X`-modules on a ringed space `X`, the
stupid filtration `F^p K^• = σ_{\ge p} K^•` yields a hypercohomology spectral sequence with
`E_1^{p,q} = H^{p + q}(X, K^p[-p])`. If `K^•` is bounded below, then this spectral sequence is
bounded and abuts to `H^{p + q}(X, K^•)`. -/
theorem exists_stupidFiltrationHypercohomologySpectralSequence
    (K : CochainComplex (RingedSpace.Modules X) ℤ) :
    Nonempty (StupidFiltrationHypercohomologySpectralSequence X K) := sorry

end AlgebraicGeometry.RingedSpace
