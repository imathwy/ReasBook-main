import Mathlib
import stacks_project.Chap20.Lemma_20_29_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
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

local notation "DMod" => DerivedCategory (RingedSpace.Modules X)
local notation "single0" => DerivedCategory.singleFunctor (RingedSpace.Modules X) (0 : ℤ)
local notation "HSh" => DerivedCategory.homologyFunctor (RingedSpace.Modules X)
local notation "HMod" => DerivedCategory.homologyFunctor (ModuleCat (globalSectionsRing X))

/-- A renumbered hypercohomology spectral sequence computing the derived global sections of a
derived `\mathcal O_X`-module `K` from the cohomology sheaves `H^j(K)`. -/
structure HypercohomologyFromCohomologySheavesSpectralSequence
    (K : DMod) where
  /-- The filtered complex of `Γ(X, \mathcal O_X)`-modules producing the spectral sequence. -/
  filteredComplex : CategoryTheory.FilteredComplex (ModuleCat (globalSectionsRing X))
  /-- The cohomological spectral sequence attached to the chosen filtered complex. -/
  spectralSequence : CohomologicalSpectralSequence (ModuleCat (globalSectionsRing X)) 0
  /-- The `E'_2`-page identifies with the sheaf cohomology groups
  `H^i(X, H^j(K))`. -/
  pageTwoIso :
    ∀ i j : ℤ,
      (spectralSequence.page 2).X (i, j) ≅
        (HMod i).obj ((moduleDerivedGlobalSections X).obj ((single0).obj ((HSh j).obj K)))
  /-- If `K` is bounded below, then the spectral sequence is bounded. -/
  bounded_of_boundedBelow :
    (∃ a : ℤ, K.IsGE a) →
      CohomologicalSpectralSequence.IsBounded spectralSequence
  /-- If `K` is bounded below, then the spectral sequence abuts to the hypercohomology of `K`.
  -/
  abuts_of_boundedBelow :
    (∃ a : ℤ, K.IsGE a) →
      CategoryTheory.FilteredComplex.abutsToCohomology filteredComplex
  /-- The abutment of the filtered complex computes the hypercohomology of `K`. -/
  abutmentIso :
    ∀ n : ℤ,
      (CategoryTheory.FilteredComplex.underlying filteredComplex).homology n ≅
        (HMod n).obj ((moduleDerivedGlobalSections X).obj K)

-- Proof sketch: choose a complex representing `K`, filter it by the truncations
-- `F^p\mathcal F^\bullet := \tau_{\le -p}\mathcal F^\bullet`, and apply Lemma `20.29.1` to the
-- resulting filtered complex. The `E_1`-page identifies with `H^{2p+q}(X, H^{-p}(\mathcal
-- F^\bullet))`; renumber by `p = -j` and `q = i + 2j` to obtain the displayed `E'_2`-page. When
-- `K` is bounded below, Remark `20.29.2` yields boundedness and convergence, and this is the
-- second Cartan-Eilenberg spectral sequence from Lemma `13.21.3` applied to derived global
-- sections.
/-- Example 20.29.3: for any `K ∈ D(\mathcal O_X)`, there is a renumbered cohomological spectral
sequence with `(E'_2)^{i,j} = H^i(X, H^j(K))`. If `K` is bounded below, then the chosen spectral
sequence is bounded and converges to the hypercohomology `H^{i + j}(X, K)`. In the bounded-below
case, this is the second spectral sequence of Derived Categories, Lemma `13.21.3`, for derived
global sections. -/
theorem exists_hypercohomologyFromCohomologySheavesSpectralSequence
    (K : DMod) :
    Nonempty (HypercohomologyFromCohomologySheavesSpectralSequence X K) := sorry

end AlgebraicGeometry.RingedSpace
