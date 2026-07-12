import Mathlib.Tactic
import StacksProject_2024.Chap12.Lemma_12_25_3
import StacksProject_2024.Chap13.CochainComplexTruncationFiltration
import StacksProject_2024.Chap13.Definition_13_21_1
import StacksProject_2024.Chap20.Lemma_20_29_1
import StacksProject_2024.Chap20.Sections_on_open

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.FilteredComplex
open ComplexShape
open CochainComplex
open CochainComplex.Plus
open DerivedCategory.TStructure
open AlgebraicGeometry
open TopologicalSpace
open scoped CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable (X : RingedSpace.{u})
variable [LocallySmall (RingedSpace.Modules X)] [WellPowered (RingedSpace.Modules X)]
  [HasWidePullbacks (RingedSpace.Modules X)] [HasCoproducts (RingedSpace.Modules X)]
  [InitialMonoClass (RingedSpace.Modules X)] [LocallySmall (ModuleCat (globalSectionsRing X))]
  [WellPowered (ModuleCat (globalSectionsRing X))]
  [HasWidePullbacks (ModuleCat (globalSectionsRing X))]
  [HasCoproducts (ModuleCat (globalSectionsRing X))]
  [InitialMonoClass (ModuleCat (globalSectionsRing X))]

local notation "ModX" => RingedSpace.Modules X
local notation "ModΓX" => ModuleCat (globalSectionsRing X)
local notation "DMod" => DerivedCategory ModX
local notation "RΓ" => moduleDerivedGlobalSections X
local notation "HX" n => DerivedCategory.homologyFunctor ModX n
local notation "HΓ" n => DerivedCategory.homologyFunctor ModΓX n

private theorem zero_le_of_one_le {r : ℤ} (hr : 1 ≤ r) : 0 ≤ r := by
  omega

/- Domain-style sampling for Example `20.29.3`.
- primary domain: truncation-filtration hypercohomology spectral sequences for derived
  `𝒪_X`-modules on a ringed space;
- sampled owner declarations:
  `exists_filteredHypercohomologySpectralSequence`,
  `FilteredComplex.convergesToCohomology`,
  `CochainComplex.truncationFiltration`,
  `truncationFiltration_stageInclusion_factors_ιTruncLE`,
  `moduleCohomologyAtOpen`,
  `rightDerived_spectralSequence_from_truncationFiltration`,
  `rightDerived_spectralSequence_from_truncationFiltration_matches_secondCartanEilenberg`;
- best owner abstraction: the spectral sequence is owned canonically by a filtered complex of
  `Γ(X, 𝒪_X)`-modules together with `IsAssociatedToFilteredComplex`; the source-facing
  `E'_2`-page should be expressed through the top-open cohomology owner
  `moduleCohomologyAtOpen (⊤)` applied to the canonical cohomology-sheaf owner `((H^j).obj K)`;
  its underlying additive sheaf is the chapter notation `𝓗[j](X, K)`, but the module-valued
  owner naturally takes the module sheaf itself. The bounded-below comparison with the second
  Cartan-Eilenberg spectral sequence is derived theorem-level data, not primitive structure
  fields;
- primitive data: the chosen filtered complex in `ModΓX`, the associated spectral sequence, and
  the explicit `E'_2`-page and abutment identifications, together with the canonical stage
  factorization API of `K.obj.truncationFiltration`;
- derived API: boundedness and convergence under the bounded-below hypothesis, expressed through
  the Chapter `12/20` owner `filteredComplex.convergesToCohomology spectralSequence`.

Source/core/bridge triage:
- `source-facing`: the existence theorem below with the displayed `E'_2`-page
  `H^i(X, H^j(K))`;
- `core/canonical`: `FilteredComplex`, `CohomologicalSpectralSequence`, and
  `IsAssociatedToFilteredComplex`;
- `bridge/view`: the renumbering from the truncation-filtration spectral sequence and, in the
  bounded-below case, its comparison with the second Cartan-Eilenberg spectral sequence from
  Lemma `13.21.3`.

The former local structure stored as primitive fields the filtered complex, the spectral sequence,
and convergence data that are already canonically organized upstream by the owner pair
`FilteredComplex`/`CohomologicalSpectralSequence`. This example should expose that owner package
directly on the theorem surface instead of introducing a parallel wrapper. -/

/- Example 20.29.3, stage description: the source-facing identification
`F^p K^• = τ_{\le -p}(K^•)` is recorded below through the canonical filtration
`K.truncationFiltration` and the stage-factorization owner
`truncationFiltration_stageInclusion_factors_ιTruncLE`. -/

-- Proof sketch: choose a complex representing `K`, filter it by the truncations
-- `F^p𝓕^• := τ_{\le -p}(𝓕^•)`, and apply Lemma `20.29.1` to the resulting filtered complex.
-- The `E₁`-page identifies with `H^(2p + q)(X, H^(-p)(𝓕^•))`; renumber by `p = -j` and
-- `q = i + 2j` to obtain the displayed `E'_2`-page. When
-- `K` is bounded below, Remark `20.29.2` yields boundedness and convergence, and this is the
-- second Cartan-Eilenberg spectral sequence from Lemma `13.21.3` applied to derived global
-- sections.
/-- Example 20.29.3: for any `K ∈ D(𝒪_X)`, there is a renumbered cohomological spectral
sequence with `(E'_2)^{i,j} = H^i(X, H^j(K))`. If `K` is bounded below, then the chosen spectral
sequence is bounded and converges to the hypercohomology `H^{i + j}(X, K)`. The bounded-below
comparison with the second spectral sequence of Derived Categories, Lemma `13.21.3`, is recorded
separately below on bounded-below complex representatives. -/
@[stacks 0BKM]
theorem exists_hypercohomologyFromCohomologySheavesSpectralSequence
    (K : DMod) :
    ∃ (filteredComplex : FilteredComplex ModΓX)
      (spectralSequence : CohomologicalSpectralSequence ModΓX 0)
      (associated : IsAssociatedToFilteredComplex filteredComplex spectralSequence)
      (pageTwo :
        ∀ (i : ℕ) (j : ℤ),
          (spectralSequence.page 2).X (Int.ofNat i, j) ≅
            moduleCohomologyAtOpen (⊤ : Opens X.carrier) ((HX j).obj K) i)
      (abutment :
        ∀ n : ℤ,
          filteredComplex.underlying.homology n ≅
            (HΓ n).obj ((RΓ).obj K)),
      (∃ a : ℤ, K.IsGE a) →
        CohomologicalSpectralSequence.IsBounded spectralSequence ∧
          filteredComplex.convergesToCohomology spectralSequence := sorry

-- Proof sketch: specialize the Chapter `13` bridge/view theorem
-- `rightDerived_spectralSequence_from_truncationFiltration_matches_secondCartanEilenberg` to the
-- global-sections functor `Γ(X, -)`. For a bounded-below complex `K`, a Cartan-Eilenberg
-- resolution realizes the second Cartan-Eilenberg spectral sequence in `Γ(X, 𝒪_X)`-modules, and
-- the truncation-filtration hypercohomology spectral sequence can be realized on the same
-- filtered complex. The comparison morphism is the identity on the common page-two terms
-- `H^i(X, H^j(K))` and is an isomorphism from page `1` onward.
/-- Example 20.29.3, bounded-below comparison: if `K^•` is bounded below, then the
hypercohomology-from-cohomology-sheaves spectral sequence agrees with the second spectral
sequence of Derived Categories, Lemma `13.21.3`, specialized to derived global sections.
Concretely, after choosing a Cartan-Eilenberg resolution `CE` of `K^•`, both constructions are
realized on the canonical second filtered total of `Γ(X, 𝒪_X)`-modules attached to `CE`, with a
comparison morphism that is the identity on the common `(E'_2)^{i,j} = H^i(X, H^j(K^•))` terms and an
isomorphism from page `1` onward. -/
@[stacks 0BKM]
theorem hypercohomologyFromCohomologySheavesSpectralSequence_matches_secondDerivedCategories
    (K : CochainComplex.Plus ModX)
    (CE : CartanEilenbergResolution K) :
    let T := moduleGlobalSectionsFunctor X
    let F := K.obj.truncationFiltration
    let I :=
      ((T.mapHomologicalComplex (up ℤ)).mapHomologicalComplex (up ℤ)).obj CE.doubleComplex.obj
    let FI₂ := secondDoubleComplexFilteredComplex I
    ∃ (E E' : CohomologicalSpectralSequence ModΓX 0)
      (associated : IsAssociatedToFilteredComplex FI₂ E)
      (secondAssociated : IsAssociatedToFilteredComplex FI₂ E')
      (truncationFactorization :
        ∀ p : ℤ,
          ∃ φ : F.stage p ⟶ K.obj.truncLE (-p),
            φ ≫ K.obj.ιTruncLE (-p) = F.stageInclusion p ∧ IsIso φ)
      (pageTwoIso :
        ∀ (i : ℕ) (j : ℤ),
          (E.page 2).X (Int.ofNat i, j) ≅
            moduleCohomologyAtOpen (⊤ : Opens X.carrier) (K.obj.homology j) i)
      (secondPageTwoIso :
        ∀ (i : ℕ) (j : ℤ),
          (E'.page 2).X (Int.ofNat i, j) ≅
            moduleCohomologyAtOpen (⊤ : Opens X.carrier) (K.obj.homology j) i)
      (comparison : E ⟶ E')
      ,
        (∀ (i : ℕ) (j : ℤ),
          CommSq
            ((comparison.hom 2).f (Int.ofNat i, j))
            (pageTwoIso i j).hom
            (secondPageTwoIso i j).hom
            (𝟙 _)) ∧
          ∀ (r : ℤ) (hr : 1 ≤ r) (p q : ℤ),
            IsIso ((comparison.hom r (zero_le_of_one_le hr)).f (p, q)) := by
  sorry

end AlgebraicGeometry.RingedSpace
