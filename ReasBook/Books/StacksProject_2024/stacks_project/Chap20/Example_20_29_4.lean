import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap12.Lemma_12_25_3
import StacksProject_2024.stacks_project.Chap13.CochainComplexStupidFiltration
import StacksProject_2024.stacks_project.Chap13.Definition_13_21_1
import StacksProject_2024.stacks_project.Chap20.Remark_20_29_2

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.FilteredComplex
open ComplexShape
open CochainComplex
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable (X : RingedSpace.{u})
variable [LocallySmall (RingedSpace.Modules X)] [WellPowered (RingedSpace.Modules X)]
  [HasWidePullbacks (RingedSpace.Modules X)] [HasCoproducts (RingedSpace.Modules X)]
  [InitialMonoClass (RingedSpace.Modules X)]
  [LocallySmall (ModuleCat (globalSectionsRing X))]
  [WellPowered (ModuleCat (globalSectionsRing X))]
  [HasWidePullbacks (ModuleCat (globalSectionsRing X))]
  [HasCoproducts (ModuleCat (globalSectionsRing X))]
  [InitialMonoClass (ModuleCat (globalSectionsRing X))]

local notation "ModX" => RingedSpace.Modules X
local notation "ModΓX" => ModuleCat (globalSectionsRing X)
local notation "RΓ" => moduleDerivedGlobalSections X
local notation "QX" => (DerivedCategory.Q : CochainComplex ModX ℤ ⥤ DerivedCategory ModX)
local notation "HΓ" n => DerivedCategory.homologyFunctor ModΓX n

private theorem zero_le_of_one_le {r : ℤ} (hr : 1 ≤ r) : 0 ≤ r := by
  omega

/- Domain-style sampling for Example `20.29.4`.
- primary domain: hypercohomology spectral sequences attached to the stupid filtration on a
  cochain complex of `𝒪_X`-modules;
- sampled owner declarations:
  `CochainComplex.stupidFiltration`,
  `stupidFiltration_stage_iso_stupidTrunc`,
  `stupidFiltration_hasFiniteFiltrations`,
  `eventualStageHypercohomologyControl_of_boundedBelow_of_hasFiniteFiltrations`;
- best owner abstraction: the source-facing owner is the canonical filtered complex
  `K.stupidFiltration`, while the bounded-below conclusion should use the Chapter `12/20`
  convergence owner `filteredComplex.convergesToCohomology spectralSequence`;
- primitive data: the owner `K.stupidFiltration`, together with the existing source-facing stage
  comparison `stupidFiltration_stage_iso_stupidTrunc` and the canonical finiteness owner
  `stupidFiltration_hasFiniteFiltrations`;
- derived API in this file: the associated spectral sequence, the displayed `E₁`-page
  identification, the hypercohomology comparison on the abutment object, and the boundedness plus
  convergence consequences under the same bounded-below hypothesis;
- source/core/bridge triage:
  `source-facing`: the stupid-filtration spectral sequence and its displayed `F^p` and `E₁`
    identifications;
  `core/canonical`: `FilteredComplex`, `CohomologicalSpectralSequence`,
    `IsAssociatedToFilteredComplex`, and `FilteredComplex.convergesToCohomology`;
  `bridge/view`: the specialization of Lemma `20.29.1` from an arbitrary filtered complex to the
    source-facing owner `K.stupidFiltration`.

This example keeps the source-facing stage identification `F^p K^• ≅ σ≥p(K^•)` and the direct
`E₁`-page comparison, while the bounded-below consequence is expressed through the canonical
convergence owner rather than the weaker abutment-only predicate. -/

/- Example 20.29.4, stage description: the source-facing identification
`F^p K^• ≅ σ≥p(K^•)` is the canonical owner declaration
`CategoryTheory.CochainComplex.stupidFiltration_stage_iso_stupidTrunc`, imported from the
Chapter `13` stupid-filtration support owner. -/
recall stupidFiltration_stage_iso_stupidTrunc

/- Example 20.29.4 also uses the canonical finiteness owner for the stupid filtration. -/
recall stupidFiltration_hasFiniteFiltrations

/-- If `K^•` is bounded below, then the stupid filtration on `K^•` satisfies the stage-control
hypotheses of Remark `20.29.2`. -/
theorem eventualStageHypercohomologyControl_of_boundedBelow_stupidFiltration
    (K : CochainComplex ModX ℤ)
    (hKboundedBelow : ∃ a : ℤ, K.IsStrictlyGE a) :
    EventualStageHypercohomologyControl X K.stupidFiltration := by
  exact eventualStageHypercohomologyControl_of_boundedBelow_of_hasFiniteFiltrations
    X K.stupidFiltration hKboundedBelow K.stupidFiltration_hasFiniteFiltrations

-- Proof sketch: specialize Lemma `20.29.1` to `K.stupidFiltration`, and use the source-facing
-- `E₁`-page description coming from the stupid-filtration identification. The bounded-below
-- consequence is recorded through the canonical control owner above rather than through a separate
-- ad hoc filtration package.
/-- Example 20.29.4: for a complex `K^•` of `𝒪_X`-modules on a ringed space `X`, the stupid
filtration yields a hypercohomology spectral sequence with
`E_1^{p,q} = H^{p + q}(X, K^p[-p])`. If `K^•` is bounded below, then the same chosen spectral
sequence is bounded and converges to `H^{p + q}(X, K^•)`. The source-facing stage identification
`F^p K^• ≅ σ≥p(K^•)` is recalled above from the canonical owner and exposed again below as
returned bridge data. -/
@[stacks 0FLK]
theorem exists_stupidFiltrationHypercohomologySpectralSequence
    (K : CochainComplex ModX ℤ) :
    ∃ (filteredComplex : FilteredComplex ModΓX)
      (spectralSequence : CohomologicalSpectralSequence ModΓX 0)
      (associated : IsAssociatedToFilteredComplex filteredComplex spectralSequence)
      (stageIso : ∀ p : ℤ,
        (K.stupidFiltration).stage p ≅ K.stupidTrunc (embeddingUpIntGE p))
      (pageOneIso :
        ∀ p q : ℤ,
          (spectralSequence.page 1).X (p, q) ≅
            (HΓ (p + q)).obj ((RΓ).obj ((QX).obj ((singleFunctor ModX p).obj (K.X p)))))
      (targetIso :
        ∀ n : ℤ,
          filteredComplex.underlying.homology n ≅
            (HΓ n).obj ((RΓ).obj ((QX).obj K))),
      (∃ a : ℤ, K.IsStrictlyGE a) →
        CohomologicalSpectralSequence.IsBounded spectralSequence ∧
          filteredComplex.convergesToCohomology spectralSequence := by
  sorry

-- Proof sketch: specialize the Chapter `13` bridge/view theorem
-- `rightDerived_spectralSequence_from_stupidFiltration_matches_firstCartanEilenberg` to the
-- global-sections functor `Γ(X, -)`. For a bounded-below complex `K`, any Cartan-Eilenberg
-- resolution of `K` produces the first Cartan-Eilenberg spectral sequence in `Γ(X, 𝒪_X)`-
-- modules, and the stupid-filtration hypercohomology spectral sequence can be realized on the
-- same filtered total complex. The comparison morphism is the identity on the common page-one
-- terms `H^q(X, K^p)` and is an isomorphism from page `1` onward.
/-- Example 20.29.4, bounded-below comparison: if `K^•` is bounded below, then the stupid-
filtration hypercohomology spectral sequence agrees with the first spectral sequence of Derived
Categories, Lemma `13.21.3`, specialized to derived global sections. Concretely, after choosing a
Cartan-Eilenberg resolution of `K^•`, both constructions can be realized on the same filtered
complex of `Γ(X, 𝒪_X)`-modules, with a comparison morphism that is the identity on the common
`E_1^{p,q} = H^q(X, K^p)` terms and an isomorphism from page `1` onward. -/
@[stacks 0FLK]
theorem stupidFiltrationHypercohomologySpectralSequence_matches_firstDerivedCategories
    (K : CochainComplex.Plus ModX)
    (CE : CartanEilenbergResolution K) :
    let T := moduleGlobalSectionsFunctor X
    let I :=
      ((T.mapHomologicalComplex (up ℤ)).mapHomologicalComplex (up ℤ)).obj CE.doubleComplex.obj
    let FI₁ := firstDoubleComplexFilteredComplex I
    ∃ (E E' : CohomologicalSpectralSequence ModΓX 0)
      (associated : IsAssociatedToFilteredComplex FI₁ E)
      (firstAssociated : IsAssociatedToFilteredComplex FI₁ E')
      (stageIso : ∀ p : ℤ,
        (K.obj.stupidFiltration).stage p ≅ K.obj.stupidTrunc (embeddingUpIntGE p))
      (pageOneIso :
        ∀ p : ℤ, ∀ q : ℕ,
          (E.page 1).X (p, Int.ofNat q) ≅
            (HΓ (Int.ofNat q)).obj
              ((RΓ).obj ((QX).obj ((singleFunctor ModX p).obj (K.obj.X p)))))
      (firstPageOneIso :
        ∀ p : ℤ, ∀ q : ℕ,
          (E'.page 1).X (p, Int.ofNat q) ≅
            (HΓ (Int.ofNat q)).obj
              ((RΓ).obj ((QX).obj ((singleFunctor ModX p).obj (K.obj.X p)))))
      (comparison : E ⟶ E')
      ,
        (∀ p : ℤ, ∀ q : ℕ,
          CommSq
            ((comparison.hom 1).f (p, Int.ofNat q))
            (pageOneIso p q).hom
            (firstPageOneIso p q).hom
            (𝟙 _)) ∧
          ∀ r : ℤ, ∀ hr : 1 ≤ r, ∀ p q : ℤ,
            IsIso ((comparison.hom r (zero_le_of_one_le hr)).f (p, q)) := by
  sorry

end AlgebraicGeometry.RingedSpace
