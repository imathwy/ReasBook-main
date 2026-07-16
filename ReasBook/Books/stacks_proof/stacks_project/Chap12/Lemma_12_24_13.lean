import Mathlib
import stacks_proof.stacks_project.Chap12.Lemma_12_24_6
import stacks_proof.stacks_project.Chap12.Definition_12_24_5
import stacks_proof.stacks_project.Chap12.Definition_12_24_9
import stacks_proof.stacks_project.Chap12.Lemma_12_24_10
import stacks_proof.stacks_project.Chap12.Lemma_12_24_11

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory
namespace FilteredComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/- Domain-style sampling for Lemma `12.24.13`.
- primary domain: convergence criteria for associated cohomological spectral sequences of filtered
  cochain complexes, expressed through the induced cohomology filtration;
- sampled owner/canonical declarations in this domain:
  `FilteredComplex.inducedCohomologyFiltration`,
  `FilteredComplex.cohomologyFiltrationIsFinite`,
  `FilteredComplex.abutsToCohomology`,
  `FilteredComplex.convergesToCohomology`,
  `CohomologicalSpectralSequence.IsBounded`;
- best owner abstraction: the filtered-complex owner `K : FilteredComplex 𝒜` together with the
  chapter-level convergence and finiteness predicates already attached to it, and the canonical
  boundedness predicate on a chosen associated spectral sequence;
- primitive data: the two eventual stage-cohomology hypotheses on `K`;
- derived API: boundedness of any associated spectral sequence, finiteness of the induced
  cohomology filtration, the owner abutment statement `K.abutsToCohomology`, and convergence of a
  chosen associated spectral sequence to the cohomology of `K`;
- source/core/bridge triage:
  `source-facing`: `EventualStageCohomologyVanishesAbove`,
    `EventualStageCohomologyStabilizesBelow`;
  `core/canonical`: `CohomologicalSpectralSequence.IsBounded`,
    `FilteredComplex.cohomologyFiltrationIsFinite`, `FilteredComplex.abutsToCohomology`,
    `FilteredComplex.convergesToCohomology`;
  `bridge/view`: the stagewise cohomology maps `K.cohomologyMap p n`.

The eventual stage-control hypotheses are genuine source-facing input, but the conclusions should
land on the existing chapter owners rather than on parallel local wrappers. -/

/-- The upper-vanishing hypothesis from Lemma `12.24.13`: in each cohomological degree, the
cohomology of the filtration stages `F^p K^•` is zero for all sufficiently large `p`. -/
def EventualStageCohomologyVanishesAbove (K : FilteredComplex 𝒜) : Prop :=
  ∀ n : ℤ, ∃ p₀ : ℤ, ∀ ⦃p : ℤ⦄ (_ : p₀ ≤ p), IsZero ((K.stage p).homology n)

/-- The lower-stability hypothesis from Lemma `12.24.13`: in each cohomological degree, the map
`H^n(F^p K^•) ⟶ H^n(K^•)` is an isomorphism for all sufficiently small `p`. -/
def EventualStageCohomologyStabilizesBelow (K : FilteredComplex 𝒜) : Prop :=
  ∀ n : ℤ, ∃ p₁ : ℤ, ∀ ⦃p : ℤ⦄ (_ : p ≤ p₁), IsIso (K.cohomologyMap p n)

-- Proof sketch: acyclicity of the stage complex `F^p K^•` identifies every cohomology object
-- `H^n(F^p K^•)` with zero, so the source-facing stage-acyclicity hypothesis implies the owner
-- predicate `EventualStageCohomologyVanishesAbove`.
/-- Bridge/view layer: eventual acyclicity of the stage complexes implies the source-facing upper
vanishing hypothesis `EventualStageCohomologyVanishesAbove`. -/
theorem eventualStageCohomologyVanishesAbove_of_stageAcyclic
    (K : FilteredComplex 𝒜)
    (hAcyclic : ∃ p₀ : ℤ, ∀ ⦃p : ℤ⦄ (_ : p₀ ≤ p), (F^{p} K).Acyclic) :
    EventualStageCohomologyVanishesAbove K := by
  sorry

-- Proof sketch: if `F^p K^• ⟶ K^•` is a quasi-isomorphism, then every induced cohomology map is
-- an isomorphism, so the source-facing eventual quasi-isomorphism hypothesis implies the owner
-- predicate `EventualStageCohomologyStabilizesBelow`.
/-- Bridge/view layer: eventual quasi-isomorphism of the stage inclusions implies the source-facing
lower-stability hypothesis `EventualStageCohomologyStabilizesBelow`. -/
theorem eventualStageCohomologyStabilizesBelow_of_stageInclusion_quasiIso
    (K : FilteredComplex 𝒜)
    (hQuasi : ∃ p₁ : ℤ, ∀ ⦃p : ℤ⦄ (_ : p ≤ p₁), QuasiIso (K.stageInclusion p)) :
    EventualStageCohomologyStabilizesBelow K := by
  sorry

-- Proof sketch: use the long exact sequence attached to
-- `0 ⟶ F^{p + 1} K^• ⟶ F^p K^• ⟶ gr^p(K^•) ⟶ 0` to show that `H^n(gr^p(K^•))` vanishes for all
-- sufficiently large `p` and all sufficiently small `p`; only finitely many indices remain on
-- each total degree.
/-- Lemma 12.24.13 (1): if the stage cohomology of a filtered complex vanishes for all sufficiently
large filtration indices and stabilizes to `H^n(K^•)` for all sufficiently small filtration
indices, then the associated spectral sequence is bounded. -/
@[stacks 0BK5]
theorem associatedSpectralSequence_isBounded_of_eventual_stage_cohomology
    (K : FilteredComplex 𝒜) (E : CohomologicalSpectralSequence 𝒜 0)
    [IsAssociatedToFilteredComplex K E]
    (hvanish : EventualStageCohomologyVanishesAbove K)
    (hstabilize : EventualStageCohomologyStabilizesBelow K) :
    CohomologicalSpectralSequence.IsBounded E := sorry

-- Proof sketch: for large `p`, the stage cohomology `H^n(F^p K^•)` is zero, so the image
-- filtration step on `H^n(K^•)` is zero; for sufficiently small `p`, the map
-- `H^n(F^p K^•) ⟶ H^n(K^•)` is an isomorphism, so the corresponding filtration step is the whole
-- cohomology object.
/-- Lemma 12.24.13 (2): under the same hypotheses, the induced filtration on each cohomology
object `H^n(K^•)` is finite. -/
@[stacks 0BK5]
theorem cohomologyFiltrationIsFinite_of_eventual_stage_cohomology
    (K : FilteredComplex 𝒜)
    (hvanish : EventualStageCohomologyVanishesAbove K)
    (hstabilize : EventualStageCohomologyStabilizesBelow K) :
    K.cohomologyFiltrationIsFinite := sorry

section Convergence

variable [LocallySmall 𝒜] [WellPowered 𝒜] [HasWidePullbacks 𝒜] [HasCoproducts 𝒜]
  [InitialMonoClass 𝒜]

-- Proof sketch: the eventual stage-cohomology hypotheses force the weak-convergence equalities
-- and the separated/exhaustive cohomology-filtration equalities from Lemma `12.24.10`, so the
-- filtered complex already abuts to the cohomology of its underlying complex.
/-- The eventual vanishing and eventual stabilization hypotheses of Lemma `12.24.13` imply the
owner abutment statement `K.abutsToCohomology`. -/
theorem abutsToCohomology_of_eventual_stage_cohomology
    (K : FilteredComplex 𝒜)
    (hvanish : EventualStageCohomologyVanishesAbove K)
    (hstabilize : EventualStageCohomologyStabilizesBelow K) :
    K.abutsToCohomology := sorry

-- Proof sketch: combine `abutsToCohomology_of_eventual_stage_cohomology` with boundedness of the
-- chosen associated spectral sequence, which gives regularity, and finiteness of the induced
-- cohomology filtration, which yields the completeness required in Definition `12.24.9`.
/-- Lemma 12.24.13 (3): under the eventual vanishing and eventual stabilization hypotheses, the
associated spectral sequence converges to the cohomology of the underlying complex. -/
@[stacks 0BK5]
theorem associatedSpectralSequence_convergesToCohomology_of_eventual_stage_cohomology
    (K : FilteredComplex 𝒜) (E : CohomologicalSpectralSequence 𝒜 0)
    [IsAssociatedToFilteredComplex K E]
    (hvanish : EventualStageCohomologyVanishesAbove K)
    (hstabilize : EventualStageCohomologyStabilizesBelow K) :
    K.convergesToCohomology E := sorry

end Convergence

end FilteredComplex
end CategoryTheory
