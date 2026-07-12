import StacksProject_2024.Chap12.Lemma_12_24_13
import StacksProject_2024.Chap20.Global_sections_module_owners_core

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.FilteredComplex
open AlgebraicGeometry
open scoped AlgebraicGeometry RingedSpaceDerivedPushforward

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace.{u}}

local notation "ModX" => RingedSpace.Modules X
local notation "ModY" => RingedSpace.Modules Y

local notation "QX" => (DerivedCategory.Q : CochainComplex ModX ℤ ⥤ DerivedCategory ModX)
local notation "HY" n => DerivedCategory.homologyFunctor ModY n

/- Domain-style sampling for Lemma `20.29.5`.
- primary domain: filtered complexes and their associated cohomological spectral sequences after
  applying the derived pushforward functor `R(f)_*` on `𝒪_X`-modules;
- sampled owner declarations:
  `R(f)_*`,
  `IsAssociatedToFilteredComplex`,
  `FilteredComplex.pageOneIso`,
  `FilteredComplex.convergesToCohomology`;
- best owner abstraction: a filtered complex of `𝒪_Y`-modules together with its chosen
  associated spectral sequence through the Chapter `12` owner `IsAssociatedToFilteredComplex`;
- primitive data: the higher direct images of the stages and graded pieces of `K`, together with
  the source-facing eventual stage-control predicates below and their bundled conjunction owner;
- derived API: the page-one and target comparison isomorphisms, and the boundedness/convergence
  consequences forced by the eventual stage-control hypotheses, expressed through
  `FilteredComplex.convergesToCohomology`;
- source/core/bridge triage:
  `source-facing`: `EventualStageDerivedPushforwardVanishesAbove`,
    `EventualStageDerivedPushforwardStabilizesBelow`,
    `EventualStageDerivedPushforwardControl`, and the existence theorem below;
  `core/canonical`: `FilteredComplex`, `CohomologicalSpectralSequence`, and
    `IsAssociatedToFilteredComplex`;
  `bridge/view`: the page-one and target identifications specialized to the Chapter `20` owner
    `R(f)_*`.

The local bundled structure was duplicate packaging for those canonical owners, so the main
existence theorem should return the owner-level existential package directly. -/

namespace RingedSpaceDerivedPushforwardCohomology

/- Textbook surface notation for the higher direct image `R^n(f_*)(K^•)`, expressed through the
chapter-owned derived pushforward notation `R(f)_*`. -/
scoped notation:max "R^{" n:max "}(" f:max " _*) " K:max =>
  CategoryTheory.Functor.obj (HY n)
    (CategoryTheory.Functor.obj (R(f)_*)
      (CategoryTheory.Functor.obj QX K))

end RingedSpaceDerivedPushforwardCohomology

open scoped RingedSpaceDerivedPushforwardCohomology

/-- In every cohomological degree, the higher direct images of the filtration stages vanish for
all sufficiently large filtration indices. -/
def EventualStageDerivedPushforwardVanishesAbove
    (f : X ⟶ Y) (K : FilteredComplex ModX) : Prop :=
  ∀ n : ℤ, ∃ p₀ : ℤ, ∀ ⦃p : ℤ⦄, p₀ ≤ p →
    IsZero (R^{n}(f _*) (F^{p} K))

/-- In every cohomological degree, the canonical maps
`R^n f_* (F^p K^•) ⟶ R^n f_* (K^•)` are isomorphisms for all sufficiently small
filtration indices. -/
def EventualStageDerivedPushforwardStabilizesBelow
    (f : X ⟶ Y) (K : FilteredComplex ModX) : Prop :=
  ∀ n : ℤ, ∃ p₁ : ℤ, ∀ ⦃p : ℤ⦄, p ≤ p₁ →
    IsIso
      ((HY n).map ((R(f)_*).map ((QX).map (K.stageInclusion p))))

-- The source-facing boundedness/convergence criterion in Lemma `20.29.5` is the conjunction of
-- the two eventual stage-control hypotheses above, matching the Chapter `20.29.1` surface.
/-- The combined stage-control hypotheses of Lemma `20.29.5`: in every total degree, the higher
direct images of the filtration stages vanish for `p ≫ 0` and the canonical stage maps to the
abutment are isomorphisms for `p ≪ 0`. -/
def EventualStageDerivedPushforwardControl
    (f : X ⟶ Y) (K : FilteredComplex ModX) : Prop :=
  EventualStageDerivedPushforwardVanishesAbove f K ∧
    EventualStageDerivedPushforwardStabilizesBelow f K

theorem EventualStageDerivedPushforwardControl.vanishesAbove
    {f : X ⟶ Y} {K : FilteredComplex ModX}
    (hcontrol : EventualStageDerivedPushforwardControl f K) :
    EventualStageDerivedPushforwardVanishesAbove f K :=
  hcontrol.1

theorem EventualStageDerivedPushforwardControl.stabilizesBelow
    {f : X ⟶ Y} {K : FilteredComplex ModX}
    (hcontrol : EventualStageDerivedPushforwardControl f K) :
    EventualStageDerivedPushforwardStabilizesBelow f K :=
  hcontrol.2

-- Proof sketch: the proof is the same as for Lemma `20.29.1`. Choose a filtered K-injective
-- replacement of `K`, apply the direct-image functor `f_*` degreewise to obtain a filtered
-- complex of `𝒪_Y`-modules, and take the associated spectral sequence. The `E₁`-page is
-- the higher direct image of the graded pieces, and Lemma `12.24.13` gives boundedness and
-- convergence from the bundled eventual stage-control hypothesis on the filtration stages.
/-- Lemma 20.29.5: for a morphism of ringed spaces `f : X ⟶ Y` and a filtered complex
`𝒜^•` of `𝒪_X`-modules, there exist a filtered complex of `𝒪_Y`-modules and an associated
cohomological spectral sequence realizing the filtered derived pushforward of `𝒜^•`. The theorem
returns the canonical Chapter `12` owners `filteredComplex`, `spectralSequence`, and
`associated : IsAssociatedToFilteredComplex filteredComplex spectralSequence`, together with the
source-facing `E₁`-page isomorphisms
`(spectralSequence.page 1).X (p, q) ≅ R^{p + q}(f _*) (gr^p 𝒜^•)` and the abutment isomorphisms
`filteredComplex.underlying.homology n ≅ R^{n}(f _*) 𝒜^•.underlying`. Under the bundled
stage-control owner `EventualStageDerivedPushforwardControl f K`, the same chosen spectral
sequence is bounded and converges to `(R(f)_*).obj (QX.obj 𝒜^•)`. -/
@[stacks 0FLL]
theorem exists_filteredDerivedPushforwardSpectralSequence
    (f : X ⟶ Y) (K : FilteredComplex ModX) :
    ∃ (filteredComplex : FilteredComplex ModY)
      (spectralSequence : CohomologicalSpectralSequence ModY 0)
      (associated : IsAssociatedToFilteredComplex filteredComplex spectralSequence)
      (pageOne :
        ∀ p q : ℤ,
          (spectralSequence.page 1).X (p, q) ≅
            R^{(p + q)}(f _*) (gr^{p} K))
      (abutment :
        ∀ n : ℤ,
          filteredComplex.underlying.homology n ≅
            R^{n}(f _*) K.underlying),
      EventualStageDerivedPushforwardControl f K →
        CohomologicalSpectralSequence.IsBounded spectralSequence ∧
          filteredComplex.convergesToCohomology spectralSequence := by
  sorry

end AlgebraicGeometry.RingedSpace
