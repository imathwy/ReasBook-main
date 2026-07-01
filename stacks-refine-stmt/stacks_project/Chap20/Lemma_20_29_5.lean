import Mathlib
import stacks_project.Chap20.Lemma_20_29_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.FilteredComplex
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace.{u}}

variable [LocallySmall (RingedSpace.Modules X)] [WellPowered (RingedSpace.Modules X)]
  [HasWidePullbacks (RingedSpace.Modules X)] [HasCoproducts (RingedSpace.Modules X)]
  [InitialMonoClass (RingedSpace.Modules X)]
  [IsGrothendieckAbelian (RingedSpace.Modules X)]
  [LocallySmall (RingedSpace.Modules Y)] [WellPowered (RingedSpace.Modules Y)]
  [HasWidePullbacks (RingedSpace.Modules Y)] [HasCoproducts (RingedSpace.Modules Y)]
  [InitialMonoClass (RingedSpace.Modules Y)]

/-- The `n`-th higher direct image of a complex of `\mathcal O_X`-modules, computed as the
`n`-th homology sheaf of the unbounded derived pushforward `Rf_*`. -/
abbrev moduleDerivedPushforwardCohomology
    (f : X ⟶ Y) (K : CochainComplex (RingedSpace.Modules X) ℤ) (n : ℤ) :
    (RingedSpace.Modules Y) :=
  (DerivedCategory.homologyFunctor (RingedSpace.Modules Y) n).obj
    ((moduleDerivedPushforward f).obj
      ((DerivedCategory.Q : CochainComplex (RingedSpace.Modules X) ℤ ⥤
        DerivedCategory (RingedSpace.Modules X)).obj K))

/-- The map on higher direct images induced by a morphism of complexes of `\mathcal O_X`-modules.
-/
abbrev moduleDerivedPushforwardCohomologyMap
    (f : X ⟶ Y) {K L : CochainComplex (RingedSpace.Modules X) ℤ} (φ : K ⟶ L) (n : ℤ) :
    moduleDerivedPushforwardCohomology f K n ⟶
      moduleDerivedPushforwardCohomology f L n :=
  (DerivedCategory.homologyFunctor (RingedSpace.Modules Y) n).map
    ((moduleDerivedPushforward f).map
      ((DerivedCategory.Q : CochainComplex (RingedSpace.Modules X) ℤ ⥤
        DerivedCategory (RingedSpace.Modules X)).map φ))

/-- The canonical map
`R^n f_* (F^p K^\bullet) \to R^n f_* (K^\bullet)` induced by the filtration-stage inclusion. -/
abbrev filteredDerivedPushforwardStageMap
    (f : X ⟶ Y) (K : CategoryTheory.FilteredComplex (RingedSpace.Modules X)) (p n : ℤ) :
    moduleDerivedPushforwardCohomology f (K.stage p) n ⟶
      moduleDerivedPushforwardCohomology f (K.underlying) n :=
  moduleDerivedPushforwardCohomologyMap f
    (K.stageInclusion p) n

/-- In every cohomological degree, the higher direct images of the filtration stages vanish for
all sufficiently large filtration indices. -/
def EventualStageDerivedPushforwardVanishesAbove
    (f : X ⟶ Y) (K : CategoryTheory.FilteredComplex (RingedSpace.Modules X)) : Prop :=
  ∀ n : ℤ, ∃ p₀ : ℤ, ∀ ⦃p : ℤ⦄, p₀ ≤ p →
    IsZero (moduleDerivedPushforwardCohomology f (K.stage p) n)

/-- In every cohomological degree, the canonical maps
`R^n f_* (F^p K^\bullet) \to R^n f_* (K^\bullet)` are isomorphisms for all sufficiently small
filtration indices. -/
def EventualStageDerivedPushforwardStabilizesBelow
    (f : X ⟶ Y) (K : CategoryTheory.FilteredComplex (RingedSpace.Modules X)) : Prop :=
  ∀ n : ℤ, ∃ p₁ : ℤ, ∀ ⦃p : ℤ⦄, p ≤ p₁ →
    IsIso (filteredDerivedPushforwardStageMap f K p n)

/-- A filtered direct-image spectral sequence for a filtered complex of `\mathcal O_X`-modules,
recorded by a filtered complex of `\mathcal O_Y`-modules together with its associated
cohomological spectral sequence. -/
structure FilteredDerivedPushforwardSpectralSequence
    (f : X ⟶ Y) (K : CategoryTheory.FilteredComplex (RingedSpace.Modules X)) where
  /-- The filtered complex of `\mathcal O_Y`-modules producing the spectral sequence. -/
  filteredComplex : CategoryTheory.FilteredComplex (RingedSpace.Modules Y)
  /-- The chosen cohomological spectral sequence. The ambient
  `CohomologicalSpectralSequence` API records that `d_r` has bidegree `(r, -r + 1)`. -/
  spectralSequence : CohomologicalSpectralSequence (RingedSpace.Modules Y) 0
  /-- The `E_1`-page identifies with the higher direct images of the graded pieces
  `gr^p(K^\bullet)`. -/
  pageOneIso :
    ∀ p q : ℤ,
      (spectralSequence.page 1).X (p, q) ≅
        moduleDerivedPushforwardCohomology f
          (K.gradedPiece p) (p + q)
  /-- The eventual vanishing and eventual stabilization hypotheses force the spectral sequence to
  be bounded. -/
  bounded_of_eventualStageDerivedPushforward_control :
    EventualStageDerivedPushforwardVanishesAbove f K →
      EventualStageDerivedPushforwardStabilizesBelow f K →
      CohomologicalSpectralSequence.IsBounded spectralSequence
  /-- The same hypotheses force the spectral sequence to abut to the cohomology sheaves of the
  derived direct image of the underlying complex. -/
  abuts_of_eventualStageDerivedPushforward_control :
    EventualStageDerivedPushforwardVanishesAbove f K →
      EventualStageDerivedPushforwardStabilizesBelow f K →
      CategoryTheory.FilteredComplex.abutsToCohomology filteredComplex
  /-- The abutment identifies with the higher direct images of the underlying complex `K^\bullet`.
  -/
  targetIso :
    ∀ n : ℤ,
      filteredComplex.underlying.homology n ≅
        moduleDerivedPushforwardCohomology f
          (K.underlying) n

-- Proof sketch: the proof is the same as for Lemma `20.29.1`. Choose a filtered K-injective
-- replacement of `K`, apply the direct-image functor `f_*` degreewise to obtain a filtered
-- complex of `\mathcal O_Y`-modules, and take the associated spectral sequence. The `E₁`-page is
-- the higher direct image of the graded pieces, and Lemma `12.24.13` gives boundedness and
-- abutment from the eventual vanishing and stabilization hypotheses on the filtration stages.
/-- Lemma 20.29.5: for a morphism of ringed spaces `f : X ⟶ Y` and a filtered complex
`\mathcal F^\bullet` of `\mathcal O_X`-modules, there exists a canonical cohomological spectral
sequence of bigraded `\mathcal O_Y`-modules with
`E_1^{p,q} = R^{p + q} f_* \operatorname{gr}^p(\mathcal F^\bullet)`. If for every `n` the higher
direct images `R^n f_* (F^p \mathcal F^\bullet)` vanish for `p ≫ 0` and the canonical maps
`R^n f_* (F^p \mathcal F^\bullet) \to R^n f_* (\mathcal F^\bullet)` are isomorphisms for
`p ≪ 0`, then the chosen spectral sequence is bounded and converges to `Rf_* \mathcal F^\bullet`.
-/
theorem exists_filteredDerivedPushforwardSpectralSequence
    (f : X ⟶ Y) (K : CategoryTheory.FilteredComplex (RingedSpace.Modules X)) :
    Nonempty (FilteredDerivedPushforwardSpectralSequence f K) := sorry

end AlgebraicGeometry.RingedSpace
