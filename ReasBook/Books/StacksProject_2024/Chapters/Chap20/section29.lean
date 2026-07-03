import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_20_29_1 (from Chap20) -/
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

/-! ### Remark_20_29_2 (from Chap20) -/
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

local notation "ModΓX" => ModuleCat (globalSectionsRing X)

-- Proof sketch: choose a bounded-below filtered injective replacement with finite termwise
-- filtrations and injective graded pieces as in Derived Categories, Lemma `13.26.9`. Apply global
-- sections degreewise to that replacement and take the associated spectral sequence. Since
-- bounded-below complexes of injectives compute derived global sections, the `E₁`-page is
-- `H^{p+q}(X, gr^p(K^•))`, and the finite-filtration hypothesis gives the boundedness and
-- convergence package described in the remark. This is the hypercohomology specialization of the
-- filtered right-derived spectral sequence from Derived Categories, Lemma `13.26.14`.
/-- Remark 20.29.2: if a filtered complex `\mathcal F^\bullet` of `\mathcal O_X`-modules is
bounded below and each term has a finite filtration, then the filtered hypercohomology spectral
sequence of Lemma `20.29.1` can be constructed from a bounded-below filtered injective model of
`\mathcal F^\bullet`; equivalently, there is a filtered hypercohomology spectral sequence with
`E_1^{p,q} = H^{p+q}(X, gr^p(\mathcal F^\bullet))` under these hypotheses. -/
theorem exists_filteredHypercohomologySpectralSequence_of_boundedBelow_of_finiteFiltrations
    (K : CategoryTheory.FilteredComplex (RingedSpace.Modules X))
    (hKboundedBelow : ∃ a : ℤ, K.underlying.IsStrictlyGE a)
    (hKfin : ∀ n : ℤ, ∃ a b : ℤ,
      (K.X n).filtration.obj a = ⊤ ∧ (K.X n).filtration.obj b = ⊥) :
    ∃ (filteredComplex : CategoryTheory.FilteredComplex ModΓX)
      (spectralSequence : CohomologicalSpectralSequence ModΓX 0)
      (_ : IsAssociatedToFilteredComplex filteredComplex spectralSequence)
      (_ :
        ∀ p q : ℤ,
          (spectralSequence.page 1).X (p, q) ≅
            moduleHypercohomology X (K.gradedPiece p) (p + q))
      (_ :
        ∀ n : ℤ,
          filteredComplex.underlying.homology n ≅
            moduleHypercohomology X K.underlying n),
      CohomologicalSpectralSequence.IsBounded spectralSequence ∧
        FilteredComplex.abutsToCohomology filteredComplex := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Example_20_29_3 (from Chap20) -/
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

/-! ### Example_20_29_4 (from Chap20) -/
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

/-! ### Lemma_20_29_5 (from Chap20) -/
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
