import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_21_25_2 (from Chap21) -/
open CategoryTheory
open CategoryTheory.GrothendieckTopology

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

section

/-- The abelian category `\mathrm{Mod}(\mathcal O_X)` of sheaves of modules on the ringed site
`X`. -/
private abbrev RingedSiteModuleCat (X : RingedSite.{u, v}) :=
  SheafOfModules X.structureSheaf

variable (X : RingedSite.{u, v})

local notation "ModX" => RingedSiteModuleCat X

variable [HasWeakSheafify X.siteTopology AddCommGrpCat]
variable [HasSheafify X.siteTopology AddCommGrpCat]
variable [HasExt (Sheaf X.siteTopology AddCommGrpCat)]
variable [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat]
variable [Abelian ModX]

variable (A : ObjectProperty ModX)
variable [A.ContainsZero] [A.IsClosedUnderKernels] [A.IsClosedUnderCokernels]
variable [A.IsClosedUnderExtensions]

-- Proof sketch: an object of `D_\mathcal A(\mathcal O_X)` has all cohomology sheaves in `A`.
-- Apply Lemma `21.23.8` to the bounded-cohomology basis from Situation `21.25.1`, using its
-- vanishing hypothesis for the negative cohomology sheaves of `E.obj`; Remark `13.34.5`
-- identifies the compatible comparison morphism with the textbook map
-- `E \to R\!\varprojlim_n \tau_{\ge -n} E`.
/-- Lemma 21.25.2: in Situation `21.25.1`, if `E` is a derived `\mathcal O_X`-module whose
cohomology sheaves all lie in the weak LinearRepresentations_Serre_1977 subcategory `\mathcal A`, then any compatible
morphism formalizing the canonical map
`E \to R\!\varprojlim_n \tau_{\ge -n} E` is an isomorphism in `D(\mathcal O_X)`. -/
theorem truncationComparison_isIso_of_mem_derivedCategoryWithCohomologyIn
    (basis : bounded_cohomology_basis X.structureSheaf A)
    (E : DerivedCategoryWithCohomologyIn A)
    (K : DerivedCategory ModX)
    (c : E.obj ⟶ K)
    (hc : IsTruncationDerivedLimitComparison E.obj K c) :
    IsIso c := sorry

end

/-! ### Lemma_21_25_3 (from Chap21) -/
open CategoryTheory
open Opposite
open CategoryTheory.GrothendieckTopology
open DerivedCategory.TStructure

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

section

/-- The abelian category `\mathrm{Mod}(\mathcal O_X)` of sheaves of modules on the ringed site
`X`. -/
private abbrev RingedSiteModuleCat (X : RingedSite.{u, v}) :=
  SheafOfModules X.structureSheaf

variable (X : RingedSite.{u, v})
variable [HasWeakSheafify X.siteTopology AddCommGrpCat]
variable [HasSheafify X.siteTopology AddCommGrpCat]
variable [HasExt (Sheaf X.siteTopology AddCommGrpCat)]
variable [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat]

local notation "ModX" => RingedSiteModuleCat X

variable [Abelian ModX]
variable [CategoryWithHomology ModX]
variable [IsGrothendieckAbelian ModX]

variable (A : ObjectProperty ModX)
variable [A.ContainsZero] [A.IsClosedUnderKernels] [A.IsClosedUnderCokernels]
variable [A.IsClosedUnderExtensions]

-- Proof sketch: use the bounded-cohomology basis from Situation `21.25.1` to reduce to basis
-- objects with uniformly bounded higher cohomology for `A`-valued sheaves. For a fixed degree `j`
-- and basis object `V`, compare the spectral sequences computing `H^*(V, K_n)` from the
-- cohomology sheaves `H^q(K_n)`; bounded-below hypotheses and eventual constancy of the
-- cohomology sheaves force the groups `H^(j-1)(V, K_n)` and `H^j(V, K_n)` to stabilize. Lemma
-- `21.23.6` then gives injectivity of the Milnor comparison map on the cohomology sheaf of
-- `R lim K_n`, and Lemmas `21.20.3` and `21.23.2` give surjectivity after passing to a covering,
-- yielding the claimed identification of cohomology sheaves.
/-- Lemma 21.25.3: in Situation `21.25.1`, let `(K_n)` be a sequential inverse system in
`D^+_\mathcal A(\mathcal O_X)` and let `K` be a derived limit of this tower. If for every degree
`j` the cohomology sheaves `H^j(K_n)` all lie in `\mathcal A` and are eventually constant with
eventual value `ℋ j`, then the degree-`j` cohomology sheaf of `K = R \!\varprojlim_n K_n` is
isomorphic to `ℋ j`. -/
lemma derivedLimit_cohomology_isomorphic_of_eventually_constant
    (basis : bounded_cohomology_basis X.structureSheaf A)
    (Ksys : ℕᵒᵖ ⥤ DerivedCategory ModX)
    (K : DerivedCategory ModX)
    (ℋ : ℤ → ModX)
    (hK : IsDerivedLimit Ksys K)
    (hboundedBelow : ∀ n : ℕ,
      (t.plus : ObjectProperty (DerivedCategory ModX)) (Ksys.obj (op n)))
    (hcohomology_mem : ∀ n : ℕ, ∀ j : ℤ,
      A ((DerivedCategory.homologyFunctor ModX j).obj (Ksys.obj (op n))))
    (hℋ_mem : ∀ j : ℤ, A (ℋ j))
    (heventually_constant : ∀ j : ℤ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      IsIsomorphic
        ((DerivedCategory.homologyFunctor ModX j).obj (Ksys.obj (op n)))
        (ℋ j)) :
    ∀ j : ℤ, IsIsomorphic ((DerivedCategory.homologyFunctor ModX j).obj K) (ℋ j) := sorry

end

/-! ### Lemma_21_25_4 (from Chap21) -/
open CategoryTheory
open CategoryTheory.GrothendieckTopology

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace RingedSite.Hom

section

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)

local notation "ModX" => ModuleCat X
local notation "ModY" => ModuleCat Y

variable [HasWeakSheafify X.siteTopology AddCommGrpCat]
variable [HasSheafify X.siteTopology AddCommGrpCat]
variable [HasExt (Sheaf X.siteTopology AddCommGrpCat)]
variable [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat]
variable [HasWeakSheafify Y.siteTopology AddCommGrpCat]
variable [HasSheafify Y.siteTopology AddCommGrpCat]
variable [HasExt (Sheaf Y.siteTopology AddCommGrpCat)]
variable [Y.siteTopology.WEqualsLocallyBijective AddCommGrpCat]

variable [Abelian ModX] [Abelian ModY]
variable [HasInjectiveResolutions (ModuleCat X)]
variable [Functor.Additive (modulePushforward f)]
variable [f.modulePushforward.Additive]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]

/-- The object property on `D(\mathcal O_X)` consisting of complexes whose every cohomology
sheaf lies in the chosen object property `A ⊆ \mathrm{Mod}(\mathcal O_X)`. -/
private abbrev derivedCategoryCohomologyInProperty (A : ObjectProperty ModX) :
    ObjectProperty (DerivedCategory ModX) :=
  fun K ↦ ∀ j : ℤ, A ((DerivedCategory.homologyFunctor ModX j).obj K)

/-- The full subcategory `D_A(\mathcal O_X) ⊆ D(\mathcal O_X)` cut out by the cohomology-in-`A`
condition. -/
private abbrev DerivedCategoryWithCohomologyIn (A : ObjectProperty ModX) :=
  (derivedCategoryCohomologyInProperty A).FullSubcategory

variable (A : ObjectProperty ModX) (A' : ObjectProperty ModY)
variable [A.ContainsZero] [A.IsClosedUnderKernels] [A.IsClosedUnderCokernels]
variable [A.IsClosedUnderExtensions]
variable [A'.ContainsZero] [A'.IsClosedUnderKernels] [A'.IsClosedUnderCokernels]
variable [A'.IsClosedUnderExtensions]

variable (basisX : bounded_cohomology_basis X.structureSheaf A)
variable (basisY : bounded_cohomology_basis Y.structureSheaf A')
variable (N : ℤ)
variable (h_mem : ∀ (p : ℕ) ⦃ℱ : ModX⦄, A ℱ →
  A' (((modulePushforward f).rightDerived p).obj ℱ))
variable (h_vanish : ∀ (p : ℕ) ⦃ℱ : ModX⦄, A ℱ → N < p →
  Limits.IsZero (((modulePushforward f).rightDerived p).obj ℱ))

-- Proof sketch: apply the spectral sequence with
-- `E₂^{p,q} = R^p f_* H^q(K)` to each cohomological degree of `K`. The hypotheses on
-- `R^p f_*` over objects of `A`, together with the bounded-cohomology bases on the source and
-- target ringed sites and the weak LinearRepresentations_Serre_1977 property of `A'`, force every cohomology sheaf of
-- `Rf_* K` to lie in `A'`.
/-- Lemma 21.25.4 (1): under the bounded-cohomological-dimension hypotheses of Situation
`21.25.1` on both the source and target ringed sites, if higher direct images of objects of the
weak LinearRepresentations_Serre_1977 subcategory `\mathcal A` land in `\mathcal A'` and vanish above the bound `N`, then
for every `K ∈ D_\mathcal A(\mathcal O_X)` the derived direct image `Rf_* K` has all cohomology
sheaves in `\mathcal A'`. -/
theorem modulePushforwardDerived_mem_derivedCategoryWithCohomologyIn
    (K : DerivedCategoryWithCohomologyIn A) :
    derivedCategoryCohomologyInProperty A' ((modulePushforwardDerived f).obj K.obj) := sorry

-- Proof sketch: specialize the truncation-range control for unbounded right derived functors to
-- `f_*`. The bound `R^p f_* = 0` for `p > N`, together with the fact that the cohomology sheaves
-- of `K` lie in `A`, gives the usual spectral-sequence comparison showing that truncating `K`
-- below degree `-n` does not change `H^j(Rf_* K)` once `j ≥ N - n`.
/-- Lemma 21.25.4 (2): under the same hypotheses, for `K ∈ D_\mathcal A(\mathcal O_X)` the
canonical map on degree-`j` cohomology sheaves
`H^j(Rf_* K) \to H^j(Rf_*(\tau_{\ge -n} K))` is an isomorphism whenever `j ≥ N - n`. -/
theorem modulePushforwardDerived_homology_isomorphic_to_truncationGEStage
    (K : DerivedCategoryWithCohomologyIn A) (n : ℕ) (j : ℤ)
    (hj : N - (n : ℤ) ≤ j) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor ModY j).obj
        ((modulePushforwardDerived f).obj K.obj))
      ((DerivedCategory.homologyFunctor ModY j).obj
        ((modulePushforwardDerived f).obj (τ≥[n](K.obj)))) := sorry

end

end RingedSite.Hom

/-! ### Lemma_21_25_6 (from Chap21) -/
open CategoryTheory
open CategoryTheory.GrothendieckTopology
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

noncomputable section

universe w u v

attribute [local instance] HasDerivedCategory.standard

namespace RingedSite.Hom

section

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)

local notation "ModX" => ModuleCat X
local notation "ModY" => ModuleCat Y

variable [HasSheafify X.siteTopology AddCommGrpCat]
variable [HasExt (Sheaf X.siteTopology AddCommGrpCat)]
variable [Abelian ModX] [Abelian ModY]
variable [HasInjectiveResolutions (SheafOfModules X.structureSheaf)]
variable [f.modulePushforward.Additive]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]

variable (A : ObjectProperty ModX)
variable [A.ContainsZero] [A.IsClosedUnderKernels] [A.IsClosedUnderCokernels]
variable [A.IsClosedUnderExtensions]

/-- The object property on `D(\mathcal O_X)` cut out by requiring all cohomology sheaves to lie
in `\mathcal A`. -/
abbrev moduleDerivedCohomologyInProperty (A : ObjectProperty ModX) :
    ObjectProperty (DerivedCategory ModX) :=
  fun K ↦ ∀ i : ℤ, A ((DerivedCategory.homologyFunctor ModX i).obj K)

/-- The full subcategory `D_\mathcal A(\mathcal O_X)` of derived `\mathcal O_X`-modules whose
cohomology sheaves all lie in `\mathcal A`. -/
abbrev moduleDerivedWithCohomologyIn (A : ObjectProperty ModX) :=
  (moduleDerivedCohomologyInProperty A).FullSubcategory

-- Proof sketch: combine the truncation-limit control from Situation `21.25.1` on the source
-- with the objectwise bounded-cohomology hypothesis from Situation `21.25.5` on the morphism
-- `f`. The spectral sequence for `Rf_*` applied to the truncation triangle shows that the cone of
-- `Rf_* K ⟶ Rf_*(τ_{\ge -n} K)` has vanishing degree-`j` cohomology once `j ≥ N - n`.
/-- Lemma 21.25.6: let `f : (\mathcal C, \mathcal O) \to (\mathcal C', \mathcal O')` be a
morphism of ringed sites. Assume there is an integer `N` such that `(\mathcal C, \mathcal O)` and
`\mathcal A` satisfy Situation `21.25.1`, `f` and `\mathcal A` satisfy Situation `21.25.5`, and
`R^p f_* \mathcal F = 0` for every `p > N` and every `\mathcal F ∈ \mathcal A`. Then for
`K ∈ D_\mathcal A(\mathcal O)` the canonical map
`H^j(Rf_* K) \to H^j(Rf_*(\tau_{\ge -n} K))` is an isomorphism for `j ≥ N - n`. -/
theorem modulePushforwardDerived_homologyMap_isIso_of_bounded_cohomological_dimension
    (basisX : CategoryTheory.GrothendieckTopology.bounded_cohomology_basis
      X.structureSheaf A)
    (basisf : bounded_cohomology_basis f A)
    (N : ℤ)
    (h_vanish : ∀ (p : ℕ) ⦃ℱ : ModX⦄, A ℱ → N < p →
      IsZero ((f.modulePushforward.rightDerived p).obj ℱ))
    (K : moduleDerivedWithCohomologyIn A) (n : ℕ) (j : ℤ)
    (hj : N - (n : ℤ) ≤ j) :
    IsIso
      ((DerivedCategory.homologyFunctor ModY j).map
        ((modulePushforwardDerived f).map
          (derivedTruncationGEToStage K.obj n))) := sorry

end

end RingedSite.Hom
