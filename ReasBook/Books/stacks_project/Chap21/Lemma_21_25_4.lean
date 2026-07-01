import Mathlib
import stacks_project.Chap13.Remark_13_34_5
import stacks_project.Chap18.Definition_18_6_1
import stacks_project.Chap18.Lemma_18_24_4
import stacks_project.Chap21.Situation_21_25_1
import stacks_project.Chap21.Lemma_21_20_5

-- Declarations for this item will be appended below by the statement pipeline.

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
-- target ringed sites and the weak Serre property of `A'`, force every cohomology sheaf of
-- `Rf_* K` to lie in `A'`.
/-- Lemma 21.25.4 (1): under the bounded-cohomological-dimension hypotheses of Situation
`21.25.1` on both the source and target ringed sites, if higher direct images of objects of the
weak Serre subcategory `\mathcal A` land in `\mathcal A'` and vanish above the bound `N`, then
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
