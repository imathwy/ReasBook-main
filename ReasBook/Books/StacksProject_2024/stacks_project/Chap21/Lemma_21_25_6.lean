import StacksProject_2024.Chap21.Lemma_21_25_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.GrothendieckTopology
open CategoryTheory.ObjectProperty
open scoped RingedSite.Hom
open scoped RingedSiteDerived
open scoped DerivedCategoryWithCohomologyIn

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace RingedSite.Hom

/- Domain-style sampling for Lemma 21.25.6:
- primary domain: truncation-range control for unbounded derived pushforward on ringed sites under
  the local bounded-cohomology hypotheses of Situation `21.25.5`;
- sampled project declarations:
  `CategoryTheory.GrothendieckTopology.BoundedCohomologyBasis`,
  `RingedSite.Hom.BoundedCohomologyBasis`,
  `RingedSite.Hom.modulePushforwardDerived_homologyMap_isIso_to_truncationGEStage`;
- best owner abstraction:
  `source-facing`: the Stacks statement that the canonical truncation comparison for `R(f)_*`
    is an isomorphism under the hypotheses of Lemma `21.25.6`;
  `core/canonical`: `modulePushforwardDerived_homologyMap_isIso_to_truncationGEStage`;
  `bridge/view`: the observation that the extra `BoundedCohomologyBasis f A` hypothesis from
    Situation `21.25.5` does not change the conclusion, so the source item is subsumed by the
    canonical theorem from Lemma `21.25.4`.
- primitive data:
  the morphism `f`, the weak Serre subcategory `A`, the source bounded-cohomology basis `basisX`,
  the vanishing bound `N`, the derived object `K ∈ D_A`, and the range condition `j ≥ N - n`;
- derived API:
  direct reuse of the canonical `IsIso` owner rather than a duplicate wrapper theorem with an
  unused extra hypothesis.
-/

/- Lemma 21.25.6: under Situation `21.25.5`, the canonical map
`𝓗[j](Y, Rf_* K) ⟶ 𝓗[j](Y, Rf_*(τ_{\ge -n} K))`
is an isomorphism whenever `j ≥ N - n`. In the current repository this conclusion adds no new
owner beyond Lemma `21.25.4`: the extra local bounded-cohomology-basis hypothesis on `f` from
Situation `21.25.5` is redundant for the conclusion, so this file intentionally keeps the
source-facing item as the same canonical comparison surface already owned by Lemma `21.25.4`. -/
section

variable {X Y : RingedSite.{u, v}} (f : X ⟶ Y)

local notation "ModX" => ModuleCat X
local notation "ModY" => ModuleCat Y

variable [Abelian ModX] [Abelian ModY]
variable (A : ObjectProperty ModX)
variable [IsWeakSerreClass A]
variable [f.modulePushforward.Additive]
variable [HasInjectiveResolutions (SheafOfModules X.structureSheaf)]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
variable [HasSheafify X.siteTopology AddCommGrpCat]
variable [HasExt (Sheaf X.siteTopology AddCommGrpCat)]

set_option linter.hashCommand false in
#check
  ∀ (_ : BoundedCohomologyBasis X.structureSheaf A) (N : ℤ)
    (_ : ∀ ⦃ℱ : ModX⦄ (p : ℕ), A ℱ → N < p → Limits.IsZero (R^{p}_[f](ℱ)))
    (K : D_{A}) (n : ℕ) (j : ℤ), N - (n : ℤ) ≤ j →
      IsIso
        (((R(f)_*) ⋙ DerivedCategory.homologyFunctor ModY j).map
          (derivedTruncationGEToStage K.obj n))

end

end RingedSite.Hom
