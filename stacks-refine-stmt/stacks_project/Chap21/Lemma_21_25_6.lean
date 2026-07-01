import Mathlib
import stacks_project.Chap13.Remark_13_34_5
import stacks_project.Chap21.Remark_21_19_3
import stacks_project.Chap21.Situation_21_25_1
import stacks_project.Chap21.Situation_21_25_5

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
