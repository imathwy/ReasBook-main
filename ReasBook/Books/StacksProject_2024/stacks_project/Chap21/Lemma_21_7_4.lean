import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap21.«21_3_0_2»
import StacksProject_2024.stacks_project.Chap21.Lemma_21_7_4_core
import StacksProject_2024.stacks_project.Chap21.Lemma_21_20_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped RingedSite.Hom
open scoped RingedSiteCohomology

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace RingedSite.Hom

/- Domain-style sampling for Lemma 21.7.4:
- primary domain: higher direct images of sheaves of modules on a morphism of ringed sites and
  the comparison with the sheafification of objectwise cohomology of the underlying abelian sheaf;
- sampled owner declarations:
  `RingedSite.Hom.higherDirectImageModule`,
  `RingedSite.Hom.modulePushforward`,
  `DerivedCategory.singleFunctor`,
  `RingedSite.Hom.objectwiseCohomologyPresheaf`,
  `CategoryTheory.presheafToSheaf`,
  `RingedSite.Hom.underlyingAbelianSheafFunctor`;
- best owner abstraction: the source-facing specialization should use the Chapter 21 higher direct
  image owner `R^{i}_[f](ℱ)` together with the underlying-abelian-sheaf bridge on `Y`; the
  canonical comparison theorem
  `sourceObjectwiseCohomologyPresheaf_sheafification_isomorphic_underlyingAbelianCohomologySheaf`,
  specialized to the degree-zero derived object `ℱ[0]`, supplies the proof;
- primitive data: the bundled morphism `f`, an `𝒪_X`-module
  `ℱ : SheafOfModules X.structureSheaf`, and the degree `i`;
- derived API: the degree-zero derived object `ℱ[0]`, the Chapter 21 owner
  `R^{i}_[f](ℱ)` for the higher direct image, the presheaf owner `𝓗'[i](X, ℱ[0])`, and the
  underlying-abelian-sheaf functor on `Y`.

Source/core/bridge triage:
- `source-facing`: the degree-zero specialization `K = ℱ[0]`, expressed as the comparison between
  the sheaf associated to `V ↦ H^i(f^{-1}(V), ℱ)` and the underlying abelian sheaf of
  `R^{i}_[f](ℱ)`;
- `core/canonical`: `sourceObjectwiseCohomologyPresheaf_sheafification_isomorphic_underlyingAbelianCohomologySheaf`,
  `RingedSite.Hom.higherDirectImageModule`, `DerivedCategory.singleFunctor`,
  `RingedSite.Hom.objectwiseCohomologyPresheaf`, `RingedSite.Hom.underlyingAbelianSheafFunctor`,
  and `presheafToSheaf`;
- `bridge/view`: the source-facing specialization theorem below, obtained by rewriting the target
  of Lemma `21.20.6` through the Chapter 21 higher-direct-image owner rather than introducing a
  second local theorem owner.
-/

section

variable {X Y : RingedSite.{u, v}} (f : X ⟶ Y)
variable [Functor.Additive f.modulePushforward]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
variable [HasSheafify Y.siteTopology AddCommGrpCat.{max u v}]
variable [IsGrothendieckAbelian.{max u v} (ModuleCat X)]

local notation "single0" => DerivedCategory.singleFunctor (SheafOfModules X.structureSheaf) (0 : ℤ)

variable (ℱ : ModuleCat X) (i : ℕ)

/- Lemma 21.7.4 is the degree-zero specialization of the canonical comparison theorem
`sourceObjectwiseCohomologyPresheaf_sheafification_isomorphic_underlyingAbelianCohomologySheaf`
from Lemma 21.20.6. -/
recall sourceObjectwiseCohomologyPresheaf_sheafification_isomorphic_underlyingAbelianCohomologySheaf

/-- Lemma 21.7.4: for a module sheaf `ℱ`, the underlying abelian sheaf of `R^{i}_[f](ℱ)` is
canonically isomorphic to the sheaf associated to the presheaf `V ↦ H^i(f⁻¹(V), ℱ)`. This is the
degree-zero specialization of Lemma `21.20.6`. -/
@[stacks 072W]
theorem sourceObjectwiseCohomologyPresheaf_sheafification_isomorphic_underlyingAbelianHigherDirectImageModule
    (ℱ : ModuleCat X) (i : ℕ) :
    IsIsomorphic
      ((presheafToSheaf Y.siteTopology AddCommGrpCat.{max u v}).obj
        (f.base.op ⋙ 𝓗'[(i : ℤ)](X, (single0).obj ℱ)))
      ((underlyingAbelianSheafFunctor Y).obj (R^{i}_[f](ℱ))) := by
  letI : HasInjectiveResolutions (ModuleCat X) := inferInstance
  rcases
    sourceObjectwiseCohomologyPresheaf_sheafification_isomorphic_underlyingAbelianCohomologySheaf
      f ((single0).obj ℱ) (i : ℤ) with
    ⟨eSource⟩
  have hHigher :
      IsIsomorphic
        (R^{i}_[f](ℱ))
        ((DerivedCategory.homologyFunctor (ModuleCat Y) (i : ℤ)).obj
          ((modulePushforwardDerived f).obj ((single0).obj ℱ))) := by
    rcases
      Functor.rightDerived_isomorphic_to_singleFunctorCompHomologyFunctor
        f.modulePushforward i (modulePushforwardDerived f) with
      ⟨eHigher⟩
    simpa [higherDirectImageModule] using
      (⟨eHigher.app ℱ⟩ :
        IsIsomorphic
          ((f.modulePushforward.rightDerived i).obj ℱ)
          ((DerivedCategory.singleFunctor (ModuleCat X) (0 : ℤ) ⋙
              modulePushforwardDerived f ⋙
              DerivedCategory.homologyFunctor (ModuleCat Y) (i : ℤ)).obj ℱ))
  rcases hHigher with ⟨eHigher⟩
  exact ⟨eSource ≪≫ (underlyingAbelianSheafFunctor Y).mapIso eHigher.symm⟩

end

end RingedSite.Hom
