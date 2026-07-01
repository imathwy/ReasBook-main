import Mathlib
import stacks_project.Chap20.Lemma_20_10_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
variable (U : Opens X.carrier) {ι : Type u} (𝒰 : ι → Over U)
variable [HasFiniteProducts (Over U)]
variable [HasProducts (ModuleCat.{u} (X.presheaf.obj (op U)))]

/-- The degree-zero Čech cohomology functor of the covering `𝒰` on presheaves of
`\mathcal O_X`-modules. -/
abbrev ringedSpaceCechH0Functor :
    ringedSpacePresheafModules X ⥤ ModuleCat.{u} (X.presheaf.obj (op U)) :=
  (ringedSpaceCechCohomologyDegree U 𝒰 0).obj

-- Proof sketch: Lemma `20.10.2` provides the cohomological `δ`-functor structure on Čech
-- cohomology. For an injective presheaf module `ℐ`, Lemmas `20.10.3` and `20.10.4` identify the
-- Čech complex with a Hom complex out of a chain complex whose positive-degree homology vanishes,
-- so `\check H^p(\mathcal U, ℐ) = 0` for every `p > 0`. Hence the positive degrees are weakly
-- effaceable, and Lemma `12.12.4` yields universality.
/-- Lemma 20.10.5 (1): the Čech cohomology functors of the covering `𝒰` form a universal
cohomological `δ`-functor on presheaves of `\mathcal O_X`-modules. -/
theorem ringedSpaceCechCohomologyDeltaFunctor_isUniversal :
    CohomologicalDeltaFunctor.IsUniversal (ringedSpaceCechCohomologyDeltaFunctor U 𝒰) := sorry

section

variable [HasInjectiveResolutions (ringedSpacePresheafModules X)]

-- Proof sketch: the degree-zero term of the universal `δ`-functor is `\check H^0`, while part
-- `(1)` shows that Čech cohomology is itself universal. Lemma `13.20.4` gives the universal
-- `δ`-functor built from the higher right derived functors of `\check H^0`, and Lemma `12.12.5`
-- identifies the two universal `δ`-functors uniquely. In positive degree this gives the canonical
-- functor isomorphism.
/-- Lemma 20.10.5 (2): for each `p`, the higher Čech cohomology functor
`\check H^{p+1}(\mathcal U, -)` is canonically isomorphic to the `(p + 1)`-st right derived
functor of `\check H^0(\mathcal U, -)`. -/
theorem ringedSpaceHigherCechCohomologyFunctor_isomorphic_rightDerived (p : ℕ) :
    IsIsomorphic ((ringedSpaceCechCohomologyDegree U 𝒰 (p + 1)).obj)
      ((ringedSpaceCechH0Functor U 𝒰).rightDerived (p + 1)) := sorry

-- Proof sketch: choose the canonical injective resolution of `ℱ`, form the double complex whose
-- `q`-th column is the Čech complex of the `q`-th injective term, and compare both
-- `\check{\mathcal C}^\bullet(\mathcal U, \mathcal F)` and the complex computing
-- `R\check H^0(\mathcal U, \mathcal F)` to the corresponding total complex using Lemma `12.25.4`.
-- The injective-resolution complex on the right computes the derived value by the standard
-- `InjectiveResolution.isoRightDerivedObj` comparison.
/-- Lemma 20.10.5 (3): for a presheaf `\mathcal F` of `\mathcal O_X`-modules, the complex obtained
by applying `\check H^0(\mathcal U, -)` termwise to an injective resolution of `\mathcal F`
computes the right derived functors of `\check H^0(\mathcal U, -)` at `\mathcal F`. This is the
canonical complex model underlying the source functorial quasi-isomorphism. -/
theorem ringedSpaceRightDerivedCechH0_obj_isomorphic_homology_chosenInjectiveResolution
    (ℱ : ringedSpacePresheafModules X) :
    ∀ p : ℕ,
      IsIsomorphic (((ringedSpaceCechH0Functor U 𝒰).rightDerived p).obj ℱ)
        ((HomologicalComplex.homologyFunctor
            (ModuleCat.{u} (X.presheaf.obj (op U)))
            (ComplexShape.up ℕ) p).obj
          (((ringedSpaceCechH0Functor U 𝒰).mapHomologicalComplex
              (ComplexShape.up ℕ)).obj
            (injectiveResolution ℱ).cocomplex)) := sorry

end

end AlgebraicGeometry.RingedSpace
