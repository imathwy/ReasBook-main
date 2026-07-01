import Mathlib
import stacks_project.Chap21.Lemma_21_9_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe w v u

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C]
variable (U : C) [Limits.HasFiniteProducts (Over U)]
variable {ι : Type w} (family : ι → Over U)

-- Proof sketch: Lemma `21.9.2` gives the cohomological `δ`-functor structure on Čech
-- cohomology. For an injective abelian presheaf `I`, Lemmas `21.9.3` and `21.9.4` identify the
-- Čech complex with a Hom complex out of an exact positive-degree resolution, so
-- `\check H^p(\mathcal U, I) = 0` for every `p > 0`. Thus the positive degrees are weakly
-- effaceable, and Lemma `12.12.4` implies universality.
/-- Lemma 21.9.6 (1): the Čech cohomology functors attached to `family` form a universal
cohomological `δ`-functor on abelian presheaves on `C`. -/
theorem cechCohomologyDeltaFunctor_isUniversal :
    CohomologicalDeltaFunctor.IsUniversal (cechCohomologyDeltaFunctor U family) := sorry

end

section

variable {C : Type u} [Category.{v} C]
variable (U : C) [Limits.HasFiniteProducts (Over U)]
variable {ι : Type w} (family : ι → Over U)

variable [HasInjectiveResolutions (Cᵒᵖ ⥤ AddCommGrpCat)]

/-- The degree-zero Čech cohomology functor attached to `family`. -/
abbrev cechH0Functor : (Cᵒᵖ ⥤ AddCommGrpCat) ⥤ AddCommGrpCat :=
  (cechCohomologyDegree U family 0).obj

-- Proof sketch: the degree-zero term of the universal `δ`-functor is `\check H^0`, while
-- part (1) shows that Čech cohomology is itself universal. Lemma `13.20.4` gives the universal
-- `δ`-functor built from the higher right derived functors of `\check H^0`, and Lemma `12.12.5`
-- identifies the two universal `δ`-functors uniquely. In positive degree this yields the stated
-- canonical functor isomorphism.
/-- Lemma 21.9.6 (2): for each `p`, the higher Čech cohomology functor
`\check H^{p+1}(\mathcal U, -)` is canonically isomorphic to the `(p + 1)`-st right derived
functor of `\check H^0(\mathcal U, -)`. -/
theorem higherCechCohomologyFunctor_isomorphic_rightDerived (p : ℕ) :
    IsIsomorphic ((cechCohomologyDegree U family (p + 1)).obj)
      ((cechH0Functor U family).rightDerived (p + 1)) := sorry

-- Proof sketch: choose the canonical injective resolution of `F`, form the double complex whose
-- `q`-th column is the Čech complex of the `q`-th injective term, and compare both
-- `\check{\mathcal C}^\bullet(\mathcal U, F)` and the complex computing
-- `R\check H^0(\mathcal U, F)` to the corresponding total complex using Lemma `12.25.4`. The
-- chosen injective-resolution complex on the right computes the derived value by the standard
-- `InjectiveResolution.isoRightDerivedObj` comparison.
/-- Lemma 21.9.6 (3): for an abelian presheaf `F`, the chosen injective-resolution complex
obtained by applying `\check H^0(\mathcal U, -)` termwise computes the right derived functors of
`\check H^0(\mathcal U, -)` at `F`. This is the canonical complex model that appears on the
right-hand side of the source functorial quasi-isomorphism. -/
theorem rightDerivedCechH0_obj_isomorphic_homology_chosenInjectiveResolution
    (F : Cᵒᵖ ⥤ AddCommGrpCat) :
    ∀ p : ℕ,
      IsIsomorphic (((cechH0Functor U family).rightDerived p).obj F)
        ((HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) p).obj
          (((cechH0Functor U family).mapHomologicalComplex (ComplexShape.up ℕ)).obj
            (injectiveResolution F).cocomplex)) := sorry

end

end CategoryTheory
