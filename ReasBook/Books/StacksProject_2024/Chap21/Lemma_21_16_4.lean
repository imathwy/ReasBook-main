import stacks_project.Chap20.Lemma_20_19_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.GrothendieckTopology

noncomputable section

universe u

namespace CategoryTheory
namespace Sheaf

variable {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
variable {I : Type u} [Category.{u} I]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable (u : D ⥤ C) [Functor.IsContinuous u JD JC]
variable [HasSheafify JC AddCommGrpCat.{u}] [HasSheafify JD AddCommGrpCat.{u}]
variable [HasExt (Sheaf JC AddCommGrpCat.{u})]
variable [HasInjectiveResolutions (Sheaf JC AddCommGrpCat.{u})]
variable [HasColimitsOfShape I (Sheaf JC AddCommGrpCat.{u})]
variable [HasColimitsOfShape I (Sheaf JD AddCommGrpCat.{u})]
variable [Functor.Additive (u.sheafPushforwardContinuous AddCommGrpCat.{u} JD JC)]

-- Proof sketch: compute `R^p f_*` as the sheafification of the objectwise cohomology presheaf,
-- use that sheafification is a left adjoint and therefore preserves colimits, and apply the local
-- criterion from Lemma `7.10.17` to the comparison map of cohomology presheaves using the covering
-- hypothesis.
/-- Lemma 21.16.4: if every object of `\mathcal D` admits a covering by objects `V` for which the
canonical map `\operatorname{colim}_i H^p(u(V), \mathcal F_i) \to H^p(u(V), \operatorname{colim}_i
\mathcal F_i)` is an isomorphism, then the `p`-th higher direct image of the colimit sheaf is the
colimit of the `p`-th higher direct images. -/
theorem higherDirectImage_colimit_iso_of_locally_objectwise_cohomology_colimit
    (ℱ : I ⥤ Sheaf JC AddCommGrpCat.{u}) (p : ℕ)
    (hcover : ∀ V : D,
      ∃ (ι : Type u) (W : ι → D) (f : ∀ i, W i ⟶ V),
        Sieve.ofArrows W f ∈ JD V ∧
          ∀ i,
            IsIso ((colimit.post ℱ (cohomologyPresheafFunctor JC p)).app
              (op (u.obj (W i))))) :
    IsIsomorphic
      (((u.sheafPushforwardContinuous AddCommGrpCat.{u} JD JC).rightDerived p).obj (colimit ℱ))
      (colimit (ℱ ⋙ (u.sheafPushforwardContinuous AddCommGrpCat.{u} JD JC).rightDerived p)) := sorry

end Sheaf
end CategoryTheory
