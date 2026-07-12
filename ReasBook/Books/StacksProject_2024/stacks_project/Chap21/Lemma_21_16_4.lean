import StacksProject_2024.Chap21.SiteHigherDirectImageCore

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.GrothendieckTopology
open scoped CategoryTheory.Sheaf

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

local notation:max "R^{" p "}_[" u "]" =>
  @higherDirectImageFunctor _ _ _ _ JC JD u _ _ _ _ _ p

/-
Domain-style sampling for Lemma 21.16.4:
  `cohomologyPresheafFunctor`, and colimits;
- sampled owner declarations:
  `CategoryTheory.Limits.colimit.post`,
  `CategoryTheory.Sheaf.higherDirectImageFunctor`,
  `CategoryTheory.Sheaf.cohomologyPresheafFunctor`,
  `CategoryTheory.Functor.sheafPushforwardContinuous`,
  `CategoryTheory.Functor.rightDerived`,
  `CategoryTheory.GrothendieckTopology.Cover`;
- best owner abstraction: the higher-direct-image comparison is the canonical morphism
  `colimit.post ℱ (R^{p}_[u])`, while the source hypothesis is the local
  objectwise criterion for the canonical presheaf comparison map
  `colimit.post ℱ (cohomologyPresheafFunctor JC p)` stated over the site-cover owner `JD.Cover V`;
- primitive-vs-derived split:
  the primitive data are the diagram `ℱ`, the continuous functor `u`, the right-derived
  pushforward owner, and the covering hypothesis on the objectwise cohomology comparison over a
  canonical cover;
  an `IsIsomorphic` assertion between the source and target objects is only derived API, weaker
  than the canonical comparison-map statement already available from `colimit.post`.

Source/core/bridge triage:
- `source-facing`: the local covering hypothesis and the theorem below;
- `core/canonical`: `colimit.post` for the right-derived pushforward and for objectwise
  cohomology, together with the Chapter `21` owner `R^{p}_[u]`;
- `bridge/view`: evaluating the source-side cohomology comparison on the covering members `A.Y`.
-/

-- Proof sketch: compute `R^p u_*` as the sheafification of the objectwise cohomology presheaf,
-- use that sheafification is a left adjoint and therefore preserves colimits, and apply the local
-- criterion from Lemma `7.10.17` to the comparison map of cohomology presheaves using the covering
-- hypothesis.
/-- Lemma 21.16.4: if every object of `D` admits a covering by objects `V` for which the
canonical map `colim_i H^p(u(V), ℱ_i) ⟶ H^p(u(V), colim_i ℱ_i)` is an isomorphism, then the
canonical map `colim_i R^p u_* ℱ_i ⟶ R^p u_* (colim_i ℱ_i)`, formalized as
`colimit.post ℱ (R^{p}_[u])`,
is an isomorphism. -/
@[stacks 0H7B]
theorem higherDirectImage_colimit_iso_of_locally_objectwise_cohomology_colimit
    (ℱ : I ⥤ Sheaf JC AddCommGrpCat.{u}) (p : ℕ)
    (hcover : ∀ V : D,
      ∃ S : JD.Cover V,
        ∀ A : S.Arrow,
          IsIso ((colimit.post ℱ (cohomologyPresheafFunctor JC p)).app
            (op (u.obj A.Y)))) :
    IsIso (colimit.post ℱ (R^{p}_[u])) := sorry

end Sheaf
end CategoryTheory
