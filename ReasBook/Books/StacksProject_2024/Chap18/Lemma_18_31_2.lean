import Mathlib
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap18.Definition_18_31_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open scoped RingedSite.Hom

noncomputable section

universe u v

namespace RingedSite.Hom

/- Domain-style sampling for Lemma 18.31.2:
- primary domain: exactness of inverse-image and pullback functors on sheaves and module sheaves;
- sampled canonical declarations:
  `exactFunctor`,
  `F.sheafPullback`,
  `RingedSite.Hom.modulePullback`,
  `RingedSite.Hom.IsFlat.pullback_exact`;
- best owner abstraction for part `(2)`: `RingedSite.Hom.IsFlat`.

Primitive-vs-derived split:
- primitive data: a morphism of ringed sites `f : X ⟶ Y` together with the flatness structure
  `[f.IsFlat]`;
- derived API: exactness of the canonical pullback functor on module sheaves, exposed by
  `RingedSite.Hom.IsFlat.pullback_exact` and written source-facing as exactness of `f^*`.

Source/core/bridge triage for part `(2)`:
- `source-facing`: exactness of pullback on module sheaves for a flat morphism of ringed topoi;
- `core/canonical`: `RingedSite.Hom.IsFlat.pullback_exact`;
- `bridge/view`: the notation `f^*` for the canonical module pullback functor.
-/

-- Proof sketch: exactness of the inverse-image functor on sheaves of sets is part of the
-- definition of a morphism of topoi, and the underlying sheaf of sets of the inverse image of an
-- abelian sheaf is computed by the same inverse-image functor; exactness on abelian sheaves
-- follows by transport across the forgetful comparison.
/-- Lemma 18.31.2 (1): for a site presentation of the underlying morphism of topoi
`f : \mathit{Sh}(\mathcal C) \to \mathit{Sh}(\mathcal C')`, the inverse-image functor on abelian
sheaves `f^{-1} : \mathrm{Ab}(\mathcal C') \to \mathrm{Ab}(\mathcal C)` is exact. -/
theorem ringedToposInverseImage_exact
    {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [Functor.IsContinuous F J K]
    [RepresentablyFlat F]
    [HasSheafify J (Type u)] [HasSheafify K (Type u)]
    [∀ P : Cᵒᵖ ⥤ Type u, F.op.HasLeftKanExtension P]
    [PreservesFiniteLimits (F.op.lan : (Cᵒᵖ ⥤ Type u) ⥤ Dᵒᵖ ⥤ Type u)] :
    exactFunctor
      (Sheaf J AddCommGrpCat.{u})
      (Sheaf K AddCommGrpCat.{u})
      (F.sheafPullback AddCommGrpCat.{u} J K) := by
  rw [exactFunctor_iff]
  constructor
  · let _ :
        PreservesFiniteLimits
          (F.op.lan :
            (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ Dᵒᵖ ⥤ AddCommGrpCat.{u}) :=
        inferInstance
    exact Functor.sheafPullbackConstruction.preservesFiniteLimits F AddCommGrpCat.{u} J K
  · let _ : (F.sheafPullback AddCommGrpCat.{u} J K).IsLeftAdjoint :=
        (F.sheafAdjunctionContinuous AddCommGrpCat.{u} J K).isLeftAdjoint
    infer_instance

/- Lemma 18.31.2 (2): for a flat morphism of ringed topoi, formalized by a flat morphism of
ringed sites `f`, the pullback functor on module sheaves `f^*` is exact. This is already the
canonical owner theorem `RingedSite.Hom.IsFlat.pullback_exact`. -/
recall IsFlat.pullback_exact

end RingedSite.Hom
