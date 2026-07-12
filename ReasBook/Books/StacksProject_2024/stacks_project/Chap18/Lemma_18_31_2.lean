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

namespace CategoryTheory.Functor

/- Domain-style sampling for Lemma 18.31.2:
- primary domain: exactness of inverse-image and pullback functors on sheaves and module sheaves;
- sampled canonical declarations:
  `exactFunctor`,
  `Functor.sheafPullback`,
  `Functor.sheafAdjunctionContinuous`,
  `Functor.sheafPullbackConstruction.preservesFiniteLimits`,
  `RingedSite.Hom.IsFlat.pullback_exact`;
- best owner abstraction for part `(1)`: `Functor.sheafPullback AddCommGrpCat J K`;
- best owner abstraction for part `(2)`: the source-facing flatness owner
  `RingedSite.Hom.IsFlat`, with exactness exposed by `RingedSite.Hom.IsFlat.pullback_exact`.

Primitive-vs-derived split:
- primitive data for part `(1)`: a continuous representably flat functor of sites `F`;
- primitive data for part `(2)`: a morphism of ringed sites `f : X ⟶ Y` together with the
  source-facing flatness hypothesis `IsFlat f` from Definition 18.31.1;
- derived API for part `(1)`: exactness of the canonical abelian-sheaf pullback owner
  `F.sheafPullback AddCommGrpCat J K`;
- derived API for part `(2)`: exactness of the canonical pullback functor on module sheaves,
  supplied directly by `RingedSite.Hom.IsFlat.pullback_exact`.

Source/core/bridge triage:
- `source-facing` for part `(1)`: exactness of inverse image on abelian sheaves for a site
  presentation of a morphism of topoi;
- `core/canonical` for part `(1)`: `F.sheafPullback AddCommGrpCat J K`;
- `bridge/view` for part `(1)`: the Stacks-language interpretation as inverse image on abelian
  sheaves;
- `source-facing` for part `(2)`: exactness of pullback on module sheaves for a flat morphism of
  ringed topoi;
- `core/canonical`: `RingedSite.Hom.IsFlat.pullback_exact`;
- `bridge/view`: the notation `f^*` for the canonical module pullback functor.
-/

-- Proof sketch: representable flatness gives finite-limit preservation for the canonical abelian
-- sheaf pullback owner, and adjointness gives finite-colimit preservation.
/-- Lemma 18.31.2 (1): for a site presentation of the underlying morphism of topoi
`f : \mathit{Sh}(\mathcal C) \to \mathit{Sh}(\mathcal C')`, the inverse-image functor on abelian
sheaves `f^{-1} : \mathrm{Ab}(\mathcal C') \to \mathrm{Ab}(\mathcal C)`, realized as
`F.sheafPullback AddCommGrpCat J K`, is exact. -/
theorem sheafPullback_addCommGrp_exact_of_isContinuous_representablyFlat
    {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [Functor.IsContinuous F J K]
    [RepresentablyFlat F] :
    exactFunctor
      (Sheaf J AddCommGrpCat.{u})
      (Sheaf K AddCommGrpCat.{u})
      (F.sheafPullback AddCommGrpCat.{u} J K) := by
  let _ :
      PreservesFiniteLimits
        (F.op.lan :
          (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ Dᵒᵖ ⥤ AddCommGrpCat.{u}) :=
    inferInstance
  let _ : PreservesFiniteLimits (F.sheafPullback AddCommGrpCat.{u} J K) :=
    Functor.sheafPullbackConstruction.preservesFiniteLimits F AddCommGrpCat.{u} J K
  let _ : (F.sheafPullback AddCommGrpCat.{u} J K).IsLeftAdjoint :=
    (F.sheafAdjunctionContinuous AddCommGrpCat.{u} J K).isLeftAdjoint
  exact (exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩

end CategoryTheory.Functor

namespace RingedSite.Hom

/- Lemma 18.31.2 (2): exactness of pullback on module sheaves is the imported theorem
`RingedSite.Hom.IsFlat.pullback_exact` for flat morphisms of ringed sites. -/
-- Route correction: the imported owner for this bridge is `IsFlat.pullback_exact`, not a
-- nonexistent local pullback-exactness wrapper.
recall IsFlat.pullback_exact

end RingedSite.Hom
