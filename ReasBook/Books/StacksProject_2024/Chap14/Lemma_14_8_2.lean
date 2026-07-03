import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Lemma 14.8.2:
- primary domain: pushouts in `SimplicialObject C`, viewed through representable functors on the
  opposite category.
- inspected owner declarations:
  `pushout.isColimit`,
  `PushoutCocone.isColimitYonedaEquiv`,
  `PullbackCone.IsLimit.equivPullbackObj`,
  `Types.PullbackObj`.
- best owner abstraction: the canonical pushout cocone `pushout.cocone a b`; the source-facing
  hom-set pullback equivalence is derived by applying `yoneda.obj T` to the opposite cocone and
  then using the resulting `Type`-valued pullback cone.
- primitive-vs-derived split:
  primitive data: the cocone `pushout.cocone a b` with its colimit witness `pushout.isColimit a b`.
  derived API: the canonical equivalence
    `PullbackCone.IsLimit.equivPullbackObj`
    on the mapped cone
    `((pushout.cocone a b).isColimitYonedaEquiv.toFun
      (pushout.isColimit a b) T)`. -/

/- Source/core/bridge triage for Lemma 14.8.2:
- source-facing: the textbook pullback description of maps `V ⨿[U] W ⟶ T`.
- core/canonical: `pushout.cocone a b` together with
  `PushoutCocone.isColimitYonedaEquiv` and `PullbackCone.IsLimit.equivPullbackObj`.
- bridge/view: the specialization to the explicit pair of precomposition maps
  `fun f : V ⟶ T ↦ a ≫ f` and `fun g : W ⟶ T ↦ b ≫ g`. -/

section PushoutsOfSimplicialObjects

variable {U V W T : SimplicialObject C}
variable {a : U ⟶ V} {b : U ⟶ W}
variable [HasPushout a b]

/- Lemma 14.8.2 starts from the canonical pushout cocone `pushout.cocone a b` of simplicial
objects. -/
recall pushout.cocone

/- Lemma 14.8.2: the chosen pushout cocone of simplicial objects is colimiting; this is the
canonical witness `pushout.isColimit a b`. -/
recall pushout.isColimit

/- Lemma 14.8.2 is the simplicial-object specialization of the canonical yoneda test for a
pushout cocone. -/
recall PushoutCocone.isColimitYonedaEquiv

/- The mapped pullback cone in `Type` yields the canonical hom-set pullback equivalence via
`PullbackCone.IsLimit.equivPullbackObj`. -/
recall PullbackCone.IsLimit.equivPullbackObj

/- Lemma 14.8.2: maps from the simplicial pushout into `T` form the canonical pullback of the two
precomposition maps to `Hom(U, T)`. This is the direct source-facing specialization of the
owner-level pushout-yoneda equivalence; no chapter-local wrapper is needed. -/
#check
  (show (pushout a b ⟶ T) ≃
      Types.PullbackObj
        (fun f : V ⟶ T ↦ a ≫ f)
        (fun g : W ⟶ T ↦ b ≫ g) from
    PullbackCone.IsLimit.equivPullbackObj
      ((pushout.cocone a b).isColimitYonedaEquiv.toFun
        (pushout.isColimit a b) T))

end PushoutsOfSimplicialObjects

end CategoryTheory
