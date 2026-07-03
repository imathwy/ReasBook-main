import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_14_8_1 (from Chap14) -/
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory.SimplicialObject

section

variable {C : Type u} [Category.{v} C]
variable {U V W : SimplicialObject C}
variable (a : U ⟶ V) (b : U ⟶ W)
variable [∀ Δ : SimplexCategoryᵒᵖ, HasPushout (a.app Δ) (b.app Δ)]

/- Domain-style sampling for Definition 14.8.1:
- primary domain: pushouts in functor categories, specialized to simplicial objects;
- sampled owner declarations:
  `CategoryTheory.Limits.functorCategoryHasColimit`,
  `CategoryTheory.Limits.pushoutObjIso`,
  `CategoryTheory.Limits.PreservesPushout.iso`,
  `CategoryTheory.Limits.diagramIsoSpan`;
- best owner abstraction: pushouts of simplicial objects are pushouts in the functor category
  `SimplexCategoryᵒᵖ ⥤ C`, computed from pointwise colimits; when `C` already has pushouts, the
  dedicated owner comparison is `pushoutObjIso`, while under the weaker degreewise hypotheses in
  this file the canonical objectwise bridge is `PreservesPushout.iso` for evaluation;
- primitive data: only the span `U ⟶ V`, `U ⟶ W` and the degreewise pushout hypotheses;
- derived API: the simplicial pushout object `pushout a b` and its canonical coprojections.

Source/core/bridge triage:
- `source-facing`: the textbook statement that a degreewise pushout of simplicial objects exists;
- `core/canonical`: the functor-category colimit owner `functorCategoryHasColimit`;
- `bridge/view`: the conversion from degreewise `HasPushout (a.app Δ) (b.app Δ)` to the generic
  colimit hypothesis on the span diagram, yielding the canonical simplicial pushout instance.

This item is not a pure recall: mathlib already owns the pushout object and maps in the functor
category, but the passage from degreewise pushouts to a simplicial-object pushout is genuine public
bridge API. The bridge belongs in the `SimplicialObject` owner context, with the visible surface on
the canonical `pushout a b` and its evaluation-comparison API, not as a separate top-level wrapper.
-/

/-- The functor-category span `span a b` has pointwise colimits whenever each degreewise span
`span (a.app Δ) (b.app Δ)` does. -/
local instance pointwiseSpanHasColimit (Δ : SimplexCategoryᵒᵖ) :
    HasColimit ((span a b).flip.obj Δ) := by
  let e : ((span a b).flip.obj Δ) ≅ span (a.app Δ) (b.app Δ) := diagramIsoSpan _
  letI : HasColimit (span (a.app Δ) (b.app Δ)) := inferInstance
  exact hasColimit_of_iso e

/-- Degreewise pushouts assemble into a pushout of simplicial objects. -/
noncomputable instance : HasPushout a b := by
  change HasColimit (span a b)
  infer_instance

/- Definition 14.8.1: if each degreewise pushout `V_n ⨿_{U_n} W_n` exists, then the pushout of
simplicial objects `V` and `W` over `U` is the canonical pushout object `pushout a b` in
`SimplicialObject C`; equivalently, it is the pushout of the corresponding presheaves on `Δ`. -/
#check (pushout a b : SimplicialObject C)

/- Companion check: the canonical map from `V` into the simplicial pushout is `pushout.inl a b`. -/
#check (pushout.inl a b : V ⟶ pushout a b)

/- Companion check: the canonical map from `W` into the simplicial pushout is `pushout.inr a b`. -/
#check (pushout.inr a b : W ⟶ pushout a b)

variable (Δ : SimplexCategoryᵒᵖ)

local instance evaluationPreservesSpanColimit :
    PreservesColimit (span a b) ((evaluation _ _).obj Δ) := by
  infer_instance

local instance evaluationHasPushout :
    HasPushout (((evaluation _ _).obj Δ).map a) (((evaluation _ _).obj Δ).map b) := by
  simpa using (inferInstance : HasPushout (a.app Δ) (b.app Δ))

/- Evaluating the simplicial pushout at `Δ` is identified with the degreewise pushout by the
canonical pushout-comparison isomorphism for the evaluation functor,
`PreservesPushout.iso ((evaluation _ _).obj Δ) a b`. The source-facing form is its inverse,
viewed as `(pushout a b).obj Δ ≅ pushout (a.app Δ) (b.app Δ)`. -/
#check ((PreservesPushout.iso ((evaluation _ _).obj Δ) a b).symm :
  (pushout a b).obj Δ ≅ pushout (a.app Δ) (b.app Δ))

/- Its coprojection identities in that source-facing orientation are the canonical lemmas
`PreservesPushout.inl_iso_inv` and `PreservesPushout.inr_iso_inv`. -/
#check (PreservesPushout.inl_iso_inv ((evaluation _ _).obj Δ) a b :
  (pushout.inl a b).app Δ ≫
      (PreservesPushout.iso ((evaluation _ _).obj Δ) a b).inv =
    pushout.inl (a.app Δ) (b.app Δ))

#check (PreservesPushout.inr_iso_inv ((evaluation _ _).obj Δ) a b :
  (pushout.inr a b).app Δ ≫
      (PreservesPushout.iso ((evaluation _ _).obj Δ) a b).inv =
    pushout.inr (a.app Δ) (b.app Δ))

end

end CategoryTheory.SimplicialObject

/-! ### Lemma_14_8_2 (from Chap14) -/
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
