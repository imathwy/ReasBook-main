import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Opposite

noncomputable section

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]
variable {T U V W : SimplicialObject C}
variable (a : V ⟶ U) (b : W ⟶ U)
variable [HasPullback a b]

local notation "homPullbackIsLimit" =>
  isLimitOfHasPullbackOfPreservesLimit (coyoneda.obj (op T)) a b

local notation "homPullbackEquiv" => PullbackCone.IsLimit.equivPullbackObj homPullbackIsLimit

/- Domain-style sampling for Lemma 14.7.2:
- primary domain: pullbacks in `SimplicialObject C`, viewed through the represented functor
  `coyoneda.obj (Opposite.op T)`;
- sampled owner declarations:
  `PullbackCone.IsLimit.equivPullbackObj`,
  `PullbackCone.IsLimit.equivPullbackObj_apply_fst`,
  `PullbackCone.IsLimit.equivPullbackObj_apply_snd`,
  `isLimitOfHasPullbackOfPreservesLimit`;
- best owner abstraction:
  - `source-facing`: the textbook identification
    `(T ⟶ pullback a b) ≃ { p : (T ⟶ V) × (T ⟶ W) // p.1 ≫ a = p.2 ≫ b }`;
  - `core/canonical`: `PullbackCone.IsLimit.equivPullbackObj`;
  - `bridge/view`: the simplicial-object specialization obtained by combining
    `[HasPullback a b]` from Definition 14.7.1 with
    `isLimitOfHasPullbackOfPreservesLimit (coyoneda.obj (op T)) a b`.
- primitive data: only the morphisms `a`, `b`, the test simplicial object `T`, and the
  owner-level assumption `[HasPullback a b]`;
- derived API: the pullback-hom equivalence and its two projection formulas.

Source/core/bridge triage:
- `source-facing`: maps from `T` into the simplicial fibre product are pairs of maps into `V` and
  `W` with equal composites into `U`;
- `core/canonical`: `PullbackCone.IsLimit.equivPullbackObj`;
- `bridge/view`: the chapter-level simplicial specialization obtained by applying
  `coyoneda.obj (op T)` to the canonical pullback of simplicial objects.

This file should therefore keep the canonical owner recall, but the main checked outcome belongs at
the `bridge/view` layer: the explicit simplicial-object specialization of the generic pullback-hom
equivalence and its projection formulas.
-/

recall PullbackCone.IsLimit.equivPullbackObj

/- Lemma 14.7.2: for simplicial objects, the canonical morphism into the pullback object is
equivalent to a compatible pair of morphisms into the two legs. This is the specialization of
`PullbackCone.IsLimit.equivPullbackObj` along `coyoneda.obj (op T)`. -/
#check
  (show (T ⟶ pullback a b) ≃
      { p : (T ⟶ V) × (T ⟶ W) // p.1 ≫ a = p.2 ≫ b } from
    homPullbackEquiv)

variable (f : T ⟶ pullback a b)

recall PullbackCone.IsLimit.equivPullbackObj_apply_fst

/- The first projection of the pullback-hom equivalence is composition with
`pullback.fst a b`. -/
#check
  (show
      (homPullbackEquiv f).1.1 =
        f ≫ pullback.fst a b from
    PullbackCone.IsLimit.equivPullbackObj_apply_fst homPullbackIsLimit f)

recall PullbackCone.IsLimit.equivPullbackObj_apply_snd

/- The second projection of the pullback-hom equivalence is composition with
`pullback.snd a b`. -/
#check
  (show
      (homPullbackEquiv f).1.2 =
        f ≫ pullback.snd a b from
    PullbackCone.IsLimit.equivPullbackObj_apply_snd homPullbackIsLimit f)

end CategoryTheory.Limits
