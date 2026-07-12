import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Opposite

noncomputable section

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]
variable {T U V W : CosimplicialObject C}
variable (a : V ⟶ U) (b : W ⟶ U)
variable [HasPullback a b]

/- Domain-style sampling for Lemma 14.10.2:
- primary domain: pullbacks in `CosimplicialObject C`, tested against the representable functor
  `coyoneda.obj (op T)`;
- sampled owner declarations:
  `PullbackCone.IsLimit.equivPullbackObj`,
  `PullbackCone.IsLimit.equivPullbackObj_apply_fst`,
  `PullbackCone.IsLimit.equivPullbackObj_apply_snd`,
  `isLimitOfHasPullbackOfPreservesLimit`;
- best owner abstraction:
  - `source-facing`: the canonical identification
    `(T ⟶ pullback a b) ≃ { p : (T ⟶ V) × (T ⟶ W) // p.1 ≫ a = p.2 ≫ b }`;
  - `core/canonical`: `PullbackCone.IsLimit.equivPullbackObj`;
  - `bridge/view`: in the chapter, Definition 14.10.1 upgrades degreewise pullbacks to
    `[HasPullback a b]`, and then `coyoneda.obj (op T)` preserves that pullback.
- primitive data: only the morphisms `a`, `b`, the test object `T`, and the canonical owner-level
  assumption `[HasPullback a b]`;
- derived API: the hom-set pullback equivalence and its two projection formulas.

Source/core/bridge triage:
- `source-facing`: maps into the cosimplicial fibre product are pairs of maps with equal
  composites to `U`;
- `core/canonical`: `PullbackCone.IsLimit.equivPullbackObj`;
- `bridge/view`: the chapter-level passage from degreewise pullbacks to `[HasPullback a b]` in
  Definition 14.10.1, followed here by the representable-functor specialization via
  `isLimitOfHasPullbackOfPreservesLimit (coyoneda.obj (op T)) a b`.

This file adds no new owner-level data, so the refinement should stay at the canonical owner while
spelling out the cosimplicial specialization explicitly, rather than introducing a parallel local
equivalence. -/

recall PullbackCone.IsLimit.equivPullbackObj

/- Lemma 14.10.2: for cosimplicial objects, the canonical morphism into the pullback object is
equivalent to a compatible pair of morphisms into the two legs. This is the specialization of
`PullbackCone.IsLimit.equivPullbackObj` along `coyoneda.obj (op T)`. -/
#check
  (PullbackCone.IsLimit.equivPullbackObj
      (isLimitOfHasPullbackOfPreservesLimit (coyoneda.obj (op T)) a b) :
    (T ⟶ pullback a b) ≃ { p : (T ⟶ V) × (T ⟶ W) // p.1 ≫ a = p.2 ≫ b })

variable (f : T ⟶ pullback a b)

recall PullbackCone.IsLimit.equivPullbackObj_apply_fst

/- The first projection of the pullback-hom equivalence is composition with
`pullback.fst a b`. -/
#check
  (PullbackCone.IsLimit.equivPullbackObj_apply_fst
      (isLimitOfHasPullbackOfPreservesLimit (coyoneda.obj (op T)) a b) f :
    (PullbackCone.IsLimit.equivPullbackObj
        (isLimitOfHasPullbackOfPreservesLimit (coyoneda.obj (op T)) a b) f).1.1 =
      f ≫ pullback.fst a b)

recall PullbackCone.IsLimit.equivPullbackObj_apply_snd

/- The second projection of the pullback-hom equivalence is composition with
`pullback.snd a b`. -/
#check
  (PullbackCone.IsLimit.equivPullbackObj_apply_snd
      (isLimitOfHasPullbackOfPreservesLimit (coyoneda.obj (op T)) a b) f :
    (PullbackCone.IsLimit.equivPullbackObj
        (isLimitOfHasPullbackOfPreservesLimit (coyoneda.obj (op T)) a b) f).1.2 =
      f ≫ pullback.snd a b)

end CategoryTheory.Limits
