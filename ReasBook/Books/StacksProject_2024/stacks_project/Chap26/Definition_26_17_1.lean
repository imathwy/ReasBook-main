import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall note: `lean_leansearch` only returned scheme-pullback infrastructure, while the
-- local owner precedent in `Chap04/Definition_4_6_3.lean` fixes this item at the canonical
-- categorical pullback object API: `pullback f g` with projections `pullback.fst`, `pullback.snd`,
-- and universal property `pullbackIsPullback`.
/- Source/core/bridge triage:
- `source-facing`: the fibre product of schemes over a base.
- `core/canonical`: the chosen pullback object `pullback f g` in `Scheme`.
- `bridge/view`: the projection maps, the commutativity relation, and the explicit universal
  property API `PullbackCone.IsLimit.equivPullbackObj` specialized to schemes. -/
/-
Definition 26.17.1: given morphisms of schemes `f : X ⟶ S` and `g : Y ⟶ S`, their fibre product
is the canonical pullback scheme `pullback f g`, with projection morphisms `pullback.fst f g` and
`pullback.snd f g`, universal among commutative squares over `f` and `g`.
-/
recall pullback
recall pullback.fst
recall pullback.snd
recall pullback.condition
recall pullback.lift
recall pullback.lift_fst
recall pullback.lift_snd
recall pullback.hom_ext
recall pullbackIsPullback
recall isLimitOfHasPullbackOfPreservesLimit
recall PullbackCone.IsLimit.equivPullbackObj
recall PullbackCone.IsLimit.equivPullbackObj_apply_fst
recall PullbackCone.IsLimit.equivPullbackObj_apply_snd

variable {S X Y T : Scheme.{u}}

variable (T : Scheme.{u}) (f : X ⟶ S) (g : Y ⟶ S)

/- Definition 26.17.1: the universal property of the fibre product of schemes over `S` is the
canonical pullback-hom equivalence specialized to `Scheme`. -/
#check
  (show (T ⟶ pullback f g) ≃
      { p : (T ⟶ X) × (T ⟶ Y) // p.1 ≫ f = p.2 ≫ g } from
    PullbackCone.IsLimit.equivPullbackObj
      (isLimitOfHasPullbackOfPreservesLimit (coyoneda.obj (op T)) f g))

variable (l : T ⟶ pullback f g)

/- The first projection of the pullback-hom equivalence is composition with
`pullback.fst f g`. -/
#check
  (show
      (PullbackCone.IsLimit.equivPullbackObj
          (isLimitOfHasPullbackOfPreservesLimit (coyoneda.obj (op T)) f g) l).1.1 =
        l ≫ pullback.fst f g from
    PullbackCone.IsLimit.equivPullbackObj_apply_fst
      (isLimitOfHasPullbackOfPreservesLimit (coyoneda.obj (op T)) f g) l)

/- The second projection of the pullback-hom equivalence is composition with
`pullback.snd f g`. -/
#check
  (show
      (PullbackCone.IsLimit.equivPullbackObj
          (isLimitOfHasPullbackOfPreservesLimit (coyoneda.obj (op T)) f g) l).1.2 =
        l ≫ pullback.snd f g from
    PullbackCone.IsLimit.equivPullbackObj_apply_snd
      (isLimitOfHasPullbackOfPreservesLimit (coyoneda.obj (op T)) f g) l)

end AlgebraicGeometry
