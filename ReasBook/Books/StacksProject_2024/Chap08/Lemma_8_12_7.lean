import Mathlib
import StacksProject_2024.Chap04.Lemma_4_35_2
import StacksProject_2024.Chap08.Lemma_8_12_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits

universe uC uD uS vC vD vS

namespace CategoryTheory

section

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]

/-
Domain-style sampling for Lemma 8.12.7:
- primary domain: localized pushforward of a fibred category along a functor, with the groupoid
  structure read from the fibers of the canonical projection to `D`.
- inspected owner-level declarations:
  `Functor.pushforwardProjection`,
  `Functor.pushforwardProjection_isFibered`,
  `isFibredInGroupoids_of_isFibered_and_fiber_groupoid`,
  `MorphismProperty.Localization.exists_rightFraction`.
- best owner abstraction: the canonical owner predicate
  `IsFibredInGroupoids (u.pushforwardProjection p)`.
- primitive data: the canonical projection `u.pushforwardProjection p` and the already-canonical
  fibred structure from Lemma `8.12.6`, which itself is built from pullbacks, equalizers, and
  preservation of those two limit shapes.
- derived API: the source-facing theorem below and the derived typeclass instance.

Source/core/bridge triage:
- `source-facing`: `pushforwardProjection_isFibredInGroupoids`.
- `core/canonical`: `IsFibredInGroupoids`, `Functor.IsFibered`, and the fiberwise groupoid
  criterion from Chapter 4.
- `bridge/view`: the private fiberwise groupoid helper, whose proof uses the right-fraction
  presentation of morphisms in the localization but introduces no parallel pushforward owner. -/

namespace Functor

variable (u : C ⥤ D) (p : S ⥤ C) [IsFibredInGroupoids p]
variable [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]

-- Proof sketch: Lemma `8.12.6` gives that the localized projection is fibred. To upgrade from
-- fibred to fibred in groupoids, use Lemma `4.35.2`: it is enough to show that every fiber of the
-- localized projection is a groupoid. A morphism in a fiber of the localization is represented by
-- a right fraction in `u_{pp} S`. Its denominator already belongs to the fraction property, and
-- the fiber condition forces the numerator to be vertical over `D`; because `p` is fibred in
-- groupoids, that vertical numerator is also strongly cartesian, hence belongs to the same
-- fraction property and becomes invertible after localization.
private theorem pushforwardProjectionFiber_hom_isIso
    (V : D) {X Y : (u.pushforwardProjection p).Fiber V} (φ : X ⟶ Y) :
    IsIso φ := by
  sorry

private instance pushforwardProjection_fiber_isGroupoid
    (V : D) :
    IsGroupoid ((u.pushforwardProjection p).Fiber V) where
  all_isIso := pushforwardProjectionFiber_hom_isIso u p V

/-- Lemma 8.12.7: with notation and assumptions as in Lemma `8.12.6`, if `p : S ⥤ C` is fibred in
groupoids, then the localized category `u ₚ p` is fibred in groupoids over `D` via its canonical
projection `u.pushforwardProjection p`. -/
theorem pushforwardProjection_isFibredInGroupoids
    : IsFibredInGroupoids (u.pushforwardProjection p) := by
  refine
    isFibredInGroupoids_of_isFibered_and_fiber_groupoid
      (u.pushforwardProjection p) (pushforwardProjection_isFibered u p) ?_
  intro V
  infer_instance

instance
    : IsFibredInGroupoids (u.pushforwardProjection p) :=
  pushforwardProjection_isFibredInGroupoids u p

end Functor

end

end CategoryTheory
