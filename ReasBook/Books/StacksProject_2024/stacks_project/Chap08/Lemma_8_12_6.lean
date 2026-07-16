import Mathlib
import StacksProject_2024.stacks_project.Chap08.Lemma_8_12_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits

universe uC uD uS vC vD vS

namespace CategoryTheory

section

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]

/- Domain-style sampling for Lemma 8.12.6:
- primary domain: pushforward of a fibred category along a functor, modeled by localization of the
  prelocalized pullback category from Lemma `8.12.5`.
- inspected owner-level declarations:
  `Functor.pushforwardProjection`,
  `Functor.pushforwardFractions_hasRightCalculusOfFractions`,
  `Functor.IsFibered`,
  `Functor.IsFibered.of_exists_isStronglyCartesian`.
- best owner abstraction: the owner predicate `Functor.IsFibered` on the canonical projection
  `u.pushforwardProjection p`.
- primitive data: the localized projection `u.pushforwardProjection p`, already constructed
  upstream from the localization data in Lemma `8.12.5`, together with the pullback/equalizer
  hypothesis layer used there.
- derived API: the source-facing theorem that this projection is fibred, and the derived instance.

Source/core/bridge triage:
- `source-facing`: Lemma `8.12.6`, asserting that the localized pushforward category is fibred
  over `D`.
- `core/canonical`: `Functor.IsFibered`.
- `bridge/view`: `Functor.pushforwardProjection u p`, the canonical projection from the localized
  pushforward category to `D`. -/

namespace Functor

variable (u : C ⥤ D) (p : S ⥤ C) [p.IsFibered]
variable [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]

-- Proof sketch: use the right-fraction description of morphisms in `u_p 𝒮` from Lemma `8.12.5`
-- and the canonical extension of the projection to `D`. Strongly cartesian morphisms in the
-- localization are detected by representatives in `u_{pp} 𝒮`, and the explicit strongly
-- cartesian lifts constructed there descend to cartesian lifts in the localized category.
/-- Lemma 8.12.6: with notation and assumptions as in Lemma `8.12.5`, the localized category
`u ₚ p` is a fibred category over `D` via its canonical projection
`u.pushforwardProjection p`. -/
theorem pushforwardProjection_isFibered :
    (u.pushforwardProjection p).IsFibered := sorry

instance :
    (u.pushforwardProjection p).IsFibered :=
  pushforwardProjection_isFibered u p

end Functor

end

end CategoryTheory
