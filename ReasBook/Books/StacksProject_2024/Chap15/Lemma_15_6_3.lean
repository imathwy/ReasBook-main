import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap15.Situation_15_6_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {B A A' : Type u}
variable [CommRing B] [CommRing A] [CommRing A']

/- Domain-style sampling for 15.6.3:
- primary domain: integrality of commutative-ring maps and its stability under base change;
- sampled owner declarations:
  `RingHom.IsIntegral`,
  `RingHom.isIntegral_isStableUnderBaseChange`,
  `SurjectiveRingPullbackSituation`,
  `SurjectiveRingPullbackSituation.bprimeToAprime`;
- best owner abstraction: the mathematical property is owned by `RingHom.IsIntegral`, and the
  base-change theorem is the canonical owner declaration
  `RingHom.isIntegral_isStableUnderBaseChange`; the chapter pullback situation is only a
  source-facing bridge packaging the specific fibre-product square from Situation `15.6.1`;
- primitive data at the core layer: a ring map and the proposition that it is integral;
- derived bridge API in this file: for `S : SurjectiveRingPullbackSituation B A A'`, the map
  `S.bprimeToAprime` is derived from the pullback owner data and inherits integrality from the core
  base-change theorem.

Source/core/bridge triage:
- `source-facing`: the chapter specialization to Situation `15.6.1`;
- `core/canonical`: `RingHom.IsIntegral` and `RingHom.isIntegral_isStableUnderBaseChange`;
- `bridge/view`: `SurjectiveRingPullbackSituation` and the specialized theorem below. -/

/- Lemma 15.6.3 is a chapter-level pullback instance of the canonical base-change theorem
`RingHom.isIntegral_isStableUnderBaseChange`. -/
recall RingHom.isIntegral_isStableUnderBaseChange

/-- Lemma 15.6.3: specialized bridge from Situation `15.6.1` to the canonical base-change owner.
If `B → A` is integral in a surjective ring pullback situation, then the induced projection
`B' = B ×_A A' → A'` is integral. -/
-- Proof sketch: specialize the canonical base-change owner theorem to the pullback ring from
-- Situation `15.6.1`.
theorem isIntegral_pullback_projection_of_surjective_of_isIntegral
    (S : SurjectiveRingPullbackSituation B A A') (hBA : S.toA.IsIntegral) :
    S.bprimeToAprime.IsIntegral := by
  sorry

end
