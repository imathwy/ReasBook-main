import Mathlib.Algebra.Category.Ring.Limits
import StacksProject_2024.Chapters.Chap23.section03

open CategoryTheory CategoryTheory.Limits

universe v u w

/- Source/core/bridge triage for Lemma 23.3.2:
- `source-facing`: the existence theorem `forgetToCommRingCat_lifts_limit`, its direct limit-cone
  companion `forgetToCommRingCat_lifts_limitCone`, and the bundled existence theorem
  `existsLimitCone`.
- `core/canonical`: mathlib's `LiftsToLimit` for the forgetful functor
  `forget₂ DividedPowerRing CommRingCat`.
- `bridge/view`: the derived `LimitCone` witness extracted from a chosen lifting datum.

Because the lifting theorem is still in proof stage, this file keeps the source-facing lifting and
existence statements rather than packaging the chosen lifted cone into public limit-instance data.
-/

namespace DividedPowerRing

section

variable {J : Type v} [Category.{w} J] (K : J ⥤ DividedPowerRing.{u})

/-- Lemma 23.3.2 (2): a limiting cone of the underlying commutative-ring diagram lifts to a
limiting cone of divided power rings. This is the source-facing form of the claim that
`forget₂ DividedPowerRing CommRingCat` creates limits. -/
@[stacks 07GV]
theorem forgetToCommRingCat_lifts_limit
    (c : Cone (K ⋙ forget₂ DividedPowerRing CommRingCat)) (hc : IsLimit c) :
    Nonempty (LiftsToLimit K (forget₂ DividedPowerRing CommRingCat) c hc) := by
  sorry

/-- Companion form of Lemma 23.3.2 (2): the lifted cone can be repackaged as a `LimitCone`, and
its image under the forgetful functor is isomorphic to the original limiting cone. -/
theorem forgetToCommRingCat_lifts_limitCone
    (c : Cone (K ⋙ forget₂ DividedPowerRing CommRingCat)) (hc : IsLimit c) :
    ∃ c' : LimitCone K, Nonempty ((forget₂ DividedPowerRing CommRingCat).mapCone c'.cone ≅ c) := by
  obtain ⟨h⟩ := forgetToCommRingCat_lifts_limit K c hc
  exact ⟨⟨h.toLiftableCone.liftedCone, h.makesLimit⟩, ⟨h.toLiftableCone.validLift⟩⟩

/-- Lemma 23.3.2 (1): every small diagram of divided power rings admits a limiting cone. -/
@[stacks 07GV]
theorem existsLimitCone [Small.{u} J] :
    Nonempty (LimitCone K) := by
  obtain ⟨h⟩ := forgetToCommRingCat_lifts_limit K
    (limit.cone (K ⋙ forget₂ DividedPowerRing CommRingCat))
    (limit.isLimit (K ⋙ forget₂ DividedPowerRing CommRingCat))
  exact ⟨⟨h.toLiftableCone.liftedCone, h.makesLimit⟩⟩

end

end DividedPowerRing
