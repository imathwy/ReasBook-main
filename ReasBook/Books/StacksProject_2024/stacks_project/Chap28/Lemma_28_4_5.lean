import StacksProject_2024.Chap10.Definition_10_104_6
import StacksProject_2024.Chap28.Definition_28_4_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

-- Semantic recall note: the chapter's canonical owner for “a ring property is local” is
-- `RingPropertyIsLocal` from Definition 28.4.1. The current project already packages the two
-- ring-side properties as `CohenMacaulayRing` and `IsRegularRing`, so Lemma 28.4.5 should expose
-- locality instances for those canonical owners and for `Algebra.FiniteType ℤ`. In the finite-type
-- case, the supporting canonical locality API is mathlib's `RingHom.finiteType_isLocal`,
-- specialized to the algebra map `ℤ → A` and repackaged in the Chapter 28 owner
-- `RingPropertyIsLocal`.
--
-- Source/core/bridge triage:
-- * source-facing: the three `RingPropertyIsLocal` instances asserting the textbook locality
--   criteria in Lemma `28.4.5`;
-- * core/canonical: `CohenMacaulayRing`, `IsRegularRing`, and `Algebra.FiniteType ℤ`;
-- * bridge/view: none needed here, since the source item only records locality of these existing
--   ring properties.

namespace CohenMacaulayRing

/-- Lemma 28.4.5 (1): the property that a ring is Noetherian and Cohen-Macaulay is local in the
sense of Definition 28.4.1. -/
@[stacks 01OT, instance]
theorem ringPropertyIsLocal :
    RingPropertyIsLocal (fun A ↦ CohenMacaulayRing A) := by
  sorry

end CohenMacaulayRing

namespace IsRegularRing

/-- Lemma 28.4.5 (2): the property that a ring is Noetherian and regular is local in the sense of
Definition 28.4.1. -/
@[stacks 01OT, instance]
theorem ringPropertyIsLocal :
    RingPropertyIsLocal (fun A ↦ IsRegularRing A) := by
  sorry

end IsRegularRing

namespace Algebra.FiniteType

/-- Lemma 28.4.5 (3): the property that a ring is of finite type over `\mathbf{Z}` is local in
the sense of Definition 28.4.1. -/
@[stacks 01OT, instance]
theorem int_ringPropertyIsLocal :
    RingPropertyIsLocal (fun A ↦ Algebra.FiniteType ℤ A) := by
  sorry

end Algebra.FiniteType
