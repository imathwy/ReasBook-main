import Mathlib
import StacksProject_2024.stacks_project.Chap28.Definition_28_4_1
import StacksProject_2024.stacks_project.Chap29.Definition_29_47_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

-- Semantic recall: `lean_leansearch` surfaced mathlib's ring-locality API
-- `LocalizationPreserves` and `OfLocalizationMaximal`; the local Chapter 28 owner for the
-- source-faithful principal-open / finite-cover formulation is `RingPropertyIsLocal`, so this
-- item is recorded on that owner for the Chapter 29 predicates `SeminormalRing` and
-- `AbsolutelyWeaklyNormalRing`.

namespace SeminormalRing

/-- Lemma 29.47.2 (1): being seminormal is a local property of rings in the sense of
Definition 28.4.1. -/
@[stacks 0EUM, instance]
theorem ringPropertyIsLocal :
    RingPropertyIsLocal (fun A ↦ SeminormalRing A) := sorry

end SeminormalRing

namespace AbsolutelyWeaklyNormalRing

/-- Lemma 29.47.2 (2): being absolutely weakly normal is a local property of rings in the sense
of Definition 28.4.1. -/
@[stacks 0EUM, instance]
theorem ringPropertyIsLocal :
    RingPropertyIsLocal (fun A ↦ AbsolutelyWeaklyNormalRing A) := sorry

end AbsolutelyWeaklyNormalRing
