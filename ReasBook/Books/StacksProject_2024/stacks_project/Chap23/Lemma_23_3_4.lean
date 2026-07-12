import Mathlib.CategoryTheory.Limits.HasLimits
import StacksProject_2024.Chapters.Chap23.section03

open CategoryTheory
open CategoryTheory.Limits

universe u

/-
Source/core/bridge triage for Lemma 23.3.4:
- `source-facing`: the existence of all small colimits of divided power rings.
- `core/canonical`: the owner instance `HasColimits DividedPowerRing.{u}`.
- `bridge/view`: the per-shape instances `HasColimitsOfShape J DividedPowerRing.{u}` obtained
  from the global owner.
-/

namespace DividedPowerRing

-- Semantic recall: `lean_leansearch` pointed to `CommRingCat.Colimits.hasColimits_commRingCat`;
-- this item keeps the chapter's existing bundled owner `DividedPowerRing`.

/-- Lemma 23.3.4: the category of divided power rings has all colimits. -/
@[stacks 07GX]
instance hasColimits : HasColimits DividedPowerRing.{u} := by
  sorry

end DividedPowerRing
