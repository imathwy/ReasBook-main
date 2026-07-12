import Mathlib
import StacksProject_2024.Chap07.Definition_7_17_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

universe u v

namespace CategoryTheory
namespace Sheaf

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C} [HasWeakSheafify J (Type (max u v))]

/- Source/core/bridge triage for 7.17.6:
- source-facing notion: `Sheaf.IsQuasiCompactObject`
- core/canonical owner:
  `ObjectProperty.IsClosedUnderFiniteCoproducts
    (IsQuasiCompactObject : ObjectProperty (Sheaf J (Type (max u v))))`
- bridge/view: any finite-family coproduct statement is obtained directly from
  `ObjectProperty.prop_coproduct`, so no parallel wrapper theorem is kept here
-/

/-- Lemma 7.17.6: quasi-compact sheaf objects are closed under finite coproducts. -/
instance isQuasiCompactObject_isClosedUnderFiniteCoproducts
    : ObjectProperty.IsClosedUnderFiniteCoproducts
        (IsQuasiCompactObject : ObjectProperty (Sheaf J (Type (max u v)))) := by
  sorry

end Sheaf

end CategoryTheory
