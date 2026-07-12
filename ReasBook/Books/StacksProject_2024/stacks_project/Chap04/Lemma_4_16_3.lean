import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits

variable {J : Type u₁} [Category.{v₁} J]
variable {C : Type u₂} [Category.{v₂} C]
variable {X : C}

/- Companion recall: for a connected indexing category `J`, the forgetful functor
`Over.forget (op X)` preserves `Jᵒᵖ`-shaped limits. -/
recall Over.preservesLimitsOfShape_forget_of_isConnected

/-- Lemma 4.16.3: for a connected diagram `M : J ⥤ Under X`, the forgetful functor
`Under.forget X` preserves the colimit of `M`. Equivalently, whenever `M` has a colimit in
`Under X`, the underlying diagram in `C` has the same colimit. -/
-- Proof sketch: dualize the connected-limit statement for `Over.forget (op X)` using
-- `Over.opEquivOpUnder X` and the opposites API, then specialize the resulting
-- `PreservesColimitsOfShape` instance to the diagram `M`.
theorem under_forget_preserves_colimit_of_isConnected (M : J ⥤ Under X) [IsConnected J] :
    PreservesColimit M (Under.forget X) := sorry

end CategoryTheory
