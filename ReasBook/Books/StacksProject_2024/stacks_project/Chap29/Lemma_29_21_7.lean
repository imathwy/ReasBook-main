import Mathlib
import StacksProject_2024.stacks_project.Chap17.Definition_17_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical closed-immersion owner
-- `AlgebraicGeometry.IsClosedImmersion`, while local Chapter 31 precedent verifies that the
-- associated ideal sheaf of a closed immersion is expressed by
-- `RingedSpace.closedImmersionIdealSheaf i.toShHom` and finite type by
-- `SheafOfModules.IsFiniteType`. The project also records finitely presented closed subschemes via
-- `LocallyOfFinitePresentation` on the closed immersion itself.

/-- Lemma 29.21.7: a closed immersion `i : Z ⟶ X` is of finite presentation if and only if its
associated ideal sheaf `\mathcal I = \ker(\mathcal O_X \to i_*\mathcal O_Z)` is of finite type as
an `\mathcal O_X`-module. -/
@[stacks 01TV]
theorem closedImmersion_locallyOfFinitePresentation_iff_idealSheaf_isFiniteType
    {X Z : Scheme.{u}} {i : Z ⟶ X} (hi : IsClosedImmersion i) :
    LocallyOfFinitePresentation i ↔
      SheafOfModules.IsFiniteType (RingedSpace.closedImmersionIdealSheaf i.toShHom) := sorry

end AlgebraicGeometry
