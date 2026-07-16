import Mathlib
import StacksProject_2024.stacks_project.Chap29.Lemma_29_21_7
import StacksProject_2024.stacks_project.Chap29.Lemma_29_35_9

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Semantic recall / analogue check:
- `lean_leansearch` recalled the canonical scheme-side owners `IsClosedImmersion` and
  `FormallyUnramified`;
- local Chapter 29 precedent provides the source-facing owners `Unramified` and `GUnramified` and
  the finite-presentation criterion
  `closedImmersion_locallyOfFinitePresentation_iff_idealSheaf_isFiniteType`.
-/

variable {X Z : Scheme.{u}} {i : Z ⟶ X}

/-- Lemma 29.35.8 (1): a closed immersion is unramified. -/
@[stacks 02GC]
theorem unramified_of_isClosedImmersion (hi : IsClosedImmersion i) :
    Unramified i := sorry

/-- Lemma 29.35.8 (2): a closed immersion `i : Z ⟶ X` is G-unramified if and only if its
associated quasi-coherent sheaf of ideals
`\mathcal I = \ker(\mathcal O_X \to i_*\mathcal O_Z)` is of finite type as an
`\mathcal O_X`-module. -/
@[stacks 02GC]
theorem gUnramified_iff_isClosedImmersion_and_idealSheaf_isFiniteType
    (hi : IsClosedImmersion i) :
    GUnramified i ↔
      SheafOfModules.IsFiniteType (RingedSpace.closedImmersionIdealSheaf i.toShHom) := sorry

end AlgebraicGeometry
