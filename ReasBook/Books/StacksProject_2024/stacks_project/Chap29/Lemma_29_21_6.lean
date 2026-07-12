import Mathlib
import StacksProject_2024.Chap29.Definition_29_21_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

-- Semantic recall: `lean_leansearch` surfaced the canonical mathlib instances
-- `AlgebraicGeometry.locallyOfFinitePresentation_of_isOpenImmersion` and
-- `AlgebraicGeometry.IsSeparated.instQuasiSeparated`. Nearby Section 29.21 files use the local
-- owner `Scheme.Hom.FinitePresentation` for the source phrase “of finite presentation”, so this
-- item records the open-immersion specialization of that owner.

/-- Lemma 29.21.6: any open immersion is of finite presentation if and only if it is
quasi-compact. -/
@[stacks 01TU]
theorem finitePresentation_iff_quasiCompact_of_isOpenImmersion
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.IsOpenImmersion f] :
    FinitePresentation f ↔ AlgebraicGeometry.QuasiCompact f := sorry

end AlgebraicGeometry.Scheme.Hom
