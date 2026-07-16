import Mathlib
import StacksProject_2024.stacks_project.Chap29.Definition_29_21_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

-- Semantic recall / owner check:
-- - `lean_leansearch` surfaced the canonical diagonal owner `pullback.diagonal`, together with the
--   quasi-separated diagonal compactness theorem `QuasiSeparated.quasiCompact_diagonal` and the
--   separatedness-from-monomorphism theorem `IsSeparated.isSeparated_of_mono`;
-- - nearby Section 29.21 files record the source phrase “of finite presentation” for scheme
--   morphisms via `Scheme.Hom.FinitePresentation`, while the local finite-presentation clause
--   remains the canonical owner `LocallyOfFinitePresentation`.

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Lemma 29.21.12 (1): if `f : X ⟶ Y` is locally of finite type, then the diagonal morphism
`Δ : X ⟶ X ×[Y] X` is locally of finite presentation. -/
@[stacks 0818]
theorem locallyOfFinitePresentation_diagonal_of_locallyOfFiniteType [LocallyOfFiniteType f] :
    LocallyOfFinitePresentation (pullback.diagonal f) := sorry

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)

/-- Lemma 29.21.12 (2): if `f : X ⟶ Y` is quasi-separated and locally of finite type, then the
diagonal morphism `Δ : X ⟶ X ×[Y] X` is of finite presentation. -/
@[stacks 0818]
theorem finitePresentation_diagonal_of_quasiSeparated_of_locallyOfFiniteType
    [AlgebraicGeometry.QuasiSeparated f] [AlgebraicGeometry.LocallyOfFiniteType f] :
    FinitePresentation (pullback.diagonal f) := sorry

end AlgebraicGeometry.Scheme.Hom
