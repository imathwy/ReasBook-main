import Mathlib
import StacksProject_2024.Chap29.Definition_29_21_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry

-- Semantic recall / analogue check:
-- - mathlib already exposes the canonical owners `LocallyOfFinitePresentation`,
--   `LocallyOfFiniteType`, `QuasiCompact.of_comp`, and `QuasiSeparated.of_comp`;
-- - unlike the finite-type analogue `locallyOfFiniteType_of_comp`, mathlib does not currently
--   expose the finite-presentation recovery direction from a composite, so this file supplies the
--   owner-level theorem for local finite presentation and the corresponding scheme-side finite
--   presentation strengthening.

/-- Lemma 29.21.11 (1): if `f ≫ g` is locally of finite presentation and `g` is locally of finite
type, then `f` is locally of finite presentation. This is the canonical composable form of the
source over-base statement. -/
@[stacks 02FV]
theorem LocallyOfFinitePresentation.of_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFinitePresentation (f ≫ g)] [LocallyOfFiniteType g] :
    LocallyOfFinitePresentation f := sorry

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

/-- Lemma 29.21.11 (2): if `f ≫ g` is of finite presentation and `g` is locally of finite type,
then `f` is of finite presentation. Since `FinitePresentation` is the chapter owner combining local
finite presentation, quasi-compactness, and quasi-separatedness, this packages the source
over-base statement in the canonical composable form, with no extra ambient quasi-separatedness
assumption on `Y`. -/
@[stacks 02FV]
theorem FinitePresentation.of_comp
    {X Y Z : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [FinitePresentation (f ≫ g)] [AlgebraicGeometry.LocallyOfFiniteType g] :
    FinitePresentation f := sorry

end AlgebraicGeometry.Scheme.Hom
