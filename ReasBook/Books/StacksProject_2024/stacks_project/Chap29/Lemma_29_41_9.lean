import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u

-- Semantic recall / analogue check:
-- - `lean_leansearch` surfaced the exact canonical descent theorem
--   `AlgebraicGeometry.UniversallyClosed.of_comp_surjective`.
-- - It also confirmed that the properness corollary should target the canonical owner
--   `AlgebraicGeometry.IsProper` via `AlgebraicGeometry.IsProper.mk`.
-- - Local Chapter 29 precedent for the naming pattern is
--   `quasiSeparated_of_comp_of_surjective_of_universallyClosed` and
--   `isSeparated_of_comp_of_surjective_of_universallyClosed` in `Lemma_29_41_11`.

namespace AlgebraicGeometry

/-- Lemma 29.41.9 (1): if `f : X ⟶ Y` is surjective and `X` is universally closed over `S` via
`f ≫ g`, then `Y` is universally closed over `S` via `g`. -/
@[stacks 03GN]
theorem universallyClosed_of_comp_of_surjective
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [Surjective f] (hfg : UniversallyClosed (f ≫ g)) :
    UniversallyClosed g := sorry

/-- Lemma 29.41.9 (2): if `f : X ⟶ Y` is surjective, `X` is universally closed over `S` via
`f ≫ g`, and `Y` is separated and locally of finite type over `S` via `g`, then `Y` is proper
over `S` via `g`. -/
@[stacks 03GN]
theorem isProper_of_comp_of_surjective_of_universallyClosed
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [Surjective f] (hfg : UniversallyClosed (f ≫ g)) [IsSeparated g] [LocallyOfFiniteType g] :
    IsProper g := sorry

end AlgebraicGeometry
