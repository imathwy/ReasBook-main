import Mathlib
import StacksProject_2024.Chap29.Definition_29_50_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall / local analogue check:
-- - `lean_leansearch` recalled the canonical dominant-morphism owner `AlgebraicGeometry.IsDominant`.
-- - The chapter-local birational owner is `AlgebraicGeometry.IsBirational` from
--   `Definition_29_50_1`, already stated for schemes with finitely many irreducible components.
-- - The source implication matches the canonical theorem shape `IsBirational f → IsDominant f`.

/-- Lemma 29.50.2: let `f : X ⟶ Y` be a morphism of schemes having finitely many irreducible
components. If `f` is birational then `f` is dominant. -/
theorem isDominant_of_isBirational
    {X Y : Scheme.{u}} [Finite (irreducibleComponents X)] [Finite (irreducibleComponents Y)]
    (f : X ⟶ Y) [IsBirational f] :
    IsDominant f := sorry

end AlgebraicGeometry
