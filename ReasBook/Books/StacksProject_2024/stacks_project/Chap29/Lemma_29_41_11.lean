import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical absolute owners
-- `Scheme.IsSeparated` and `quasiSeparatedSpace_iff_quasiSeparated`, together with the morphism
-- owner facts `IsSeparated.comp_iff` and `QuasiSeparated.of_comp`. Nearby Chapter 29 files use the
-- absolute scheme-side owners `QuasiSeparatedSpace X`, `X.IsSeparated` and the relative owners
-- `QuasiSeparated f`, `IsSeparated f`, so the source item is split into these four atomic descent
-- statements.

/-- Lemma 29.41.11 (1): if `f : X ⟶ Y` is surjective and universally closed and `X` is
quasi-separated, then `Y` is quasi-separated. -/
theorem quasiSeparatedSpace_of_surjective_of_universallyClosed
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Surjective f] [UniversallyClosed f] [QuasiSeparatedSpace X] :
    QuasiSeparatedSpace Y := sorry

/-- Lemma 29.41.11 (2): if `f : X ⟶ Y` is surjective and universally closed and `X` is separated,
then `Y` is separated. -/
theorem isSeparated_of_surjective_of_universallyClosed
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Surjective f] [UniversallyClosed f] [X.IsSeparated] :
    Y.IsSeparated := sorry

/-- Lemma 29.41.11 (3): if `f : X ⟶ Y` is surjective and universally closed, and `X` is
quasi-separated over `S` via `f ≫ g`, then `Y` is quasi-separated over `S` via `g`. -/
theorem quasiSeparated_of_comp_of_surjective_of_universallyClosed
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [Surjective f] [UniversallyClosed f] [QuasiSeparated (f ≫ g)] :
    QuasiSeparated g := sorry

/-- Lemma 29.41.11 (4): if `f : X ⟶ Y` is surjective and universally closed, and `X` is separated
over `S` via `f ≫ g`, then `Y` is separated over `S` via `g`. -/
theorem isSeparated_of_comp_of_surjective_of_universallyClosed
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [Surjective f] [UniversallyClosed f] [IsSeparated (f ≫ g)] :
    IsSeparated g := sorry

end AlgebraicGeometry
