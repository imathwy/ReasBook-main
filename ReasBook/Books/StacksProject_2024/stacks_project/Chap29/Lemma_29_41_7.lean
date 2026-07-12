import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u

namespace AlgebraicGeometry

section

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-morphism theorem
-- `AlgebraicGeometry.UniversallyClosed.of_comp_of_isSeparated`; the proper and closed-image
-- clauses are stated as source-facing companions using `IsProper`, `UniversallyClosed`, and
-- the set-theoretic image `Set.range f.base`. The Stacks tag evidence is consistent: item tag
-- `01W6` agrees with the source URL ending in `/tag/01W6`.

/-- Lemma 29.41.7 (1): in a commutative triangle `X ⟶ Y ⟶ S` with `Y` separated over `S`,
if `X` is universally closed over `S` via the composite, then `X ⟶ Y` is universally closed. -/
@[stacks 01W6]
theorem universallyClosed_of_comp_of_isSeparated
    [IsSeparated g] (hfg : UniversallyClosed (f ≫ g)) :
    UniversallyClosed f := sorry

/-- Lemma 29.41.7 (2): in a commutative triangle `X ⟶ Y ⟶ S` with `Y` separated over `S`,
if `X` is proper over `S` via the composite, then `X ⟶ Y` is proper. -/
@[stacks 01W6]
theorem isProper_of_comp_of_isSeparated
    [IsSeparated g] (hfg : IsProper (f ≫ g)) :
    IsProper f := sorry

/-- Lemma 29.41.7 (3): under the universally closed hypothesis in the first part, the
set-theoretic image of `X` in `Y` is closed. -/
@[stacks 01W6]
theorem isClosed_range_of_universallyClosed_comp_of_isSeparated
    [IsSeparated g] (hfg : UniversallyClosed (f ≫ g)) :
    IsClosed (Set.range f.base) := sorry

/-- Lemma 29.41.7 (4): under the properness hypothesis in the second part, the set-theoretic
image of `X` in `Y` is closed. -/
@[stacks 01W6]
theorem isClosed_range_of_isProper_comp_of_isSeparated
    [IsSeparated g] (hfg : IsProper (f ≫ g)) :
    IsClosed (Set.range f.base) := sorry

end

end AlgebraicGeometry
