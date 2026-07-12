import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u

namespace AlgebraicGeometry

section

variable {X Y S : Scheme.{u}} (h : X ⟶ Y) (f : X ⟶ S) (g : Y ⟶ S)

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-theoretic-image owner
-- `Scheme.Hom.image`, the factorization map `Scheme.Hom.toImage`, the closed immersion
-- `Scheme.Hom.imageι`, and the canonical morphism-property owners `UniversallyClosed`,
-- `IsSeparated`, `LocallyOfFiniteType`, `IsProper`, and `Surjective`. The Stacks tag evidence is
-- consistent: item tag `0AH6` agrees with the source URL ending in `/tag/0AH6`.

/-- Lemma 29.41.10 (1): in a commutative triangle `X ⟶ Y ⟶ S`, if `X` is universally
closed over `S` and `Y` is separated and locally of finite type over `S`, then the
scheme-theoretic image of `h : X ⟶ Y` is proper over `S`. -/
@[stacks 0AH6]
theorem schemeTheoreticImage_isProper_of_universallyClosed
    (hcomm : h ≫ g = f) [UniversallyClosed f] [IsSeparated g] [LocallyOfFiniteType g] :
    IsProper (Scheme.Hom.imageι h ≫ g) := sorry

/-- Lemma 29.41.10 (2): under the same hypotheses, the canonical morphism from `X` to the
scheme-theoretic image of `h : X ⟶ Y` is surjective. -/
@[stacks 0AH6]
theorem schemeTheoreticImage_toImage_surjective_of_universallyClosed
    (hcomm : h ≫ g = f) [UniversallyClosed f] [IsSeparated g] [LocallyOfFiniteType g] :
    Surjective (Scheme.Hom.toImage h) := sorry

end

end AlgebraicGeometry
