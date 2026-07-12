import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section

variable {X Y Z' : Scheme.{u}} (f : X ⟶ Y)

-- Semantic recall: `lean_leansearch` returned the canonical scheme-theoretic-image owner
-- `Scheme.Hom.image`, with maps `Scheme.Hom.toImage` and `Scheme.Hom.imageι`. The Stacks tag
-- evidence is consistent: item tag `01R6` matches the source URL `/tag/01R6`.

/-- Lemma 29.6.1 (1): the canonical scheme-theoretic image of `f : X \to Y` is a closed
subscheme of `Y`. -/
@[stacks 01R6]
theorem schemeTheoreticImage_isClosedImmersion :
    IsClosedImmersion (Scheme.Hom.imageι f) := sorry

/-- Lemma 29.6.1 (2): the morphism `f : X \to Y` factors through the canonical closed subscheme
`Scheme.Hom.image f \subset Y`. -/
@[stacks 01R6]
theorem schemeTheoreticImage_factor :
    Scheme.Hom.toImage f ≫ Scheme.Hom.imageι f = f := sorry

/-- Lemma 29.6.1 (3): the canonical scheme-theoretic image of `f` is contained in every closed
subscheme of `Y` through which `f` factors. -/
@[stacks 01R6]
theorem schemeTheoreticImage_le_of_factor
    (i' : Z' ⟶ Y) [IsClosedImmersion i'] (g' : X ⟶ Z') (hg' : g' ≫ i' = f) :
    ∃ h : Scheme.Hom.image f ⟶ Z', IsClosedImmersion h ∧
      h ≫ i' = Scheme.Hom.imageι f := sorry

end

end AlgebraicGeometry
