import StacksProject_2024.stacks_project.Chap29.Definition_29_45_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-morphism owners
-- `IsIntegralHom` and `UniversallyInjective`; local Chapter 29 precedent supplies
-- `UniversalHomeomorphism` as the source-facing owner. The Stacks tag evidence is consistent:
-- item tag `04DF` agrees with the source URL ending in `/tag/04DF`.

section

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Lemma 29.45.5 (1): a universal homeomorphism of schemes is integral. -/
@[stacks 04DF]
theorem isIntegralHom_of_universalHomeomorphism
    (hf : UniversalHomeomorphism f) : IsIntegralHom f := sorry

/-- Lemma 29.45.5 (2): a universal homeomorphism of schemes is universally injective. -/
@[stacks 04DF]
theorem universallyInjective_of_universalHomeomorphism
    (hf : UniversalHomeomorphism f) : UniversallyInjective f := sorry

/-- Lemma 29.45.5 (3): a universal homeomorphism of schemes is surjective. -/
@[stacks 04DF]
theorem surjective_of_universalHomeomorphism
    (hf : UniversalHomeomorphism f) : Surjective f := sorry

/-- Lemma 29.45.5 (4): an integral, universally injective, and surjective morphism of schemes
is a universal homeomorphism. -/
@[stacks 04DF]
theorem universalHomeomorphism_of_isIntegralHom_universallyInjective_surjective
    (hfint : IsIntegralHom f) (hfinj : UniversallyInjective f) (hfsurj : Surjective f) :
    UniversalHomeomorphism f := sorry

end

end AlgebraicGeometry
