import StacksProject_2024.stacks_project.Chap29.Definition_29_45_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced nearby morphism-property infrastructure but no
-- canonical mathlib owner for universal homeomorphisms beyond the local source-facing
-- `UniversalHomeomorphism`. The Stacks tag evidence is consistent: item tag `0H2M` agrees with
-- the source URL ending in `/tag/0H2M`.

section

variable {X Y Z : Scheme.{u}} {g : X ⟶ Y} {h : Y ⟶ Z}

/-- Lemma 29.45.8 (1): if `g : X ⟶ Y` and `h : Y ⟶ Z` are universal
homeomorphisms, then their composition `g ≫ h : X ⟶ Z` is a universal homeomorphism. -/
@[stacks 0H2M]
theorem universalHomeomorphism_comp_of_left_right
    (hg : UniversalHomeomorphism g) (hh : UniversalHomeomorphism h) :
    UniversalHomeomorphism (g ≫ h) := sorry

/-- Lemma 29.45.8 (2): if the composition `g ≫ h : X ⟶ Z` and
`g : X ⟶ Y` are universal homeomorphisms, then `h : Y ⟶ Z` is a universal homeomorphism. -/
@[stacks 0H2M]
theorem universalHomeomorphism_right_of_comp_left
    (hcomp : UniversalHomeomorphism (g ≫ h)) (hg : UniversalHomeomorphism g) :
    UniversalHomeomorphism h := sorry

/-- Lemma 29.45.8 (3): if the composition `g ≫ h : X ⟶ Z` and
`h : Y ⟶ Z` are universal homeomorphisms, then `g : X ⟶ Y` is a universal homeomorphism. -/
@[stacks 0H2M]
theorem universalHomeomorphism_left_of_comp_right
    (hcomp : UniversalHomeomorphism (g ≫ h)) (hh : UniversalHomeomorphism h) :
    UniversalHomeomorphism g := sorry

end

end AlgebraicGeometry
