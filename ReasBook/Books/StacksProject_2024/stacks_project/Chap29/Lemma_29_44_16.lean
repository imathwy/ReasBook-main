import StacksProject_2024.stacks_project.Chap29.Definition_29_43_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u

namespace AlgebraicGeometry

section

variable {X S : Scheme.{u}} (f : X ⟶ S)

-- Semantic recall: `lean_leansearch` surfaced `AlgebraicGeometry.IsFinite` as the canonical
-- scheme-morphism finiteness owner. Local Chapter 29 provides `AlgebraicGeometry.Projective` in
-- `Definition_29_43_1`; the source tag evidence is consistent with Stacks tag `0B3I`.

/-- Lemma 29.44.16: a finite morphism of schemes is projective. -/
@[stacks 0B3I]
theorem IsFinite.projective [IsFinite f] :
    Projective f := sorry

end

end AlgebraicGeometry
