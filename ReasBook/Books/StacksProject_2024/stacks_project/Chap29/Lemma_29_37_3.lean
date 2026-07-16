import StacksProject_2024.stacks_project.Chap29.Definition_29_37_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Semantic recall: `lean_leansearch` surfaced the canonical separatedness owner
`AlgebraicGeometry.IsSeparated`. Local Chapter 29 precedent represents an `f`-ample invertible
sheaf by the source-facing owner `RelativelyAmple f L`. -/

/-- Lemma 29.37.3: let `f : X ⟶ S` be a morphism of schemes. If there exists an `f`-ample
invertible sheaf, then `f` is separated. -/
@[stacks 01VI]
theorem isSeparated_of_exists_relativelyAmple
    {X S : Scheme.{u}} (f : X ⟶ S)
    (h : ∃ L : X.Modules, RelativelyAmple f L) :
    IsSeparated f := sorry

end AlgebraicGeometry
