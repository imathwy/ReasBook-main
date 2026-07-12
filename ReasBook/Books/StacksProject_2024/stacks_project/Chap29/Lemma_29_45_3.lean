import StacksProject_2024.Chap29.Definition_29_45_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced generic composition-stability infrastructure for
-- scheme morphism properties, and local Chapter 29 precedent provides the source-facing owner
-- `UniversalHomeomorphism` in `Definition_29_45_1`. The source item is therefore formalized as
-- the direct composition theorem for that established owner.

section

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- Lemma 29.45.3: the composition of a pair of universal homeomorphisms of schemes is a
universal homeomorphism. -/
@[stacks 0CEV, instance]
theorem universalHomeomorphism_comp
    [UniversalHomeomorphism f] [UniversalHomeomorphism g] :
    UniversalHomeomorphism (f ≫ g) := by
  rw [universalHomeomorphism_iff]
  let hf : universally topologicallyIsHomeomorph f :=
    UniversalHomeomorphism.universally_isHomeomorph
  let hg : universally topologicallyIsHomeomorph g :=
    UniversalHomeomorphism.universally_isHomeomorph
  exact topologicallyIsHomeomorph.universally.comp_mem f g hf hg

end

end AlgebraicGeometry
