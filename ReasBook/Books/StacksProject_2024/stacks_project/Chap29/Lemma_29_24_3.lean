import StacksProject_2024.stacks_project.Chap29.Lemma_29_24_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MorphismProperty

namespace AlgebraicGeometry

-- The main source-facing owners for this section are the local classes `Submersive` and
-- `UniversallySubmersive` from `Definition_29_24_1`. The quotient-map bridge from the owner file
-- supplies the reusable canonical link to
-- `MorphismProperty.universally`.

universe u

section

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- Lemma 29.24.3 (1): the composition of submersive morphisms of schemes is submersive. -/
@[stacks 01KV]
theorem submersive_comp (hf : Submersive f) (hg : Submersive g) :
    Submersive (f ≫ g) := by
  exact (submersive_iff_base_isQuotientMap (f ≫ g)).mpr <|
    ((submersive_iff_base_isQuotientMap g).mp hg).comp ((submersive_iff_base_isQuotientMap f).mp hf)

/-- Lemma 29.24.3 (2): the composition of universally submersive morphisms of schemes is
universally submersive. -/
@[stacks 01KV]
theorem universallySubmersive_comp
    (hf : UniversallySubmersive f) (hg : UniversallySubmersive g) :
    UniversallySubmersive (f ≫ g) := by
  exact submersiveProperty.universally.comp_mem f g hf hg

instance instSubmersiveComp [Submersive f] [Submersive g] :
    Submersive (f ≫ g) :=
  submersive_comp f g inferInstance inferInstance

instance instUniversallySubmersiveComp [UniversallySubmersive f] [UniversallySubmersive g] :
    UniversallySubmersive (f ≫ g) :=
  universallySubmersive_comp f g inferInstance inferInstance

end

end AlgebraicGeometry
