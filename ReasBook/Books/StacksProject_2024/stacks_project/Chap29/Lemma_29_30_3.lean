import StacksProject_2024.stacks_project.Chap29.Definition_29_30_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}

/- Semantic recall / analogue check:
- `Definition_29_30_1.lean` fixes the source-facing syntomic owner as
  `Syntomic f := LocallyOfType RingHom.Syntomic f`;
- this file should therefore expose the source lemma `syntomic_comp` directly, with the
  morphism-property stability theorem and instance kept only as companions.
-/

/-- Lemma 29.30.3: the composition of two morphisms which are syntomic is syntomic. -/
@[stacks 01UH]
theorem syntomic_comp (hf : Syntomic f) (hg : Syntomic g) :
    Syntomic (f ≫ g) := by
  sorry

/-- The morphism property `Syntomic` is stable under composition. -/
theorem syntomic_isStableUnderComposition :
    CategoryTheory.MorphismProperty.IsStableUnderComposition @Syntomic :=
by
  refine CategoryTheory.MorphismProperty.IsStableUnderComposition.mk ?_
  intro X Y Z f g hf hg
  exact syntomic_comp hf hg

/-- Instance form of `syntomic_isStableUnderComposition`. -/
instance instSyntomicIsStableUnderComposition :
    CategoryTheory.MorphismProperty.IsStableUnderComposition @Syntomic :=
  syntomic_isStableUnderComposition

end AlgebraicGeometry
