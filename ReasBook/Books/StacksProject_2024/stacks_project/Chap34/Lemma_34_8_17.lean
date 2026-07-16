import Mathlib
import StacksProject_2024.stacks_project.Chap34.Lemma_34_8_16

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped MorphismOfTopoiIn

noncomputable section

universe u w

namespace AlgebraicGeometry

section

-- Semantic recall / owner check:
-- `lean_leansearch` surfaced the canonical slice-site pullback-composition comparison
-- `GrothendieckTopology.overMapPullbackComp`, and local Chapter 7 precedent (`7_25_8_1`) fixes
-- `MorphismOfTopoiIn.comp` as the source-facing owner for composition of site-presented morphisms
-- of topoi. Lemma 34.8.16 already packages `f_big` as `bigPhMorphismOfTopoi Jph f`, so the
-- present item should state equality at that owner level.

variable (Jph : GrothendieckTopology Scheme.{u})
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
variable [HasPullbacksAlong f] [HasPullbacksAlong g] [HasPullbacksAlong (f ≫ g)]
variable [Functor.IsContinuous (Over.map f) (Jph.over X) (Jph.over Y)]
variable [Functor.IsContinuous (Over.map g) (Jph.over Y) (Jph.over Z)]
variable [Functor.IsContinuous (Over.map (f ≫ g)) (Jph.over X) (Jph.over Z)]
variable [HasWeakSheafify (Jph.over Y) (Type w)]
variable [HasWeakSheafify (Jph.over Z) (Type w)]
variable [∀ P : (Over X)ᵒᵖ ⥤ Type w, (Over.map f).op.HasLeftKanExtension P]
variable [∀ P : (Over Y)ᵒᵖ ⥤ Type w, (Over.map g).op.HasLeftKanExtension P]
variable [∀ P : (Over X)ᵒᵖ ⥤ Type w, (Over.map (f ≫ g)).op.HasLeftKanExtension P]
variable [HasSheafify (Jph.over X) (Type w)]
variable [HasSheafify (Jph.over Y) (Type w)]
variable [∀ P : (Over X)ᵒᵖ ⥤ Type w, (Over.map f).op.HasPointwiseRightKanExtension P]
variable [∀ P : (Over Y)ᵒᵖ ⥤ Type w, (Over.map g).op.HasPointwiseRightKanExtension P]
variable [∀ P : (Over X)ᵒᵖ ⥤ Type w, (Over.map (f ≫ g)).op.HasPointwiseRightKanExtension P]

/-- Lemma 34.8.17: for composable morphisms `f : X ⟶ Y` and `g : Y ⟶ Z`, the associated big ph
morphisms of topoi compose as expected:
`g_big ∘ f_big = (g ∘ f)_big`. In Lean's left-to-right composition notation on schemes, the
composite morphism is `f ≫ g`. -/
@[stacks 0DBS]
theorem bigPhMorphismOfTopoi_comp :
    MorphismOfTopoiIn.comp (bigPhMorphismOfTopoi Jph g) (bigPhMorphismOfTopoi Jph f) =
      bigPhMorphismOfTopoi Jph (f ≫ g) := sorry

end

end AlgebraicGeometry
