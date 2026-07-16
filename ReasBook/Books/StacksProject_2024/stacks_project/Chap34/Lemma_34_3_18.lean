import StacksProject_2024.stacks_project.Chap34.Lemma_34_3_17

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced `GrothendieckTopology.overMapPullbackComp` and
-- `Over.pullbackComp`; local Chapter 34 precedent in the fppf/ph composition lemmas fixes the
-- source-facing owner as equality of the bundled morphisms of topoi under `MorphismOfTopoiIn.comp`.

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- Lemma 34.3.18 (1): for composable morphisms of schemes `f : X ⟶ Y` and `g : Y ⟶ Z`, the
associated big Zariski morphisms of topoi satisfy `g_big ∘ f_big = (g ∘ f)_big`. -/
@[stacks 0212]
theorem bigZariskiMorphismOfTopoi_comp :
    MorphismOfTopoiIn.comp (bigZariskiMorphismOfTopoi g) (bigZariskiMorphismOfTopoi f) =
      bigZariskiMorphismOfTopoi (f ≫ g) := sorry

/-- Lemma 34.3.18 (2): for composable morphisms of schemes `f : X ⟶ Y` and `g : Y ⟶ Z`, the
associated small Zariski morphisms of topoi satisfy `g_small ∘ f_small = (g ∘ f)_small`. -/
@[stacks 0212]
theorem smallZariskiMorphismOfTopoi_comp :
    MorphismOfTopoiIn.comp (smallZariskiMorphismOfTopoi g) (smallZariskiMorphismOfTopoi f) =
      smallZariskiMorphismOfTopoi (f ≫ g) := sorry

end AlgebraicGeometry.Scheme
